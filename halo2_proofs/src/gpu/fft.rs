use crate::arithmetic::Group;
use crate::gpu::{
    error::{GPUError, GPUResult},
    get_lock_name_and_gpu_range, locks, sources,
};
use crate::worker::THREAD_POOL;
use group::ff::Field;
use log::{error, info};
use rayon::join;
use rust_gpu_tools::*;
use std::cmp::min;
use std::ops::MulAssign;
use std::{cmp, env};

const LOG2_MAX_ELEMENTS: usize = 32; // At most 2^32 elements is supported.
const MAX_LOG2_RADIX: u32 = 9; // Radix512
const MAX_LOG2_LOCAL_WORK_SIZE: u32 = 8; // 256

/// SingleFFTKernel
#[allow(missing_debug_implementations)]
pub struct SingleFFTKernel<G>
where
    G: Group,
{
    program: opencl::Program,
    pq_buffer: opencl::Buffer<G::Scalar>,
    omegas_buffer: opencl::Buffer<G::Scalar>,
    #[allow(dead_code)]
    priority: bool,
}

impl<G> SingleFFTKernel<G>
where
    G: Group,
{
    /// New gpu fft kernel device
    pub fn create(device: opencl::Device, priority: bool) -> GPUResult<SingleFFTKernel<G>> {
        let src = sources::kernel::<G>(device.brand() == opencl::Brand::Nvidia);

        let program = opencl::Program::from_opencl(device, &src)?;
        let pq_buffer = program.create_buffer::<G::Scalar>(1 << MAX_LOG2_RADIX >> 1)?;
        let omegas_buffer = program.create_buffer::<G::Scalar>(LOG2_MAX_ELEMENTS)?;

        info!("FFT: Device: {}", program.device().name());

        Ok(SingleFFTKernel {
            program,
            pq_buffer,
            omegas_buffer,
            priority,
        })
    }

    /// Peforms a FFT round
    /// * `log_n` - Specifies log2 of number of elements
    /// * `log_p` - Specifies log2 of `p`, (http://www.bealto.com/gpu-fft_group-1.html)
    /// * `deg` - 1=>radix2, 2=>radix4, 3=>radix8, ...
    /// * `max_deg` - The precalculated values pq` and `omegas` are valid for radix degrees up to `max_deg`
    fn radix_fft_round(
        &mut self,
        src_buffer: &opencl::Buffer<G::Scalar>,
        dst_buffer: &opencl::Buffer<G::Scalar>,
        log_n: u32,
        log_p: u32,
        deg: u32,
        max_deg: u32,
    ) -> GPUResult<()> {
        // if locks::PriorityLock::should_break(self.priority) {
        //     return Err(GPUError::GPUTaken);
        // }

        let n = 1u32 << log_n;
        let local_work_size = 1 << cmp::min(deg - 1, MAX_LOG2_LOCAL_WORK_SIZE);
        let global_work_size = (n >> deg) * local_work_size;
        let kernel = self.program.create_kernel(
            "radix_fft",
            global_work_size as usize,
            Some(local_work_size as usize),
        );
        kernel
            .arg(src_buffer)
            .arg(dst_buffer)
            .arg(&self.pq_buffer)
            .arg(&self.omegas_buffer)
            .arg(opencl::LocalBuffer::<G::Scalar>::new(1 << deg))
            .arg(n)
            .arg(log_p)
            .arg(deg)
            .arg(max_deg)
            .run()?;
        Ok(())
    }

    /// Share some precalculated values between threads to boost the performance
    fn setup_pq_omegas(&mut self, omega: &G::Scalar, n: usize, max_deg: u32) -> GPUResult<()> {
        // Precalculate:
        // [omega^(0/(2^(deg-1))), omega^(1/(2^(deg-1))), ..., omega^((2^(deg-1)-1)/(2^(deg-1)))]
        let mut pq = vec![G::Scalar::zero(); 1 << max_deg >> 1];
        let twiddle = omega.pow_vartime([(n >> max_deg) as u64]);
        pq[0] = G::Scalar::one();
        if max_deg > 1 {
            pq[1] = twiddle;
            for i in 2..(1 << max_deg >> 1) {
                pq[i] = pq[i - 1];
                pq[i].mul_assign(&twiddle);
            }
        }
        self.pq_buffer.write_from(0, &pq)?;

        // Precalculate [omega, omega^2, omega^4, omega^8, ..., omega^(2^31)]
        let mut omegas = vec![G::Scalar::zero(); 32];
        omegas[0] = *omega;
        for i in 1..LOG2_MAX_ELEMENTS {
            omegas[i] = omegas[i - 1].pow_vartime([2u64]);
        }
        self.omegas_buffer.write_from(0, &omegas)?;

        Ok(())
    }

    /// Performs FFT on `a`
    /// * `omega` - Special value `omega` is used for FFT over finite-fields
    /// * `log_n` - Specifies log2 of number of elements
    pub fn radix_fft(
        &mut self,
        a: &mut [G::Scalar],
        omega: &G::Scalar,
        log_n: u32,
    ) -> GPUResult<()> {
        let n = 1 << log_n;
        let mut src_buffer = self.program.create_buffer::<G::Scalar>(n)?;
        let mut dst_buffer = self.program.create_buffer::<G::Scalar>(n)?;

        let max_deg = cmp::min(MAX_LOG2_RADIX, log_n);
        self.setup_pq_omegas(omega, n, max_deg)?;

        src_buffer.write_from(0, &*a)?;
        let mut log_p = 0u32;
        while log_p < log_n {
            let deg = cmp::min(max_deg, log_n - log_p);
            self.radix_fft_round(&src_buffer, &dst_buffer, log_n, log_p, deg, max_deg)?;
            log_p += deg;
            std::mem::swap(&mut src_buffer, &mut dst_buffer);
        }

        src_buffer.read_into(0, a)?;

        Ok(())
    }
}

/// Gpu fft kernel vec
#[allow(missing_debug_implementations)]
pub struct MultiFFTKernel<G>
where
    G: Group,
{
    kernels: Vec<SingleFFTKernel<G>>,
    _lock: locks::GPULock,
}

impl<G> MultiFFTKernel<G>
where
    G: Group,
{
    /// New gpu kernel device
    pub fn create(priority: bool) -> GPUResult<MultiFFTKernel<G>> {
        let mut all_devices = opencl::Device::all();
        let all_num = all_devices.len();
        let (lock_index, gpu_range) = get_lock_name_and_gpu_range(all_num);

        let lock = locks::GPULock::lock(lock_index);

        let devices: Vec<&opencl::Device> = all_devices.drain(gpu_range).collect();

        // use all of the  GPUs
        let kernels: Vec<_> = devices
            .into_iter()
            .map(|d| (d, SingleFFTKernel::<G>::create(d.clone(), priority)))
            .filter_map(|(device, res)| {
                if let Err(ref e) = res {
                    error!(
                        "Cannot initialize kernel for device '{}'! Error: {}",
                        device.name(),
                        e
                    );
                }
                res.ok()
            })
            .collect();

        Ok(MultiFFTKernel {
            kernels,
            _lock: lock,
        })
    }

    /// fft_multiple call for kernel radix_fft
    pub fn fft_multiple(
        &mut self,
        polys: &mut [&mut [G::Scalar]],
        omega: &G::Scalar,
        log_n: u32,
    ) -> GPUResult<()> {
        use rayon::prelude::*;

        for poly in polys.chunks_mut(self.kernels.len()) {
            crate::worker::THREAD_POOL.install(|| {
                poly.par_iter_mut()
                    .zip(self.kernels.par_iter_mut())
                    .for_each(|(p, kern)| kern.radix_fft(p, omega, log_n).unwrap())
            });
        }

        Ok(())
    }
}
