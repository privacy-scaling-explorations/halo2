use rust_gpu_tools::opencl;

#[derive(thiserror::Error, Debug)]
pub enum GPUError {
    #[error("GPUError: {0}")]
    Simple(&'static str),

    #[error("OpenCL Error: {0}")]
    OpenCL(#[from] opencl::GPUError),

    #[error("GPU taken by a high priority process!")]
    GPUTaken,

    #[error("No kernel is initialized!")]
    KernelUninitialized,

    #[error("GPU accelerator is disabled!")]
    GPUDisabled,
}

pub type GPUResult<T> = std::result::Result<T, GPUError>;

impl From<std::boxed::Box<dyn std::any::Any + std::marker::Send>> for GPUError {
    fn from(e: std::boxed::Box<dyn std::any::Any + std::marker::Send>) -> Self {
        match e.downcast::<Self>() {
            Ok(err) => *err,
            Err(_) => GPUError::Simple("An unknown GPU error happened!"),
        }
    }
}
