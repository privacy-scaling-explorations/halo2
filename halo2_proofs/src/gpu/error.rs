use rust_gpu_tools::opencl;

/// Gpu err
#[derive(thiserror::Error, Debug)]
pub enum GPUError {
    /// Simple
    #[error("GPUError: {0}")]
    Simple(&'static str),

    /// OpenCL
    #[error("OpenCL Error: {0}")]
    OpenCL(#[from] opencl::GPUError),

    /// GPUTaken
    #[error("GPU taken by a high priority process!")]
    GPUTaken,

    /// KernelUninitialized
    #[error("No kernel is initialized!")]
    KernelUninitialized,

    /// GPUDisabled
    #[error("GPU accelerator is disabled!")]
    GPUDisabled,
}

/// Type GPUResult
pub type GPUResult<T> = std::result::Result<T, GPUError>;

impl From<std::boxed::Box<dyn std::any::Any + std::marker::Send>> for GPUError {
    fn from(e: std::boxed::Box<dyn std::any::Any + std::marker::Send>) -> Self {
        match e.downcast::<Self>() {
            Ok(err) => *err,
            Err(_) => GPUError::Simple("An unknown GPU error happened!"),
        }
    }
}
