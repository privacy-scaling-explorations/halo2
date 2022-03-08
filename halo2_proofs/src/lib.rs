//! # halo2_proofs

#![cfg_attr(docsrs, feature(doc_cfg))]
// Build without warnings on stable 1.51 and later.
#![allow(unknown_lints)]
// Disable old lint warnings until our MSRV is at least 1.51.
#![allow(renamed_and_removed_lints)]
// Use the old lint name to build without warnings until our MSRV is at least 1.51.
#![allow(clippy::unknown_clippy_lints)]
// The actual lints we want to disable.
#![allow(
    clippy::op_ref,
    clippy::assign_op_pattern,
    clippy::too_many_arguments,
    clippy::suspicious_arithmetic_impl,
    clippy::many_single_char_names,
    clippy::same_item_push,
    clippy::upper_case_acronyms
)]
#![deny(broken_intra_doc_links)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]
#![deny(unsafe_code)]
// Remove this once we update pasta_curves
#![allow(unused_imports)]

pub mod arithmetic;
pub mod arithmetic_msm;
pub mod circuit;
use std::{
    env::var,
    sync::atomic::{AtomicUsize, Ordering},
    time::Instant,
};

pub use pairing;
mod multicore;
pub mod plonk;
pub mod poly;
pub mod transcript;

pub mod dev;
mod helpers;

/// Temp
#[allow(missing_debug_implementations)]
pub struct MeasurementInfo {
    /// Show measurement
    pub show: bool,
    /// The start time
    pub time: Instant,
    /// What is being measured
    pub message: String,
    /// The indent
    pub indent: usize,
}

/// Global indent counter
pub static NUM_INDENT: AtomicUsize = AtomicUsize::new(0);

/// Gets the time difference between the current time and the passed in time
pub fn get_duration(start: Instant) -> usize {
    let final_time = Instant::now() - start;
    let secs = final_time.as_secs() as usize;
    let millis = final_time.subsec_millis() as usize;
    let micros = (final_time.subsec_micros() % 1000) as usize;
    secs * 1000000 + millis * 1000 + micros
}

/// Prints a measurement on screen
pub fn log_measurement(indent: Option<usize>, msg: String, duration: usize) {
    let indent = indent.unwrap_or(0);
    println!(
        "{}{} ........ {}s",
        "*".repeat(indent),
        msg,
        (duration as f32) / 1000000.0
    );
}

/// Starts a measurement
pub fn start_measure(msg: String, always: bool) -> MeasurementInfo {
    let measure = env_value("MEASURE", 0);
    let indent = NUM_INDENT.fetch_add(1, Ordering::Relaxed);
    MeasurementInfo {
        show: always || measure == 1,
        time: Instant::now(),
        message: msg,
        indent,
    }
}

/// Stops a measurement, returns the duration
pub fn stop_measure(info: MeasurementInfo) -> usize {
    NUM_INDENT.fetch_sub(1, Ordering::Relaxed);
    let duration = get_duration(info.time);
    if info.show {
        log_measurement(Some(info.indent), info.message, duration);
    }
    duration
}

/// Gets the ENV variable if defined, otherwise returns the default value
pub fn env_value(key: &str, default: usize) -> usize {
    match var(key) {
        Ok(val) => val.parse().unwrap(),
        Err(_) => default,
    }
}
