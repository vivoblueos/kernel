//! This module offers a convenient way to enable only a subset of logging levels
//! for just this `fatfs` crate only without changing the logging levels
//! of other crates in a given project.

use log::LevelFilter;

#[cfg(feature = "log_level_trace")]
pub const MAX_LOG_LEVEL: LevelFilter = LevelFilter::Trace;

#[cfg(all(not(feature = "log_level_trace"), feature = "log_level_debug",))]
pub const MAX_LOG_LEVEL: LevelFilter = LevelFilter::Debug;

#[cfg(all(
    not(feature = "log_level_trace"),
    not(feature = "log_level_debug"),
    feature = "log_level_info",
))]
pub const MAX_LOG_LEVEL: LevelFilter = LevelFilter::Info;

#[cfg(all(
    not(feature = "log_level_trace"),
    not(feature = "log_level_debug"),
    not(feature = "log_level_info"),
    feature = "log_level_warn",
))]
pub const MAX_LOG_LEVEL: LevelFilter = LevelFilter::Warn;

#[cfg(all(
    not(feature = "log_level_trace"),
    not(feature = "log_level_debug"),
    not(feature = "log_level_info"),
    not(feature = "log_level_warn"),
    feature = "log_level_error",
))]
pub const MAX_LOG_LEVEL: LevelFilter = LevelFilter::Error;

#[cfg(all(
    not(feature = "log_level_trace"),
    not(feature = "log_level_debug"),
    not(feature = "log_level_info"),
    not(feature = "log_level_warn"),
    not(feature = "log_level_error"),
))]
pub const MAX_LOG_LEVEL: LevelFilter = LevelFilter::Off;

#[macro_export]
macro_rules! log {
    (target: $target:expr, $lvl:expr, $($arg:tt)+) => ({
        let lvl = $lvl;
        if lvl <= $crate::log_macros::MAX_LOG_LEVEL {
            log::log!(target: $target, lvl, $($arg)+);
        }
    });
    ($lvl:expr, $($arg:tt)+) => ({
        let lvl = $lvl;
        if lvl <= $crate::log_macros::MAX_LOG_LEVEL {
            log::log!(lvl, $($arg)+);
        }
    })
}

#[macro_export]
macro_rules! error {
    (target: $target:expr, $($arg:tt)+) => (
        log!(target: $target, log::Level::Error, $($arg)+);
    );
    ($($arg:tt)+) => (
        log!(log::Level::Error, $($arg)+);
    )
}

#[macro_export]
macro_rules! warn {
    (target: $target:expr, $($arg:tt)+) => (
        log!(target: $target, log::Level::Warn, $($arg)+);
    );
    ($($arg:tt)+) => (
        log!(log::Level::Warn, $($arg)+);
    )
}

#[macro_export]
macro_rules! info {
    (target: $target:expr, $($arg:tt)+) => (
        log!(target: $target, log::Level::Info, $($arg)+);
    );
    ($($arg:tt)+) => (
        log!(log::Level::Info, $($arg)+);
    )
}

#[macro_export]
macro_rules! debug {
    (target: $target:expr, $($arg:tt)+) => (
        log!(target: $target, log::Level::Debug, $($arg)+);
    );
    ($($arg:tt)+) => (
        log!(log::Level::Debug, $($arg)+);
    )
}

#[macro_export]
macro_rules! trace {
    (target: $target:expr, $($arg:tt)+) => (
        log!(target: $target, log::Level::Trace, $($arg)+);
    );
    ($($arg:tt)+) => (
        log!(log::Level::Trace, $($arg)+);
    )
}
