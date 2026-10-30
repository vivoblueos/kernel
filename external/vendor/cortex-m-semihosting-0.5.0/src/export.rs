//! IMPLEMENTATION DETAILS USED BY MACROS

use core::fmt::{self, Write};

use cortex_m::interrupt;

use crate::hio::{self, HostStream};

static mut HSTDOUT: Option<HostStream> = None;

pub fn hstdout_str(s: &str) {
    let _result = interrupt::free(|_| unsafe {
        if HSTDOUT.is_none() {
            HSTDOUT = Some(hio::hstdout()?);
        }

        HSTDOUT.as_mut().unwrap().write_str(s).map_err(drop)
    });
}

pub fn hstdout_fmt(args: fmt::Arguments) {
    let _result = interrupt::free(|_| unsafe {
        if HSTDOUT.is_none() {
            HSTDOUT = Some(hio::hstdout()?);
        }

        HSTDOUT.as_mut().unwrap().write_fmt(args).map_err(drop)
    });
}

static mut HSTDERR: Option<HostStream> = None;

pub fn hstderr_str(s: &str) {
    let _result = interrupt::free(|_| unsafe {
        if HSTDERR.is_none() {
            HSTDERR = Some(hio::hstderr()?);
        }

        HSTDERR.as_mut().unwrap().write_str(s).map_err(drop)
    });
}

pub fn hstderr_fmt(args: fmt::Arguments) {
    let _result = interrupt::free(|_| unsafe {
        if HSTDERR.is_none() {
            HSTDERR = Some(hio::hstderr()?);
        }

        HSTDERR.as_mut().unwrap().write_fmt(args).map_err(drop)
    });
}
