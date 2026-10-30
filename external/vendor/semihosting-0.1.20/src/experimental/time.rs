// SPDX-License-Identifier: Apache-2.0 OR MIT

// TODO: re-export Duration?

use core::{fmt, ops, time::Duration};

use self::sys as time;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SystemTime(time::SystemTime);

#[derive(Clone, Debug)]
pub struct SystemTimeError(Duration);

impl SystemTime {
    pub const UNIX_EPOCH: Self = Self(time::UNIX_EPOCH);

    // TODO: return result?
    /// # Platform-specific behavior
    ///
    /// Currently, this function is not supported on MIPS32/MIPS64.
    #[must_use]
    pub fn now() -> Self {
        Self(time::SystemTime::now().unwrap())
    }

    pub fn duration_since(&self, earlier: SystemTime) -> Result<Duration, SystemTimeError> {
        self.0.sub_time(&earlier.0).map_err(SystemTimeError)
    }

    pub fn elapsed(&self) -> Result<Duration, SystemTimeError> {
        SystemTime::now().duration_since(*self)
    }

    pub fn checked_add(&self, duration: Duration) -> Option<SystemTime> {
        self.0.checked_add_duration(&duration).map(SystemTime)
    }

    pub fn checked_sub(&self, duration: Duration) -> Option<SystemTime> {
        self.0.checked_sub_duration(&duration).map(SystemTime)
    }
}

impl ops::Add<Duration> for SystemTime {
    type Output = SystemTime;

    fn add(self, dur: Duration) -> Self::Output {
        self.checked_add(dur).expect("overflow when adding duration to instant")
    }
}

impl ops::AddAssign<Duration> for SystemTime {
    fn add_assign(&mut self, other: Duration) {
        *self = *self + other;
    }
}

impl ops::Sub<Duration> for SystemTime {
    type Output = SystemTime;

    fn sub(self, dur: Duration) -> Self::Output {
        self.checked_sub(dur).expect("overflow when subtracting duration from instant")
    }
}

impl ops::SubAssign<Duration> for SystemTime {
    fn sub_assign(&mut self, other: Duration) {
        *self = *self - other;
    }
}

impl fmt::Debug for SystemTime {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl SystemTimeError {
    #[must_use]
    pub fn duration(&self) -> Duration {
        self.0
    }
}

impl fmt::Display for SystemTimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("second time provided was later than self")
    }
}

// Based on https://github.com/rust-lang/rust/blob/1.84.0/library/std/src/sys/pal/unix/time.rs.
mod sys {
    #![allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap, clippy::cast_sign_loss)]

    use core::{fmt, time::Duration};

    const NSEC_PER_SEC: u64 = 1_000_000_000;
    pub(crate) const UNIX_EPOCH: SystemTime = SystemTime { t: Timespec::zero() };

    #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    #[repr(transparent)]
    struct Nanoseconds(u32);

    #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub(crate) struct SystemTime {
        t: Timespec,
    }

    #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    struct Timespec {
        tv_sec: i64,
        tv_nsec: Nanoseconds,
    }

    impl SystemTime {
        pub(crate) fn sub_time(&self, other: &SystemTime) -> Result<Duration, Duration> {
            self.t.sub_timespec(&other.t)
        }

        pub(crate) fn checked_add_duration(&self, other: &Duration) -> Option<SystemTime> {
            Some(SystemTime { t: self.t.checked_add_duration(other)? })
        }

        pub(crate) fn checked_sub_duration(&self, other: &Duration) -> Option<SystemTime> {
            Some(SystemTime { t: self.t.checked_sub_duration(other)? })
        }
    }

    impl fmt::Debug for SystemTime {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("SystemTime")
                .field("tv_sec", &self.t.tv_sec)
                .field("tv_nsec", &self.t.tv_nsec.0)
                .finish()
        }
    }

    impl Timespec {
        const fn new_unchecked(tv_sec: i64, tv_nsec: i64) -> Timespec {
            Timespec { tv_sec, tv_nsec: Nanoseconds(tv_nsec as u32) }
        }

        const fn zero() -> Timespec {
            Self::new_unchecked(0, 0)
        }

        fn sub_timespec(&self, other: &Timespec) -> Result<Duration, Duration> {
            if self >= other {
                let (secs, nsec) = if self.tv_nsec.0 >= other.tv_nsec.0 {
                    ((self.tv_sec - other.tv_sec) as u64, self.tv_nsec.0 - other.tv_nsec.0)
                } else {
                    (
                        (self.tv_sec - other.tv_sec - 1) as u64,
                        self.tv_nsec.0 + (NSEC_PER_SEC as u32) - other.tv_nsec.0,
                    )
                };

                Ok(Duration::new(secs, nsec))
            } else {
                match other.sub_timespec(self) {
                    Ok(d) => Err(d),
                    Err(d) => Ok(d),
                }
            }
        }

        pub(crate) fn checked_add_duration(&self, other: &Duration) -> Option<Timespec> {
            // i*::checked_add_unsigned requires Rust 1.66
            #[inline]
            fn checked_add_unsigned(this: i64, rhs: u64) -> Option<i64> {
                let (a, b) = {
                    let rhs = rhs as i64;
                    let (res, overflowed) = this.overflowing_add(rhs);
                    (res, overflowed ^ (rhs < 0))
                };
                if b { None } else { Some(a) }
            }

            let mut secs = checked_add_unsigned(self.tv_sec, other.as_secs())?;

            // Nano calculations can't overflow because nanos are <1B which fit
            // in a u32.
            let mut nsec = other.subsec_nanos() + self.tv_nsec.0;
            if nsec >= NSEC_PER_SEC as u32 {
                nsec -= NSEC_PER_SEC as u32;
                secs = secs.checked_add(1)?;
            }
            Some(Timespec::new_unchecked(secs, nsec.into()))
        }

        pub(crate) fn checked_sub_duration(&self, other: &Duration) -> Option<Timespec> {
            // i*::checked_sub_unsigned requires Rust 1.66
            #[inline]
            fn checked_sub_unsigned(this: i64, rhs: u64) -> Option<i64> {
                let (a, b) = {
                    let rhs = rhs as i64;
                    let (res, overflowed) = this.overflowing_sub(rhs);
                    (res, overflowed ^ (rhs < 0))
                };
                if b { None } else { Some(a) }
            }

            let mut secs = checked_sub_unsigned(self.tv_sec, other.as_secs())?;

            // Similar to above, nanos can't overflow.
            let mut nsec = self.tv_nsec.0 as i32 - other.subsec_nanos() as i32;
            if nsec < 0 {
                nsec += NSEC_PER_SEC as i32;
                secs = secs.checked_sub(1)?;
            }
            Some(Timespec::new_unchecked(secs, nsec.into()))
        }
    }

    #[cfg(any(
        target_arch = "aarch64",
        target_arch = "arm",
        target_arch = "riscv32",
        target_arch = "riscv64",
        all(target_arch = "xtensa", feature = "openocd-semihosting"),
    ))]
    mod inner {
        use super::{Nanoseconds, SystemTime, Timespec};
        use crate::{io, sys::arm_compat::sys_time};

        impl SystemTime {
            pub(crate) fn now() -> io::Result<Self> {
                // SYS_TIME doesn't have Y2038 problem (although it still has Y2106 problem): https://github.com/ARM-software/abi-aa/commit/d281283bf3dcec4d4ebf9e5646020d77904904e1
                Ok(Self {
                    t: Timespec { tv_sec: sys_time()? as u64 as i64, tv_nsec: Nanoseconds(0) },
                })
            }
        }
    }
    #[cfg(any(
        target_arch = "mips",
        target_arch = "mips32r6",
        target_arch = "mips64",
        target_arch = "mips64r6",
    ))]
    mod inner {
        use super::SystemTime;
        use crate::io;

        impl SystemTime {
            pub(crate) fn now() -> io::Result<Self> {
                Err(io::ErrorKind::Unsupported.into())
            }
        }
    }
}
