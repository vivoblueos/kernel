//! Type aliases for common uses

use crate::Duration;
use crate::Instant;
use crate::Rate;

/// Alias for nanosecond duration
pub type NanosDuration<T> = Duration<T, 1, 1_000_000_000>;

/// Alias for nanosecond duration (`u32` backing storage)
pub type NanosDurationU32 = Duration<u32, 1, 1_000_000_000>;

/// Alias for nanosecond duration (`u64` backing storage)
pub type NanosDurationU64 = Duration<u64, 1, 1_000_000_000>;

/// Alias for microsecond duration
pub type MicrosDuration<T> = Duration<T, 1, 1_000_000>;

/// Alias for microsecond duration (`u32` backing storage)
pub type MicrosDurationU32 = Duration<u32, 1, 1_000_000>;

/// Alias for microsecond duration (`u64` backing storage)
pub type MicrosDurationU64 = Duration<u64, 1, 1_000_000>;

/// Alias for millisecond duration
pub type MillisDuration<T> = Duration<T, 1, 1_000>;

/// Alias for millisecond duration (`u32` backing storage)
pub type MillisDurationU32 = Duration<u32, 1, 1_000>;

/// Alias for millisecond duration (`u64` backing storage)
pub type MillisDurationU64 = Duration<u64, 1, 1_000>;

/// Alias for second duration
pub type SecsDuration<T> = Duration<T, 1, 1>;

/// Alias for second duration (`u32` backing storage)
pub type SecsDurationU32 = Duration<u32, 1, 1>;

/// Alias for second duration (`u64` backing storage)
pub type SecsDurationU64 = Duration<u64, 1, 1>;

/// Alias for minutes duration
pub type MinutesDuration<T> = Duration<T, 60, 1>;

/// Alias for minutes duration (`u32` backing storage)
pub type MinutesDurationU32 = Duration<u32, 60, 1>;

/// Alias for minutes duration (`u64` backing storage)
pub type MinutesDurationU64 = Duration<u64, 60, 1>;

/// Alias for hours duration
pub type HoursDuration<T> = Duration<T, 3_600, 1>;

/// Alias for hours duration (`u32` backing storage)
pub type HoursDurationU32 = Duration<u32, 3_600, 1>;

/// Alias for hours duration (`u64` backing storage)
pub type HoursDurationU64 = Duration<u64, 3_600, 1>;

/// Alias for durations that come from timers with a specific frequency
pub type TimerDuration<T, const FREQ_HZ: u32> = Duration<T, 1, FREQ_HZ>;

/// Alias for durations that come from timers with a specific frequency (`u32` backing storage)
pub type TimerDurationU32<const FREQ_HZ: u32> = Duration<u32, 1, FREQ_HZ>;

/// Alias for durations that come from timers with a specific frequency (`u64` backing storage)
pub type TimerDurationU64<const FREQ_HZ: u32> = Duration<u64, 1, FREQ_HZ>;

// -------------------------------

/// Alias for instants that come from timers with a specific frequency
pub type TimerInstant<T, const FREQ_HZ: u32> = Instant<T, 1, FREQ_HZ>;

/// Alias for instants that come from timers with a specific frequency (`u32` backing storage)
pub type TimerInstantU32<const FREQ_HZ: u32> = Instant<u32, 1, FREQ_HZ>;

/// Alias for instants that come from timers with a specific frequency (`u64` backing storage)
pub type TimerInstantU64<const FREQ_HZ: u32> = Instant<u64, 1, FREQ_HZ>;

// -------------------------------

/// Alias for hertz rate
pub type Hertz<T> = Rate<T, 1, 1>;

/// Alias for hertz rate (`u32` backing storage)
pub type HertzU32 = Rate<u32, 1, 1>;

/// Alias for hertz rate (`u64` backing storage)
pub type HertzU64 = Rate<u64, 1, 1>;

/// Alias for kilohertz rate
pub type Kilohertz<T> = Rate<T, 1_000, 1>;

/// Alias for kilohertz rate (`u32` backing storage)
pub type KilohertzU32 = Rate<u32, 1_000, 1>;

/// Alias for kilohertz rate (`u64` backing storage)
pub type KilohertzU64 = Rate<u64, 1_000, 1>;

/// Alias for megahertz rate
pub type Megahertz<T> = Rate<T, 1_000_000, 1>;

/// Alias for megahertz rate (`u32` backing storage)
pub type MegahertzU32 = Rate<u32, 1_000_000, 1>;

/// Alias for megahertz rate (`u64` backing storage)
pub type MegahertzU64 = Rate<u64, 1_000_000, 1>;

/// Alias for rate that come from timers with a specific frequency
pub type TimerRate<T, const FREQ_HZ: u32> = Rate<T, FREQ_HZ, 1>;

/// Alias for rate that come from timers with a specific frequency (`u32` backing storage)
pub type TimerRateU32<const FREQ_HZ: u32> = Rate<u32, FREQ_HZ, 1>;

/// Alias for rate that come from timers with a specific frequency (`u64` backing storage)
pub type TimerRateU64<const FREQ_HZ: u32> = Rate<u64, FREQ_HZ, 1>;
