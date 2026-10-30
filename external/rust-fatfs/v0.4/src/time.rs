#[cfg(feature = "chrono")]
use core::convert::TryFrom;
use core::fmt::Debug;

#[cfg(feature = "chrono")]
use chrono::{self, Datelike, Timelike};

const MIN_YEAR: u16 = 1980;
const MAX_YEAR: u16 = 2107;
const MIN_MONTH: u16 = 1;
const MAX_MONTH: u16 = 12;
const MIN_DAY: u16 = 1;
const MAX_DAY: u16 = 31;

/// A DOS compatible date.
///
/// Used by `DirEntry` time-related methods.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
#[non_exhaustive]
pub struct Date {
    /// Full year - [1980, 2107]
    pub year: u16,
    /// Month of the year - [1, 12]
    pub month: u16,
    /// Day of the month - [1, 31]
    pub day: u16,
}

impl Date {
    /// Creates a new `Date` instance.
    ///
    /// * `year` - full year number in the range [1980, 2107]
    /// * `month` - month of the year in the range [1, 12]
    /// * `day` - a day of the month in the range [1, 31]
    ///
    /// # Panics
    ///
    /// Panics if one of provided arguments is out of the supported range.
    #[must_use]
    pub fn new(year: u16, month: u16, day: u16) -> Self {
        assert!((MIN_YEAR..=MAX_YEAR).contains(&year), "year out of range");
        assert!((MIN_MONTH..=MAX_MONTH).contains(&month), "month out of range");
        assert!((MIN_DAY..=MAX_DAY).contains(&day), "day out of range");
        Self { year, month, day }
    }

    pub(crate) fn decode(dos_date: u16) -> Self {
        let (year, month, day) = ((dos_date >> 9) + MIN_YEAR, (dos_date >> 5) & 0xF, dos_date & 0x1F);
        Self { year, month, day }
    }

    pub(crate) fn encode(self) -> u16 {
        ((self.year - MIN_YEAR) << 9) | (self.month << 5) | self.day
    }
}

/// A DOS compatible time.
///
/// Used by `DirEntry` time-related methods.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
#[non_exhaustive]
pub struct Time {
    /// Hours after midnight - [0, 23]
    pub hour: u16,
    /// Minutes after the hour - [0, 59]
    pub min: u16,
    /// Seconds after the minute - [0, 59]
    pub sec: u16,
    /// Milliseconds after the second - [0, 999]
    pub millis: u16,
}

impl Time {
    /// Creates a new `Time` instance.
    ///
    /// * `hour` - number of hours after midnight in the range [0, 23]
    /// * `min` - number of minutes after the hour in the range [0, 59]
    /// * `sec` - number of seconds after the minute in the range [0, 59]
    /// * `millis` - number of milliseconds after the second in the range [0, 999]
    ///
    /// # Panics
    ///
    /// Panics if one of provided arguments is out of the supported range.
    #[must_use]
    pub fn new(hour: u16, min: u16, sec: u16, millis: u16) -> Self {
        assert!(hour <= 23, "hour out of range");
        assert!(min <= 59, "min out of range");
        assert!(sec <= 59, "sec out of range");
        assert!(millis <= 999, "millis out of range");
        Self { hour, min, sec, millis }
    }

    pub(crate) fn decode(dos_time: u16, dos_time_hi_res: u8) -> Self {
        let hour = dos_time >> 11;
        let min = (dos_time >> 5) & 0x3F;
        let sec = (dos_time & 0x1F) * 2 + u16::from(dos_time_hi_res / 100);
        let millis = u16::from(dos_time_hi_res % 100) * 10;
        Self { hour, min, sec, millis }
    }

    pub(crate) fn encode(self) -> (u16, u8) {
        let dos_time = (self.hour << 11) | (self.min << 5) | (self.sec / 2);
        let dos_time_hi_res = (self.millis / 10) + (self.sec % 2) * 100;
        // safe cast: value in range [0, 199]
        #[allow(clippy::cast_possible_truncation)]
        (dos_time, dos_time_hi_res as u8)
    }
}

/// A DOS compatible date and time.
///
/// Used by `DirEntry` time-related methods.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
#[non_exhaustive]
pub struct DateTime {
    /// A date part
    pub date: Date,
    // A time part
    pub time: Time,
}

impl DateTime {
    #[must_use]
    pub fn new(date: Date, time: Time) -> Self {
        Self { date, time }
    }

    pub(crate) fn decode(dos_date: u16, dos_time: u16, dos_time_hi_res: u8) -> Self {
        Self::new(Date::decode(dos_date), Time::decode(dos_time, dos_time_hi_res))
    }
}

#[cfg(feature = "chrono")]
impl From<Date> for chrono::NaiveDate {
    fn from(date: Date) -> Self {
        chrono::NaiveDate::from_ymd_opt(i32::from(date.year), u32::from(date.month), u32::from(date.day)).unwrap()
    }
}

#[cfg(feature = "chrono")]
impl From<DateTime> for chrono::NaiveDateTime {
    fn from(date_time: DateTime) -> Self {
        chrono::NaiveDate::from(date_time.date)
            .and_hms_milli_opt(
                u32::from(date_time.time.hour),
                u32::from(date_time.time.min),
                u32::from(date_time.time.sec),
                u32::from(date_time.time.millis),
            )
            .unwrap()
    }
}

#[cfg(feature = "chrono")]
impl From<chrono::NaiveDate> for Date {
    fn from(date: chrono::NaiveDate) -> Self {
        #[allow(clippy::cast_sign_loss)]
        let year = u16::try_from(date.year()).unwrap(); // safe unwrap unless year is below 0 or above u16::MAX
        assert!((MIN_YEAR..=MAX_YEAR).contains(&year), "year out of range");
        Self {
            year,
            month: date.month() as u16, // safe cast: value in range [1, 12]
            day: date.day() as u16,     // safe cast: value in range [1, 31]
        }
    }
}

#[cfg(feature = "chrono")]
impl From<chrono::NaiveDateTime> for DateTime {
    fn from(date_time: chrono::NaiveDateTime) -> Self {
        let millis_leap = date_time.nanosecond() / 1_000_000; // value in the range [0, 1999] (> 999 if leap second)
        let millis = millis_leap.min(999); // during leap second set milliseconds to 999
        let date = Date::from(date_time.date());
        #[allow(clippy::cast_possible_truncation)]
        let time = Time {
            hour: date_time.hour() as u16,  // safe cast: value in range [0, 23]
            min: date_time.minute() as u16, // safe cast: value in range [0, 59]
            sec: date_time.second() as u16, // safe cast: value in range [0, 59]
            millis: millis as u16,          // safe cast: value in range [0, 999]
        };
        Self::new(date, time)
    }
}

/// A current time and date provider.
///
/// Provides a custom implementation for a time resolution used when updating directory entry time fields.
/// `TimeProvider` is specified by the `time_provider` property in `FsOptions` struct.
pub trait TimeProvider: Debug {
    fn get_current_date(&self) -> Date;
    fn get_current_date_time(&self) -> DateTime;
}

/// `TimeProvider` implementation that returns current local time retrieved from `chrono` crate.
#[cfg(feature = "chrono")]
#[derive(Debug, Clone, Copy, Default)]
pub struct ChronoTimeProvider {
    _dummy: (),
}

#[cfg(feature = "chrono")]
impl ChronoTimeProvider {
    #[must_use]
    pub fn new() -> Self {
        Self { _dummy: () }
    }
}

#[cfg(feature = "chrono")]
impl TimeProvider for ChronoTimeProvider {
    fn get_current_date(&self) -> Date {
        Date::from(chrono::Local::now().date_naive())
    }

    fn get_current_date_time(&self) -> DateTime {
        DateTime::from(chrono::Local::now().naive_local())
    }
}

/// `TimeProvider` implementation that always returns DOS minimal date-time (1980-01-01 00:00:00).
#[derive(Debug, Clone, Copy, Default)]
pub struct NullTimeProvider {
    _dummy: (),
}

impl NullTimeProvider {
    #[must_use]
    pub fn new() -> Self {
        Self { _dummy: () }
    }
}

impl TimeProvider for NullTimeProvider {
    fn get_current_date(&self) -> Date {
        Date::decode(0)
    }

    fn get_current_date_time(&self) -> DateTime {
        DateTime::decode(0, 0, 0)
    }
}

/// Default time provider implementation.
///
/// Defined as `ChronoTimeProvider` if `chrono` feature is enabled. Otherwise defined as `NullTimeProvider`.
#[cfg(feature = "chrono")]
pub type DefaultTimeProvider = ChronoTimeProvider;
#[cfg(not(feature = "chrono"))]
pub type DefaultTimeProvider = NullTimeProvider;

#[cfg(test)]
mod tests {
    use super::{Date, DateTime, Time};

    #[test]
    fn date_new_no_panic_1980() {
        let _ = Date::new(1980, 1, 1);
    }

    #[test]
    #[should_panic]
    fn date_new_panic_year_1979() {
        let _ = Date::new(1979, 12, 31);
    }

    #[test]
    fn date_new_no_panic_2107() {
        let _ = Date::new(2107, 12, 31);
    }

    #[test]
    #[should_panic]
    fn date_new_panic_year_2108() {
        let _ = Date::new(2108, 1, 1);
    }

    #[test]
    fn date_encode_decode() {
        let d = Date::new(2055, 7, 23);
        let x = d.encode();
        assert_eq!(x, 38647);
        assert_eq!(d, Date::decode(x));
    }

    #[test]
    fn time_encode_decode() {
        let t1 = Time::new(15, 3, 29, 990);
        let t2 = Time { sec: 18, ..t1 };
        let t3 = Time { millis: 40, ..t1 };
        let (x1, y1) = t1.encode();
        let (x2, y2) = t2.encode();
        let (x3, y3) = t3.encode();
        assert_eq!((x1, y1), (30830, 199));
        assert_eq!((x2, y2), (30825, 99));
        assert_eq!((x3, y3), (30830, 104));
        assert_eq!(t1, Time::decode(x1, y1));
        assert_eq!(t2, Time::decode(x2, y2));
        assert_eq!(t3, Time::decode(x3, y3));
    }

    #[test]
    fn date_time_from_chrono_leap_second() {
        let chrono_date_time = chrono::NaiveDate::from_ymd_opt(2016, 12, 31)
            .unwrap()
            .and_hms_milli_opt(23, 59, 59, 1999)
            .unwrap();
        let date_time = DateTime::from(chrono_date_time);
        assert_eq!(
            date_time,
            DateTime::new(Date::new(2016, 12, 31), Time::new(23, 59, 59, 999))
        );
    }
}
