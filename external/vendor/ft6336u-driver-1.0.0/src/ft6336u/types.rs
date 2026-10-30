//! Type definitions for the FT6336U touch controller.
//!
//! This module contains enums and structs representing the various
//! states and data structures used by the touch controller.

/// Device operating mode
///
/// The FT6336U can operate in different modes for normal operation or factory testing.
///
/// # Examples
///
/// ```rust
/// use ft6336u_driver::DeviceMode;
///
/// let mode = DeviceMode::Working;
/// assert_eq!(mode.to_register(), 0x00);
///
/// let parsed = DeviceMode::from_register(0x00).unwrap();
/// assert_eq!(parsed, DeviceMode::Working);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum DeviceMode {
    /// Working mode (normal operation)
    Working = 0b000,
    /// Factory mode (calibration/testing)
    Factory = 0b100,
}

impl DeviceMode {
    /// Convert from raw register value
    pub fn from_register(val: u8) -> Option<Self> {
        match val & 0b111 {
            0b000 => Some(Self::Working),
            0b100 => Some(Self::Factory),
            _ => None,
        }
    }

    /// Convert to register value
    pub fn to_register(self) -> u8 {
        (self as u8) << 4
    }
}

/// Control mode for power management
///
/// Controls whether the device stays in active mode or switches to lower-power monitor mode.
///
/// # Examples
///
/// ```rust
/// use ft6336u_driver::CtrlMode;
///
/// let mode = CtrlMode::KeepActive;
/// assert_eq!(CtrlMode::from_register(0).unwrap(), CtrlMode::KeepActive);
/// assert_eq!(CtrlMode::from_register(1).unwrap(), CtrlMode::SwitchToMonitor);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum CtrlMode {
    /// Keep the device in active mode
    KeepActive = 0,
    /// Switch to monitor mode
    SwitchToMonitor = 1,
}

impl CtrlMode {
    /// Convert from raw register value
    pub fn from_register(val: u8) -> Option<Self> {
        match val {
            0 => Some(Self::KeepActive),
            1 => Some(Self::SwitchToMonitor),
            _ => None,
        }
    }
}

/// Gesture mode (interrupt trigger configuration)
///
/// Configures whether the device generates interrupts on touch events or requires polling.
///
/// # Examples
///
/// ```rust
/// use ft6336u_driver::GestureMode;
///
/// let mode = GestureMode::Trigger;
/// assert_eq!(GestureMode::from_register(1).unwrap(), GestureMode::Trigger);
/// assert_eq!(GestureMode::from_register(0).unwrap(), GestureMode::Polling);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum GestureMode {
    /// Polling mode - no interrupts
    Polling = 0,
    /// Trigger mode - generate interrupts on touch events
    Trigger = 1,
}

impl GestureMode {
    /// Convert from raw register value
    pub fn from_register(val: u8) -> Option<Self> {
        match val {
            0 => Some(Self::Polling),
            1 => Some(Self::Trigger),
            _ => None,
        }
    }
}

/// Touch event status for a single touch point
///
/// Indicates whether a touch is new, continuing, or has been released.
///
/// # Examples
///
/// ```rust
/// use ft6336u_driver::TouchStatus;
///
/// // A new touch starts as Touch, then becomes Stream for continuous contact
/// let status = TouchStatus::Touch;
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TouchStatus {
    /// Initial touch detected
    Touch,
    /// Continuous touch (streaming)
    Stream,
    /// Touch released
    Release,
}

/// A single touch point with coordinates and status
///
/// Represents one touch point detected by the FT6336U. The controller can detect
/// up to 2 simultaneous touch points.
///
/// # Examples
///
/// ```rust
/// use ft6336u_driver::{TouchPoint, TouchStatus};
///
/// let point = TouchPoint {
///     status: TouchStatus::Touch,
///     x: 120,
///     y: 240,
/// };
///
/// println!("Touch detected at ({}, {})", point.x, point.y);
/// ```
#[derive(Debug, Clone, Copy)]
pub struct TouchPoint {
    /// Touch status
    pub status: TouchStatus,
    /// X coordinate
    pub x: u16,
    /// Y coordinate
    pub y: u16,
}

impl Default for TouchPoint {
    fn default() -> Self {
        Self {
            status: TouchStatus::Release,
            x: 0,
            y: 0,
        }
    }
}

/// Complete touch data including up to 2 touch points
///
/// Contains the results of a touch scan, including the number of active touches
/// and data for each detected touch point.
///
/// # Examples
///
/// ```rust
/// use ft6336u_driver::{TouchData, TouchStatus};
///
/// let mut data = TouchData::default();
/// data.touch_count = 1;
/// data.points[0].status = TouchStatus::Touch;
/// data.points[0].x = 100;
/// data.points[0].y = 200;
///
/// if data.touch_count > 0 {
///     println!("Touch at ({}, {})", data.points[0].x, data.points[0].y);
/// }
/// ```
#[derive(Debug, Clone, Copy, Default)]
pub struct TouchData {
    /// Number of active touch points (0-2)
    pub touch_count: u8,
    /// Touch point data (up to 2 points)
    pub points: [TouchPoint; 2],
}
