//! Register addresses and constant values for the FT6336U touch controller.
//!
//! This module contains all the hardware register addresses and constant
//! values used to communicate with the FT6336U device.

// =============================================================================
// I2C Address
// =============================================================================

/// FT6336U I2C address
pub const I2C_ADDR: u8 = 0x38;

// =============================================================================
// Touch Parameters
// =============================================================================

/// Touch press down flag
pub const PRES_DOWN: u8 = 0x02;
/// Coordinate up/down flag
pub const COORD_UD: u8 = 0x01;

// =============================================================================
// Register Addresses
// =============================================================================

// Device Mode Register
/// Device mode register address
pub const ADDR_DEVICE_MODE: u8 = 0x00;

// Gesture and Touch Status Registers
/// Gesture ID register address
pub const ADDR_GESTURE_ID: u8 = 0x01;
/// Touch detection status register address
pub const ADDR_TD_STATUS: u8 = 0x02;

// Touch Point 1 Registers
/// Touch point 1 event register address
pub const ADDR_TOUCH1_EVENT: u8 = 0x03;
/// Touch point 1 ID register address
pub const ADDR_TOUCH1_ID: u8 = 0x05;
/// Touch point 1 X coordinate register address
pub const ADDR_TOUCH1_X: u8 = 0x03;
/// Touch point 1 Y coordinate register address
pub const ADDR_TOUCH1_Y: u8 = 0x05;
/// Touch point 1 weight register address
pub const ADDR_TOUCH1_WEIGHT: u8 = 0x07;
/// Touch point 1 miscellaneous data register address
pub const ADDR_TOUCH1_MISC: u8 = 0x08;

// Touch Point 2 Registers
/// Touch point 2 event register address
pub const ADDR_TOUCH2_EVENT: u8 = 0x09;
/// Touch point 2 ID register address
pub const ADDR_TOUCH2_ID: u8 = 0x0B;
/// Touch point 2 X coordinate register address
pub const ADDR_TOUCH2_X: u8 = 0x09;
/// Touch point 2 Y coordinate register address
pub const ADDR_TOUCH2_Y: u8 = 0x0B;
/// Touch point 2 weight register address
pub const ADDR_TOUCH2_WEIGHT: u8 = 0x0D;
/// Touch point 2 miscellaneous data register address
pub const ADDR_TOUCH2_MISC: u8 = 0x0E;

// Mode Parameter Registers
/// Touch detection threshold register address
pub const ADDR_THRESHOLD: u8 = 0x80;
/// Filter coefficient register address
pub const ADDR_FILTER_COE: u8 = 0x85;
/// Control mode register address
pub const ADDR_CTRL: u8 = 0x86;
/// Time to enter monitor mode register address
pub const ADDR_TIME_ENTER_MONITOR: u8 = 0x87;
/// Active mode report rate register address
pub const ADDR_ACTIVE_MODE_RATE: u8 = 0x88;
/// Monitor mode report rate register address
pub const ADDR_MONITOR_MODE_RATE: u8 = 0x89;

// Gesture Parameter Registers
/// Gesture radian value register address
pub const ADDR_RADIAN_VALUE: u8 = 0x91;
/// Gesture offset left/right register address
pub const ADDR_OFFSET_LEFT_RIGHT: u8 = 0x92;
/// Gesture offset up/down register address
pub const ADDR_OFFSET_UP_DOWN: u8 = 0x93;
/// Gesture distance left/right register address
pub const ADDR_DISTANCE_LEFT_RIGHT: u8 = 0x94;
/// Gesture distance up/down register address
pub const ADDR_DISTANCE_UP_DOWN: u8 = 0x95;
/// Gesture distance zoom register address
pub const ADDR_DISTANCE_ZOOM: u8 = 0x96;

// System Information Registers
/// Library version high byte register address
pub const ADDR_LIBRARY_VERSION_H: u8 = 0xA1;
/// Library version low byte register address
pub const ADDR_LIBRARY_VERSION_L: u8 = 0xA2;
/// Chip ID register address
pub const ADDR_CHIP_ID: u8 = 0xA3;
/// Gesture mode register address
pub const ADDR_G_MODE: u8 = 0xA4;
/// Power mode register address
pub const ADDR_POWER_MODE: u8 = 0xA5;
/// Firmware ID register address
pub const ADDR_FIRMWARE_ID: u8 = 0xA6;
/// Focaltech ID register address
pub const ADDR_FOCALTECH_ID: u8 = 0xA8;
/// Release code ID register address
pub const ADDR_RELEASE_CODE_ID: u8 = 0xAF;
/// Device state register address
pub const ADDR_STATE: u8 = 0xBC;
