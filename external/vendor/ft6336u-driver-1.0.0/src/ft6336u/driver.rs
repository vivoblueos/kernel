//! Driver implementation for the FT6336U touch controller.
//!
//! This module contains the main driver struct and all its methods
//! for interacting with the FT6336U hardware.

use embedded_hal::i2c::I2c;

use super::constants::*;
use super::error::Error;
use super::types::*;

/// FT6336U capacitive touch controller driver with async I2C interface
///
/// This driver provides a high-level interface to the FT6336U touch controller,
/// supporting touch scanning, gesture detection, and configuration of various
/// operating parameters.
///
/// # Examples
///
/// Basic usage with polling:
///
/// ```rust,no_run
/// # use embedded_hal::i2c::I2c;
/// # use core::convert::Infallible;
/// # struct MockI2c;
/// # impl embedded_hal::i2c::ErrorType for MockI2c {
/// #     type Error = Infallible;
/// # }
/// # impl I2c for MockI2c {
/// #     fn write(&mut self, _: u8, _: &[u8]) -> Result<(), Self::Error> { Ok(()) }
/// #     fn read(&mut self, _: u8, _: &mut [u8]) -> Result<(), Self::Error> { Ok(()) }
/// #     fn write_read(&mut self, _: u8, _: &[u8], _: &mut [u8]) -> Result<(), Self::Error> { Ok(()) }
/// #     fn transaction(&mut self, _: u8, _: &mut [embedded_hal::i2c::Operation<'_>]) -> Result<(), Self::Error> { Ok(()) }
/// # }
/// # let i2c = MockI2c;
/// use ft6336u_driver::FT6336U;
///
/// let mut touch = FT6336U::new(i2c);
///
/// // Poll for touch events in a loop
/// loop {
///     let data = touch.scan().unwrap();
///
///     for i in 0..data.touch_count as usize {
///         let point = &data.points[i];
///         // Process touch point...
///     }
/// }
/// ```
///
/// Reading device information:
///
/// ```rust,no_run
/// # use embedded_hal::i2c::I2c;
/// # use core::convert::Infallible;
/// # struct MockI2c;
/// # impl embedded_hal::i2c::ErrorType for MockI2c {
/// #     type Error = Infallible;
/// # }
/// # impl I2c for MockI2c {
/// #     fn write(&mut self, _: u8, _: &[u8]) -> Result<(), Self::Error> { Ok(()) }
/// #     fn read(&mut self, _: u8, _: &mut [u8]) -> Result<(), Self::Error> { Ok(()) }
/// #     fn write_read(&mut self, _: u8, _: &[u8], _: &mut [u8]) -> Result<(), Self::Error> { Ok(()) }
/// #     fn transaction(&mut self, _: u8, _: &mut [embedded_hal::i2c::Operation<'_>]) -> Result<(), Self::Error> { Ok(()) }
/// # }
/// # let i2c = MockI2c;
/// use ft6336u_driver::FT6336U;
///
/// let mut touch = FT6336U::new(i2c);
///
/// // Read device information (these will return errors with MockI2c)
/// // let chip_id = touch.read_chip_id().unwrap();
/// // let firmware_id = touch.read_firmware_id().unwrap();
/// ```
pub struct FT6336U<I2C> {
    /// I2C bus for communicating with the touch controller
    i2c: I2C,
    /// Cached touch point data from last scan
    touch_data: TouchData,
}

impl<I2C> FT6336U<I2C>
where
    I2C: I2c,
{
    /// Create a new FT6336U driver instance
    ///
    /// # Arguments
    /// * `i2c` - I2C bus instance that implements embedded_hal::i2c::I2c
    ///
    /// # Note
    /// The reset and interrupt pins should be managed by the AW9523B GPIO expander
    /// or by the calling code before creating this driver instance.
    pub fn new(i2c: I2C) -> Self {
        Self {
            i2c,
            touch_data: TouchData::default(),
        }
    }

    // =========================================================================
    // Private I2C Helper Methods
    // =========================================================================

    /// Read a single byte from a register
    fn read_byte(&mut self, addr: u8) -> Result<u8, Error<I2C::Error>> {
        let mut buf = [0u8; 1];
        self.i2c.write_read(I2C_ADDR, &[addr], &mut buf)?;
        Ok(buf[0])
    }

    /// Write a single byte to a register
    fn write_byte(&mut self, addr: u8, data: u8) -> Result<(), Error<I2C::Error>> {
        self.i2c.write(I2C_ADDR, &[addr, data])?;
        Ok(())
    }

    // =========================================================================
    // Device Mode Register Methods
    // =========================================================================

    /// Read the current device operating mode
    ///
    /// # Returns
    /// The device mode (Working or Factory)
    pub fn read_device_mode(&mut self) -> Result<u8, Error<I2C::Error>> {
        let val = self.read_byte(ADDR_DEVICE_MODE)?;
        Ok((val & 0x70) >> 4)
    }

    /// Write the device operating mode
    ///
    /// # Arguments
    /// * `mode` - The desired device mode
    pub fn write_device_mode(&mut self, mode: DeviceMode) -> Result<(), Error<I2C::Error>> {
        self.write_byte(ADDR_DEVICE_MODE, mode.to_register())
    }

    // =========================================================================
    // Gesture and Touch Status Methods
    // =========================================================================

    /// Read the gesture ID register
    ///
    /// # Returns
    /// Gesture ID value
    pub fn read_gesture_id(&mut self) -> Result<u8, Error<I2C::Error>> {
        self.read_byte(ADDR_GESTURE_ID)
    }

    /// Read the touch detection status register
    ///
    /// # Returns
    /// Raw TD_STATUS register value
    pub fn read_td_status(&mut self) -> Result<u8, Error<I2C::Error>> {
        self.read_byte(ADDR_TD_STATUS)
    }

    /// Read the number of detected touch points
    ///
    /// # Returns
    /// Number of touch points (0-2)
    pub fn read_touch_number(&mut self) -> Result<u8, Error<I2C::Error>> {
        let val = self.read_byte(ADDR_TD_STATUS)?;
        Ok(val & 0x0F)
    }

    // =========================================================================
    // Touch Point 1 Methods
    // =========================================================================

    /// Read X coordinate of touch point 1
    ///
    /// # Returns
    /// X coordinate (0-4095, 12-bit value)
    pub fn read_touch1_x(&mut self) -> Result<u16, Error<I2C::Error>> {
        let mut buf = [0u8; 2];
        self.i2c.write_read(I2C_ADDR, &[ADDR_TOUCH1_X], &mut buf)?;
        Ok((((buf[0] & 0x0F) as u16) << 8) | (buf[1] as u16))
    }

    /// Read Y coordinate of touch point 1
    ///
    /// # Returns
    /// Y coordinate (0-4095, 12-bit value)
    pub fn read_touch1_y(&mut self) -> Result<u16, Error<I2C::Error>> {
        let mut buf = [0u8; 2];
        self.i2c.write_read(I2C_ADDR, &[ADDR_TOUCH1_Y], &mut buf)?;
        Ok((((buf[0] & 0x0F) as u16) << 8) | (buf[1] as u16))
    }

    /// Read event type of touch point 1
    ///
    /// # Returns
    /// Event type (0=down, 1=up, 2=contact)
    pub fn read_touch1_event(&mut self) -> Result<u8, Error<I2C::Error>> {
        let val = self.read_byte(ADDR_TOUCH1_EVENT)?;
        Ok(val >> 6)
    }

    /// Read ID of touch point 1
    ///
    /// # Returns
    /// Touch point ID (0 or 1)
    pub fn read_touch1_id(&mut self) -> Result<u8, Error<I2C::Error>> {
        let val = self.read_byte(ADDR_TOUCH1_ID)?;
        Ok(val >> 4)
    }

    /// Read weight/pressure of touch point 1
    ///
    /// # Returns
    /// Touch weight value
    pub fn read_touch1_weight(&mut self) -> Result<u8, Error<I2C::Error>> {
        self.read_byte(ADDR_TOUCH1_WEIGHT)
    }

    /// Read miscellaneous data for touch point 1
    ///
    /// # Returns
    /// Misc data value
    pub fn read_touch1_misc(&mut self) -> Result<u8, Error<I2C::Error>> {
        let val = self.read_byte(ADDR_TOUCH1_MISC)?;
        Ok(val >> 4)
    }

    // =========================================================================
    // Touch Point 2 Methods
    // =========================================================================

    /// Read X coordinate of touch point 2
    ///
    /// # Returns
    /// X coordinate (0-4095, 12-bit value)
    pub fn read_touch2_x(&mut self) -> Result<u16, Error<I2C::Error>> {
        let mut buf = [0u8; 2];
        self.i2c.write_read(I2C_ADDR, &[ADDR_TOUCH2_X], &mut buf)?;
        Ok((((buf[0] & 0x0F) as u16) << 8) | (buf[1] as u16))
    }

    /// Read Y coordinate of touch point 2
    ///
    /// # Returns
    /// Y coordinate (0-4095, 12-bit value)
    pub fn read_touch2_y(&mut self) -> Result<u16, Error<I2C::Error>> {
        let mut buf = [0u8; 2];
        self.i2c.write_read(I2C_ADDR, &[ADDR_TOUCH2_Y], &mut buf)?;
        Ok((((buf[0] & 0x0F) as u16) << 8) | (buf[1] as u16))
    }

    /// Read event type of touch point 2
    ///
    /// # Returns
    /// Event type (0=down, 1=up, 2=contact)
    pub fn read_touch2_event(&mut self) -> Result<u8, Error<I2C::Error>> {
        let val = self.read_byte(ADDR_TOUCH2_EVENT)?;
        Ok(val >> 6)
    }

    /// Read ID of touch point 2
    ///
    /// # Returns
    /// Touch point ID (0 or 1)
    pub fn read_touch2_id(&mut self) -> Result<u8, Error<I2C::Error>> {
        let val = self.read_byte(ADDR_TOUCH2_ID)?;
        Ok(val >> 4)
    }

    /// Read weight/pressure of touch point 2
    ///
    /// # Returns
    /// Touch weight value
    pub fn read_touch2_weight(&mut self) -> Result<u8, Error<I2C::Error>> {
        self.read_byte(ADDR_TOUCH2_WEIGHT)
    }

    /// Read miscellaneous data for touch point 2
    ///
    /// # Returns
    /// Misc data value
    pub fn read_touch2_misc(&mut self) -> Result<u8, Error<I2C::Error>> {
        let val = self.read_byte(ADDR_TOUCH2_MISC)?;
        Ok(val >> 4)
    }

    // =========================================================================
    // Mode Parameter Register Methods
    // =========================================================================

    /// Read the touch detection threshold
    ///
    /// # Returns
    /// Threshold value (lower = more sensitive)
    pub fn read_touch_threshold(&mut self) -> Result<u8, Error<I2C::Error>> {
        self.read_byte(ADDR_THRESHOLD)
    }

    /// Read the filter coefficient
    ///
    /// # Returns
    /// Filter coefficient value
    pub fn read_filter_coefficient(&mut self) -> Result<u8, Error<I2C::Error>> {
        self.read_byte(ADDR_FILTER_COE)
    }

    /// Read the control mode register
    ///
    /// # Returns
    /// Control mode value
    pub fn read_ctrl_mode(&mut self) -> Result<u8, Error<I2C::Error>> {
        self.read_byte(ADDR_CTRL)
    }

    /// Write the control mode
    ///
    /// # Arguments
    /// * `mode` - Control mode (KeepActive or SwitchToMonitor)
    pub fn write_ctrl_mode(&mut self, mode: CtrlMode) -> Result<(), Error<I2C::Error>> {
        self.write_byte(ADDR_CTRL, mode as u8)
    }

    /// Read the time period to enter monitor mode
    ///
    /// # Returns
    /// Time period value in seconds
    pub fn read_time_period_enter_monitor(&mut self) -> Result<u8, Error<I2C::Error>> {
        self.read_byte(ADDR_TIME_ENTER_MONITOR)
    }

    /// Read the active mode report rate
    ///
    /// # Returns
    /// Report rate in Hz
    pub fn read_active_rate(&mut self) -> Result<u8, Error<I2C::Error>> {
        self.read_byte(ADDR_ACTIVE_MODE_RATE)
    }

    /// Read the monitor mode report rate
    ///
    /// # Returns
    /// Report rate in Hz
    pub fn read_monitor_rate(&mut self) -> Result<u8, Error<I2C::Error>> {
        self.read_byte(ADDR_MONITOR_MODE_RATE)
    }

    // =========================================================================
    // Gesture Parameter Register Methods
    // =========================================================================

    /// Read the radian value for gesture detection
    ///
    /// # Returns
    /// Radian value
    pub fn read_radian_value(&mut self) -> Result<u8, Error<I2C::Error>> {
        self.read_byte(ADDR_RADIAN_VALUE)
    }

    /// Write the radian value for gesture detection
    ///
    /// # Arguments
    /// * `val` - Radian value to set
    pub fn write_radian_value(&mut self, val: u8) -> Result<(), Error<I2C::Error>> {
        self.write_byte(ADDR_RADIAN_VALUE, val)
    }

    /// Read the offset for left/right gesture detection
    ///
    /// # Returns
    /// Offset value
    pub fn read_offset_left_right(&mut self) -> Result<u8, Error<I2C::Error>> {
        self.read_byte(ADDR_OFFSET_LEFT_RIGHT)
    }

    /// Write the offset for left/right gesture detection
    ///
    /// # Arguments
    /// * `val` - Offset value to set
    pub fn write_offset_left_right(&mut self, val: u8) -> Result<(), Error<I2C::Error>> {
        self.write_byte(ADDR_OFFSET_LEFT_RIGHT, val)
    }

    /// Read the offset for up/down gesture detection
    ///
    /// # Returns
    /// Offset value
    pub fn read_offset_up_down(&mut self) -> Result<u8, Error<I2C::Error>> {
        self.read_byte(ADDR_OFFSET_UP_DOWN)
    }

    /// Write the offset for up/down gesture detection
    ///
    /// # Arguments
    /// * `val` - Offset value to set
    pub fn write_offset_up_down(&mut self, val: u8) -> Result<(), Error<I2C::Error>> {
        self.write_byte(ADDR_OFFSET_UP_DOWN, val)
    }

    /// Read the distance for left/right gesture detection
    ///
    /// # Returns
    /// Distance value
    pub fn read_distance_left_right(&mut self) -> Result<u8, Error<I2C::Error>> {
        self.read_byte(ADDR_DISTANCE_LEFT_RIGHT)
    }

    /// Write the distance for left/right gesture detection
    ///
    /// # Arguments
    /// * `val` - Distance value to set
    pub fn write_distance_left_right(&mut self, val: u8) -> Result<(), Error<I2C::Error>> {
        self.write_byte(ADDR_DISTANCE_LEFT_RIGHT, val)
    }

    /// Read the distance for up/down gesture detection
    ///
    /// # Returns
    /// Distance value
    pub fn read_distance_up_down(&mut self) -> Result<u8, Error<I2C::Error>> {
        self.read_byte(ADDR_DISTANCE_UP_DOWN)
    }

    /// Write the distance for up/down gesture detection
    ///
    /// # Arguments
    /// * `val` - Distance value to set
    pub fn write_distance_up_down(&mut self, val: u8) -> Result<(), Error<I2C::Error>> {
        self.write_byte(ADDR_DISTANCE_UP_DOWN, val)
    }

    /// Read the distance for zoom gesture detection
    ///
    /// # Returns
    /// Distance value
    pub fn read_distance_zoom(&mut self) -> Result<u8, Error<I2C::Error>> {
        self.read_byte(ADDR_DISTANCE_ZOOM)
    }

    /// Write the distance for zoom gesture detection
    ///
    /// # Arguments
    /// * `val` - Distance value to set
    pub fn write_distance_zoom(&mut self, val: u8) -> Result<(), Error<I2C::Error>> {
        self.write_byte(ADDR_DISTANCE_ZOOM, val)
    }

    // =========================================================================
    // System Information Methods
    // =========================================================================

    /// Read the library version from the device
    ///
    /// # Returns
    /// 16-bit library version number
    pub fn read_library_version(&mut self) -> Result<u16, Error<I2C::Error>> {
        let mut buf = [0u8; 2];
        self.i2c
            .write_read(I2C_ADDR, &[ADDR_LIBRARY_VERSION_H], &mut buf)?;
        Ok((((buf[0] & 0x0F) as u16) << 8) | (buf[1] as u16))
    }

    /// Read the chip ID
    ///
    /// # Returns
    /// Chip ID (should be 0x64 for FT6336U)
    pub fn read_chip_id(&mut self) -> Result<u8, Error<I2C::Error>> {
        self.read_byte(ADDR_CHIP_ID)
    }

    /// Read the gesture/interrupt mode
    ///
    /// # Returns
    /// G_MODE register value
    pub fn read_g_mode(&mut self) -> Result<u8, Error<I2C::Error>> {
        self.read_byte(ADDR_G_MODE)
    }

    /// Write the gesture/interrupt mode
    ///
    /// # Arguments
    /// * `mode` - Gesture mode (Polling or Trigger)
    pub fn write_g_mode(&mut self, mode: GestureMode) -> Result<(), Error<I2C::Error>> {
        self.write_byte(ADDR_G_MODE, mode as u8)
    }

    /// Read the power mode
    ///
    /// # Returns
    /// Power mode value
    pub fn read_pwrmode(&mut self) -> Result<u8, Error<I2C::Error>> {
        self.read_byte(ADDR_POWER_MODE)
    }

    /// Read the firmware ID
    ///
    /// # Returns
    /// Firmware ID value
    pub fn read_firmware_id(&mut self) -> Result<u8, Error<I2C::Error>> {
        self.read_byte(ADDR_FIRMWARE_ID)
    }

    /// Read the Focaltech ID
    ///
    /// # Returns
    /// Focaltech ID value
    pub fn read_focaltech_id(&mut self) -> Result<u8, Error<I2C::Error>> {
        self.read_byte(ADDR_FOCALTECH_ID)
    }

    /// Read the release code ID
    ///
    /// # Returns
    /// Release code ID value
    pub fn read_release_code_id(&mut self) -> Result<u8, Error<I2C::Error>> {
        self.read_byte(ADDR_RELEASE_CODE_ID)
    }

    /// Read the device state
    ///
    /// # Returns
    /// Device state value
    pub fn read_state(&mut self) -> Result<u8, Error<I2C::Error>> {
        self.read_byte(ADDR_STATE)
    }

    // =========================================================================
    // High-Level Scan Method
    // =========================================================================

    /// Scan for touch events and update internal touch data
    ///
    /// This is the main method to call periodically or in response to interrupts
    /// to read the current touch state. It reads all touch point data and updates
    /// the internal touch data structure.
    ///
    /// # Returns
    /// TouchData containing the number of touch points and their coordinates/status
    pub fn scan(&mut self) -> Result<TouchData, Error<I2C::Error>> {
        // Read the number of touch points
        let touch_count = self.read_touch_number()?;
        self.touch_data.touch_count = touch_count;

        if touch_count == 0 {
            // No touches - mark both points as released
            self.touch_data.points[0].status = TouchStatus::Release;
            self.touch_data.points[1].status = TouchStatus::Release;
        } else if touch_count == 1 {
            // Single touch point
            let id1 = self.read_touch1_id()? as usize;
            if id1 < 2 {
                // Update status: if previously released, mark as new touch, otherwise streaming
                let prev_status = self.touch_data.points[id1].status;
                self.touch_data.points[id1].status = match prev_status {
                    TouchStatus::Release => TouchStatus::Touch,
                    _ => TouchStatus::Stream,
                };

                // Read coordinates
                self.touch_data.points[id1].x = self.read_touch1_x()?;
                self.touch_data.points[id1].y = self.read_touch1_y()?;

                // Mark the other point as released
                let other_id = (!id1) & 0x01;
                self.touch_data.points[other_id].status = TouchStatus::Release;
            }
        } else {
            // Two touch points
            let id1 = self.read_touch1_id()? as usize;
            if id1 < 2 {
                let prev_status1 = self.touch_data.points[id1].status;
                self.touch_data.points[id1].status = match prev_status1 {
                    TouchStatus::Release => TouchStatus::Touch,
                    _ => TouchStatus::Stream,
                };
                self.touch_data.points[id1].x = self.read_touch1_x()?;
                self.touch_data.points[id1].y = self.read_touch1_y()?;
            }

            let id2 = self.read_touch2_id()? as usize;
            if id2 < 2 {
                let prev_status2 = self.touch_data.points[id2].status;
                self.touch_data.points[id2].status = match prev_status2 {
                    TouchStatus::Release => TouchStatus::Touch,
                    _ => TouchStatus::Stream,
                };
                self.touch_data.points[id2].x = self.read_touch2_x()?;
                self.touch_data.points[id2].y = self.read_touch2_y()?;
            }
        }

        Ok(self.touch_data)
    }
}
