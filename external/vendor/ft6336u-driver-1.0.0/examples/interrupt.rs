//! Interrupt-driven example for the FT6336U touch controller
//!
//! This example demonstrates how to use the touch controller in interrupt mode,
//! which is more power-efficient than continuous polling.
//!
//! # Hardware Requirements
//!
//! - A microcontroller with I2C support and GPIO interrupts
//! - FT6336U touch controller connected via I2C
//! - Interrupt pin connected from FT6336U to MCU GPIO
//! - Optional: Reset pin for touch controller initialization
//!
//! # Note
//!
//! This is a no_run example as it requires actual hardware.

fn main() {
    // This example demonstrates the structure for embedded use
    // In a real embedded application, you would:
    // Initialize your hardware
    // let peripherals = Peripherals::take();

    // Initialize I2C
    // let i2c = I2c::new(peripherals.I2C0, sda, scl, 400u32.kHz());
    // let mut touch = FT6336U::new(i2c);

    // Configure the touch controller for interrupt mode
    // touch.write_g_mode(GestureMode::Trigger).unwrap();

    // Configure your interrupt pin
    // let mut touch_int = Input::new(touch_int_pin, Pull::Up);
    // touch_int.listen(Event::FallingEdge);

    // Read device info for verification
    // let chip_id = touch.read_chip_id().unwrap();
    // println!("FT6336U Chip ID: 0x{:02X}", chip_id);

    // let firmware_id = touch.read_firmware_id().unwrap();
    // println!("Firmware ID: 0x{:02X}", firmware_id);

    // Main loop
    // loop {
    //     // Wait for interrupt
    //     touch_int.wait_for_falling_edge().await;
    //
    //     // Read touch data
    //     match touch.scan() {
    //         Ok(data) => {
    //             if data.touch_count > 0 {
    //                 for i in 0..data.touch_count as usize {
    //                     let point = &data.points[i];
    //
    //                     match point.status {
    //                         TouchStatus::Touch => {
    //                             println!("Touch #{} started at ({}, {})", i, point.x, point.y);
    //                         }
    //                         TouchStatus::Stream => {
    //                             println!("Touch #{} at ({}, {})", i, point.x, point.y);
    //                         }
    //                         TouchStatus::Release => {
    //                             println!("Touch #{} ended", i);
    //                         }
    //                     }
    //                 }
    //             }
    //         }
    //         Err(e) => {
    //             println!("Touch read error: {:?}", e);
    //         }
    //     }
    // }

    println!("This is a template for embedded use. See comments for implementation.");
}
