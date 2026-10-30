//! Device information reading example
//!
//! This example demonstrates how to read various device information
//! from the FT6336U touch controller, including chip ID, firmware version,
//! and configuration parameters.
//!
//! # Hardware Requirements
//!
//! - A microcontroller with I2C support
//! - FT6336U touch controller connected via I2C
//!
//! # Note
//!
//! This is a no_run example as it requires actual hardware.

fn main() {
    // This example demonstrates the structure for embedded use
    // In a real embedded application, you would:
    // Initialize I2C peripheral
    // let i2c = ...; // Your I2C initialization here
    // let mut touch = FT6336U::new(i2c);

    // Read chip identification
    // println!("=== FT6336U Device Information ===");

    // Chip ID (should be 0x64 for FT6336U)
    // match touch.read_chip_id() {
    //     Ok(id) => println!("Chip ID: 0x{:02X}", id),
    //     Err(e) => println!("Error reading chip ID: {:?}", e),
    // }

    // Firmware ID
    // match touch.read_firmware_id() {
    //     Ok(id) => println!("Firmware ID: 0x{:02X}", id),
    //     Err(e) => println!("Error reading firmware ID: {:?}", e),
    // }

    // Library version
    // match touch.read_library_version() {
    //     Ok(version) => println!("Library Version: 0x{:04X}", version),
    //     Err(e) => println!("Error reading library version: {:?}", e),
    // }

    // Focaltech ID
    // match touch.read_focaltech_id() {
    //     Ok(id) => println!("Focaltech ID: 0x{:02X}", id),
    //     Err(e) => println!("Error reading Focaltech ID: {:?}", e),
    // }

    // Release code ID
    // match touch.read_release_code_id() {
    //     Ok(id) => println!("Release Code ID: 0x{:02X}", id),
    //     Err(e) => println!("Error reading release code: {:?}", e),
    // }

    // Read configuration parameters
    // println!("\n=== Configuration Parameters ===");

    // Device mode
    // match touch.read_device_mode() {
    //     Ok(mode) => println!("Device Mode: {}", mode),
    //     Err(e) => println!("Error reading device mode: {:?}", e),
    // }

    // Touch threshold
    // match touch.read_touch_threshold() {
    //     Ok(threshold) => println!("Touch Threshold: {}", threshold),
    //     Err(e) => println!("Error reading threshold: {:?}", e),
    // }

    // Active mode report rate
    // match touch.read_active_rate() {
    //     Ok(rate) => println!("Active Rate: {} Hz", rate),
    //     Err(e) => println!("Error reading active rate: {:?}", e),
    // }

    // Monitor mode report rate
    // match touch.read_monitor_rate() {
    //     Ok(rate) => println!("Monitor Rate: {} Hz", rate),
    //     Err(e) => println!("Error reading monitor rate: {:?}", e),
    // }

    // Power mode
    // match touch.read_pwrmode() {
    //     Ok(mode) => println!("Power Mode: 0x{:02X}", mode),
    //     Err(e) => println!("Error reading power mode: {:?}", e),
    // }

    // State
    // match touch.read_state() {
    //     Ok(state) => println!("State: 0x{:02X}", state),
    //     Err(e) => println!("Error reading state: {:?}", e),
    // }

    println!("This is a template for embedded use. See comments for implementation.");
}
