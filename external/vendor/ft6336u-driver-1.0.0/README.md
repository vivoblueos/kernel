# FT6336U Touch Controller Driver

[![Crates.io](https://img.shields.io/crates/v/ft6336u-driver.svg)](https://crates.io/crates/ft6336u-driver)
[![Documentation](https://docs.rs/ft6336u-driver/badge.svg)](https://docs.rs/ft6336u-driver)
[![License](https://img.shields.io/badge/license-MIT%2FApache--2.0-blue.svg)](README.md#license)

A platform-agnostic Rust driver for the FT6336U capacitive touch controller, built using the [`embedded-hal`](https://github.com/rust-embedded/embedded-hal) traits.

## Features

- **`no_std` compatible** - Works in embedded environments without the standard library
- **Platform-agnostic** - Uses `embedded-hal` I2C traits for maximum portability
- **Multi-touch support** - Handles up to 2 simultaneous touch points
- **Gesture detection** - Built-in gesture recognition capabilities
- **Power management** - Configurable active and monitor modes for power efficiency
- **Interrupt-driven operation** - Support for both polling and interrupt modes
- **Comprehensive API** - Full access to all device registers and configuration options

## Hardware Support

The FT6336U is a capacitive touch controller commonly found in:
- Touch screen displays
- Touch panels
- Embedded systems with touch interfaces

**I2C Address:** `0x38`

## Installation

Add this to your `Cargo.toml`:

```toml
[dependencies]
ft6336u-driver = "1.0"
embedded-hal = "1.0"
```

## Usage

### Basic Example

```rust
use ft6336u_driver::FT6336U;

// Create the driver with your I2C peripheral
let mut touch = FT6336U::new(i2c);

// Scan for touch events
let touch_data = touch.scan().unwrap();

if touch_data.touch_count > 0 {
    let point = &touch_data.points[0];
    println!("Touch at ({}, {})", point.x, point.y);
}
```

### Polling Mode

Continuously poll for touch events:

```rust
use ft6336u_driver::{FT6336U, TouchStatus};

let mut touch = FT6336U::new(i2c);

loop {
    let data = touch.scan().unwrap();

    for i in 0..data.touch_count as usize {
        let point = &data.points[i];

        match point.status {
            TouchStatus::Touch => {
                println!("New touch at ({}, {})", point.x, point.y);
            }
            TouchStatus::Stream => {
                println!("Touch moved to ({}, {})", point.x, point.y);
            }
            TouchStatus::Release => {
                println!("Touch released");
            }
        }
    }

    delay.delay_ms(10);
}
```

### Interrupt Mode

For better power efficiency, use interrupt-driven operation:

```rust
use ft6336u_driver::{FT6336U, GestureMode};

let mut touch = FT6336U::new(i2c);

// Enable interrupt mode
touch.write_g_mode(GestureMode::Trigger).unwrap();

// In your interrupt handler:
// let data = touch.scan().unwrap();
// Process touch data...
```

### Reading Device Information

```rust
// Read chip ID (should be 0x64)
let chip_id = touch.read_chip_id().unwrap();

// Read firmware version
let firmware_id = touch.read_firmware_id().unwrap();

// Read library version
let lib_version = touch.read_library_version().unwrap();
```

## Hardware Integration

### Connections

- **SDA** - I2C data line (requires pull-up resistor)
- **SCL** - I2C clock line (requires pull-up resistor)
- **INT** - Interrupt output (optional, active low)
- **RST** - Reset input (active low)

### Typical Integration

1. Connect I2C lines with appropriate pull-up resistors (typically 4.7kΩ)
2. Connect reset pin to GPIO or GPIO expander
3. Connect interrupt pin to GPIO with interrupt capability (optional)
4. Initialize I2C at 100kHz or 400kHz
5. Reset the controller by toggling the reset pin
6. Create the driver and start scanning

### Example with GPIO Expander (e.g., AW9523B)

On some boards like the CoreSE-S3, the touch controller's reset and interrupt pins are managed through a GPIO expander:

```rust
// Configure expander pins
// - P0_0 (TOUCH_RST): Output mode
// - P1_2 (TOUCH_INT): Input mode with interrupt

// Reset sequence
expander.set_pin_low(P0_0);  // Assert reset
delay.delay_ms(10);
expander.set_pin_high(P0_0); // Release reset
delay.delay_ms(50);

// Create touch driver
let mut touch = FT6336U::new(i2c);

// Enable interrupt mode
touch.write_g_mode(GestureMode::Trigger).unwrap();
```

## Examples

The repository includes several examples:

- **`polling.rs`** - Continuous polling for touch events
- **`interrupt.rs`** - Interrupt-driven touch detection
- **`device_info.rs`** - Reading device information and configuration

Run examples with (requires hardware):

```bash
cargo build --example polling --target your-target
```

## API Documentation

For complete API documentation, visit [docs.rs/ft6336u-driver](https://docs.rs/ft6336u-driver).

Build documentation locally:

```bash
cargo doc --open
```

## Register Access

The driver provides both high-level methods (like `scan()`) and low-level register access:

```rust
// High-level touch scanning
let data = touch.scan().unwrap();

// Low-level register access
let threshold = touch.read_touch_threshold().unwrap();
touch.write_ctrl_mode(CtrlMode::KeepActive).unwrap();
```

## Supported Platforms

This driver works on any platform that implements the `embedded-hal` I2C traits, including:

- **ARM Cortex-M** (STM32, nRF, etc.)
- **RISC-V** (ESP32-C3, GD32V, etc.)
- **Xtensa** (ESP32, ESP32-S3, etc.)
- **AVR** (Arduino)
- Any other platform with `embedded-hal` support

## Testing

Run documentation tests:

```bash
cargo test --doc
```

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request.

## License

Licensed under either of:

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.

## References

- [FT6336U Datasheet](https://www.buydisplay.com/download/ic/FT6336U.pdf)
- [embedded-hal Documentation](https://docs.rs/embedded-hal)

## Author

**Trevor Flahardy**

---

**Note:** This is an unofficial driver and is not affiliated with or endorsed by FocalTech Systems Co., Ltd.

Platform-agnostic driver for the FT6336U capacitive touch controller using embedded-hal traits.
