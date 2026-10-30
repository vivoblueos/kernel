# `max7219`

> A platform agnostic driver to interface with the MAX7219 (LED display driver)

[![Build Status](https://travis-ci.org/almindor/max7219.svg?branch=master)](https://travis-ci.org/almindor/max7219)

## What works

- Powering on/off the MAX chip
- Basic commands for setting LEDs on/off.
- Chaining support (max 8 devices)
- Hardware SPI support (with or without CS pin)

## [Changelog](CHANGELOG.md)

## Example

Example projects are at [this repo](https://github.com/almindor/max7219-examples)

Here is a simple example for using the MAX7219 on a hifive1-revb device with e310x_hal:
```rust
#![no_std]
#![no_main]

extern crate panic_halt;

use riscv_rt::entry;
use hifive1::hal::prelude::*;
use hifive1::hal::DeviceResources;
use hifive1::pin;
use max7219::*;

#[entry]
fn main() -> ! {
    let dr = DeviceResources::take().unwrap();
    let p = dr.peripherals;
    let gpio = dr.pins;

    // Configure clocks
    hifive1::clock::configure(p.PRCI, p.AONCLK, 320.mhz().into());
    
    let data = pin!(gpio, spi0_mosi).into_output();
    let sck = pin!(gpio, spi0_sck).into_output();
    let cs = pin!(gpio, spi0_ss0).into_output();

    let mut display = MAX7219::from_pins(1, data, cs, sck).unwrap();

    // make sure to wake the display up
    display.power_on().unwrap();
    // write given octet of ASCII characters with dots specified by 3rd param bits
    display.write_str(0, b"pls help", 0b00100000).unwrap();
    // set display intensity lower
    display.set_intensity(0, 0x1).unwrap();

    loop {}
}
```

## Credits

Original work by [Maikel Wever](https://github.com/maikelwever/max7219).
Adapted to latest embedded-hal and documented by Ales Katona.

## License

Licensed under MIT license ([LICENSE](LICENSE) or http://opensource.org/licenses/MIT)

