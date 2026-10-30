extern crate bme280;
extern crate linux_embedded_hal as hal;

use bme280::i2c::BME280;
use hal::{Delay, I2cdev};
use std::thread;
use std::time::Duration;

fn main() {
    let i2c_bus = I2cdev::new("/dev/i2c-1").unwrap();
    let mut bme280 = BME280::new_secondary(i2c_bus);
    let delay = /*... some delay */
    bme280.init(&mut delay).unwrap();
    loop {
        let measurements = bme280.measure(&mut delay).unwrap();
        println!("Relative Humidity = {}%", measurements.humidity);
        println!("Temperature = {} deg C", measurements.temperature);
        println!("Pressure = {} pascals", measurements.pressure);
        thread::sleep(Duration::from_secs(1));
    }
}
