#![no_main]
#![no_std]

use panic_semihosting as _;

#[rtic::app(device = stm32f4xx_hal::pac)]
mod app {
    use bme280::i2c::BME280;
    use stm32f4xx_hal::{
        gpio::{Alternate, OpenDrain, Pin},
        i2c::{DutyCycle, I2c, I2c1, Mode},
        pac::{I2C1, TIM2},
        prelude::*,
        timer::delay::Delay,
    };

    type Scl = Pin<Alternate<OpenDrain, 4>, 'B', 6>;
    type Sda = Pin<Alternate<OpenDrain, 4>, 'B', 7>;

    #[shared]
    struct Shared {}

    #[local]
    struct Local {
        bme: BME280<I2c<I2C1, (Scl, Sda)>>,
        delay: Delay<TIM2, 1000000>,
    }

    #[init]
    fn init(cx: init::Context) -> (Shared, Local, init::Monotonics) {
        // Get access to the device specific peripherals from the peripheral access crate
        let dp = cx.device;

        // Take ownership over the raw flash and rcc devices and convert them into the corresponding
        // HAL structs
        let rcc = dp.RCC.constrain();
        // Freeze the configuration of all the clocks in the system and store the frozen frequencies in
        // `clocks`
        let clocks = rcc.cfgr.use_hse(25.MHz()).sysclk(100.MHz()).freeze();

        let gpiob = dp.GPIOB.split();
        // I2C config
        let i2c_scl = gpiob
            .pb6
            .into_alternate()
            .internal_pull_up(false)
            .set_open_drain();
        let i2c_sda = gpiob
            .pb7
            .into_alternate()
            .internal_pull_up(false)
            .set_open_drain();

        let i2c = I2c1::new(
            dp.I2C1,
            (i2c_scl, i2c_sda),
            Mode::Fast {
                frequency: 400000.Hz(),
                duty_cycle: DutyCycle::Ratio2to1,
            },
            &clocks,
        );

        //Initialize the sensor
        let mut delay = dp.TIM2.delay_us(&clocks);
        let mut bme = BME280::new_primary(i2c);
        bme.init(&mut delay)
            .map_err(|_| {
                defmt::println!("Could not initialize bme280, Error");
                panic!();
            })
            .unwrap();

        (Shared {}, Local { bme, delay }, init::Monotonics())
    }

    #[idle(local = [bme, delay])]
    fn idle(cx: idle::Context) -> ! {
        let bme = cx.local.bme;
        let delay = cx.local.delay;

        loop {
            match bme.measure(delay) {
                Ok(measurements) => {
                    defmt::println!("Relative Humidity = {}%", measurements.humidity);
                    defmt::println!("Temperature = {} deg C", measurements.temperature);
                    defmt::println!("Pressure = {} pascals", measurements.pressure);
                }
                Err(_) => {
                    defmt::println!("Could not read bme280 due to error");
                }
            }
            let _ = delay.delay_ms(5000u32);
        }
    }
}
