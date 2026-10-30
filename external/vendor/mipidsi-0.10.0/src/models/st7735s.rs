use embedded_graphics_core::pixelcolor::Rgb565;
use embedded_hal::delay::DelayNs;

use crate::{
    dcs::{
        BitsPerPixel, ExitSleepMode, InterfaceExt, PixelFormat, SetAddressMode, SetDisplayOn,
        SetInvertMode, SetPixelFormat,
    },
    interface::{Interface, InterfaceKind},
    models::{Model, ModelInitError},
    options::ModelOptions,
    ConfigurationError,
};

/// ST7735s display in Rgb565 color mode.
pub struct ST7735s;

impl Model for ST7735s {
    type ColorFormat = Rgb565;
    const FRAMEBUFFER_SIZE: (u16, u16) = (132, 162);

    fn init<DELAY, DI>(
        &mut self,
        di: &mut DI,
        delay: &mut DELAY,
        options: &ModelOptions,
    ) -> Result<SetAddressMode, ModelInitError<DI::Error>>
    where
        DELAY: DelayNs,
        DI: Interface,
    {
        if !matches!(
            DI::KIND,
            InterfaceKind::Serial4Line | InterfaceKind::Parallel8Bit | InterfaceKind::Parallel16Bit
        ) {
            return Err(ModelInitError::InvalidConfiguration(
                ConfigurationError::UnsupportedInterface,
            ));
        }

        let madctl = SetAddressMode::from(options);

        delay.delay_us(200_000);

        di.write_command(ExitSleepMode)?; // turn off sleep
        delay.delay_us(120_000);

        di.write_command(SetInvertMode::new(options.invert_colors))?; // set color inversion
        di.write_raw(0xB1, &[0x05, 0x3A, 0x3A])?; // set frame rate
        di.write_raw(0xB2, &[0x05, 0x3A, 0x3A])?; // set frame rate
        di.write_raw(0xB3, &[0x05, 0x3A, 0x3A, 0x05, 0x3A, 0x3A])?; // set frame rate
        di.write_raw(0xB4, &[0b0000_0011])?; // set inversion control
        di.write_raw(0xC0, &[0x62, 0x02, 0x04])?; // set power control 1
        di.write_raw(0xC1, &[0xC0])?; // set power control 2
        di.write_raw(0xC2, &[0x0D, 0x00])?; // set power control 3
        di.write_raw(0xC3, &[0x8D, 0x6A])?; // set power control 4
        di.write_raw(0xC4, &[0x8D, 0xEE])?; // set power control 5
        di.write_raw(0xC5, &[0x0E])?; // set VCOM control 1
        di.write_raw(
            0xE0,
            &[
                0x10, 0x0E, 0x02, 0x03, 0x0E, 0x07, 0x02, 0x07, 0x0A, 0x12, 0x27, 0x37, 0x00, 0x0D,
                0x0E, 0x10,
            ],
        )?; // set GAMMA +Polarity characteristics
        di.write_raw(
            0xE1,
            &[
                0x10, 0x0E, 0x03, 0x03, 0x0F, 0x06, 0x02, 0x08, 0x0A, 0x13, 0x26, 0x36, 0x00, 0x0D,
                0x0E, 0x10,
            ],
        )?; // set GAMMA -Polarity characteristics

        let pf = PixelFormat::with_all(BitsPerPixel::from_rgb_color::<Self::ColorFormat>());
        di.write_command(SetPixelFormat::new(pf))?; // set interface pixel format, 16bit pixel into frame memory

        di.write_command(madctl)?; // set memory data access control, Top -> Bottom, RGB, Left -> Right
        di.write_command(SetDisplayOn)?; // turn on display

        Ok(madctl)
    }
}
