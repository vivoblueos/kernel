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

/// GC9A01 display in Rgb565 color mode.
pub struct GC9A01;

impl Model for GC9A01 {
    type ColorFormat = Rgb565;
    const FRAMEBUFFER_SIZE: (u16, u16) = (240, 240);

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

        di.write_raw(0xEF, &[])?; // inter register enable 2
        di.write_raw(0xEB, &[0x14])?;
        di.write_raw(0xFE, &[])?; // inter register enable 1
        di.write_raw(0xEF, &[])?; // inter register enable 2
        di.write_raw(0xEB, &[0x14])?;

        di.write_raw(0x84, &[0x40])?;
        di.write_raw(0x85, &[0xFF])?;
        di.write_raw(0x86, &[0xFF])?;
        di.write_raw(0x87, &[0xFF])?;
        di.write_raw(0x88, &[0x0A])?;
        di.write_raw(0x89, &[0x21])?;
        di.write_raw(0x8A, &[0x00])?;
        di.write_raw(0x8B, &[0x80])?;
        di.write_raw(0x8C, &[0x01])?;
        di.write_raw(0x8D, &[0x01])?;
        di.write_raw(0x8E, &[0xFF])?;
        di.write_raw(0x8F, &[0xFF])?;

        di.write_raw(0xB6, &[0x00, 0x20])?; // display function control

        di.write_command(madctl)?; // set memory data access control, Top -> Bottom, RGB, Left -> Right

        let pf = PixelFormat::with_all(BitsPerPixel::from_rgb_color::<Self::ColorFormat>());
        di.write_command(SetPixelFormat::new(pf))?; // set interface pixel format, 16bit pixel into frame memory

        di.write_raw(0x90, &[0x08, 0x08, 0x08, 0x08])?;
        di.write_raw(0xBD, &[0x06])?;
        di.write_raw(0xBC, &[0x00])?;
        di.write_raw(0xFF, &[0x60, 0x01, 0x04])?;

        di.write_raw(0xC3, &[0x13])?; // power control 2
        di.write_raw(0xC4, &[0x13])?; // power control 3
        di.write_raw(0xC9, &[0x22])?; // power control 4

        di.write_raw(0xBE, &[0x11])?;
        di.write_raw(0xE1, &[0x10, 0x0E])?;
        di.write_raw(0xDF, &[0x20, 0x0c, 0x02])?;

        di.write_raw(0xF0, &[0x45, 0x09, 0x08, 0x08, 0x26, 0x2A])?; // gamma 1
        di.write_raw(0xF1, &[0x43, 0x70, 0x72, 0x36, 0x37, 0x6f])?; // gamma 2
        di.write_raw(0xF2, &[0x45, 0x09, 0x08, 0x08, 0x26, 0x2A])?; // gamma 3
        di.write_raw(0xF3, &[0x43, 0x70, 0x72, 0x36, 0x37, 0x6f])?; // gamma 4

        di.write_raw(0xED, &[0x18, 0x0B])?;
        di.write_raw(0xAE, &[0x77])?;
        di.write_raw(0xCD, &[0x63])?;

        di.write_raw(
            0x70,
            &[0x07, 0x07, 0x04, 0x0E, 0x0F, 0x09, 0x07, 0x08, 0x03],
        )?;

        di.write_raw(0xE8, &[0x34])?; // framerate

        di.write_raw(
            0x62,
            &[
                0x18, 0x0D, 0x71, 0xED, 0x70, 0x70, 0x18, 0x0F, 0x71, 0xEF, 0x70, 0x70,
            ],
        )?;
        di.write_raw(
            0x63,
            &[
                0x18, 0x11, 0x71, 0xF1, 0x70, 0x70, 0x18, 0x13, 0x71, 0xF3, 0x70, 0x70,
            ],
        )?;
        di.write_raw(0x64, &[0x28, 0x29, 0xF1, 0x01, 0xF1, 0x00, 0x07])?;
        di.write_raw(
            0x66,
            &[0x3C, 0x00, 0xCD, 0x67, 0x45, 0x45, 0x10, 0x00, 0x00, 0x00],
        )?;
        di.write_raw(
            0x67,
            &[0x00, 0x3C, 0x00, 0x00, 0x00, 0x01, 0x54, 0x10, 0x32, 0x98],
        )?;

        di.write_raw(0x74, &[0x10, 0x85, 0x80, 0x00, 0x00, 0x4E, 0x00])?;
        di.write_raw(0x98, &[0x3e, 0x07])?;

        di.write_command(SetInvertMode::new(options.invert_colors))?; // set color inversion

        di.write_command(ExitSleepMode)?; // turn off sleep
        delay.delay_us(120_000);

        di.write_command(SetDisplayOn)?; // turn on display

        Ok(madctl)
    }
}
