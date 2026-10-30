use embedded_hal::delay::DelayNs;

use crate::{
    dcs::{
        EnterNormalMode, ExitSleepMode, InterfaceExt, PixelFormat, SetAddressMode, SetDisplayOn,
        SetInvertMode, SetPixelFormat,
    },
    interface::Interface,
    models::ModelInitError,
    options::ModelOptions,
};

/// Common init for all ILI948x models and color formats.
pub fn init_common<DELAY, DI>(
    di: &mut DI,
    delay: &mut DELAY,
    options: &ModelOptions,
    pixel_format: PixelFormat,
) -> Result<SetAddressMode, ModelInitError<DI::Error>>
where
    DELAY: DelayNs,
    DI: Interface,
{
    let madctl = SetAddressMode::from(options);
    di.write_command(ExitSleepMode)?; // turn off sleep
    di.write_command(SetPixelFormat::new(pixel_format))?; // pixel format
    di.write_command(madctl)?; // left -> right, bottom -> top RGB
                               // dcs.write_command(Instruction::VCMOFSET, &[0x00, 0x48, 0x00, 0x48])?; //VCOM  Control 1 [00 40 00 40]
                               // dcs.write_command(Instruction::INVCO, &[0x0])?; //Inversion Control [00]
    di.write_command(SetInvertMode::new(options.invert_colors))?;

    // optional gamma setup
    // dcs.write_raw(Instruction::PGC, &[0x00, 0x2C, 0x2C, 0x0B, 0x0C, 0x04, 0x4C, 0x64, 0x36, 0x03, 0x0E, 0x01, 0x10, 0x01, 0x00])?; // Positive Gamma Control
    // dcs.write_raw(Instruction::NGC, &[0x0F, 0x37, 0x37, 0x0C, 0x0F, 0x05, 0x50, 0x32, 0x36, 0x04, 0x0B, 0x00, 0x19, 0x14, 0x0F])?; // Negative Gamma Control

    di.write_raw(0xB6, &[0b0000_0010, 0x02, 0x3B])?; // DFC
    di.write_command(EnterNormalMode)?; // turn to normal mode
    di.write_command(SetDisplayOn)?; // turn on display

    // DISPON requires some time otherwise we risk SPI data issues
    delay.delay_us(120_000);

    Ok(madctl)
}
