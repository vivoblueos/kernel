use embedded_graphics_core::pixelcolor::Rgb565;
use embedded_hal::delay::DelayNs;

use crate::{
    dcs::SetAddressMode,
    interface::{Interface, InterfaceKind},
    models::{Model, ModelInitError},
    options::ModelOptions,
    ConfigurationError,
};

/// ST7796 display in Rgb565 color mode.
pub struct ST7796;

impl Model for ST7796 {
    type ColorFormat = Rgb565;
    const FRAMEBUFFER_SIZE: (u16, u16) = (320, 480);

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

        super::ST7789.init(di, delay, options)
    }
}
