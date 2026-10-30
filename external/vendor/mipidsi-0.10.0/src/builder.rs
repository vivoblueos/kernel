//! [super::Display] builder module

use embedded_hal::{
    delay::DelayNs,
    digital::{self, OutputPin},
};

use crate::{
    dcs::InterfaceExt,
    interface::{Interface, InterfacePixelFormat},
    models::{Model, ModelInitError},
    options::{ColorInversion, ColorOrder, ModelOptions, Orientation, RefreshOrder},
    Display,
};

/// Builder for [Display] instances.
///
/// Exposes all possible display options.
///
/// # Examples
///
/// ```
/// use mipidsi::{Builder, options::ColorOrder, models::ILI9342CRgb565};
///
/// # let di = mipidsi::_mock::MockDisplayInterface;
/// # let rst = mipidsi::_mock::MockOutputPin;
/// # let mut delay = mipidsi::_mock::MockDelay;
/// let mut display = Builder::new(ILI9342CRgb565, di)
///     .reset_pin(rst)
///     .color_order(ColorOrder::Bgr)
///     .display_size(320, 240)
///     .init(&mut delay).unwrap();
/// ```
pub struct Builder<DI, MODEL, RST>
where
    DI: Interface,
    MODEL: Model,
    MODEL::ColorFormat: InterfacePixelFormat<DI::Word>,
{
    di: DI,
    model: MODEL,
    rst: Option<RST>,
    options: ModelOptions,
}

impl<DI, MODEL> Builder<DI, MODEL, NoResetPin>
where
    DI: Interface,
    MODEL: Model,
    MODEL::ColorFormat: InterfacePixelFormat<DI::Word>,
{
    ///
    /// Constructs a new builder for given [Model].
    ///
    #[must_use]
    pub fn new(model: MODEL, di: DI) -> Self {
        Self {
            di,
            model,
            rst: None,
            options: ModelOptions::full_size::<MODEL>(),
        }
    }
}

impl<DI, MODEL, RST> Builder<DI, MODEL, RST>
where
    DI: Interface,
    MODEL: Model,
    MODEL::ColorFormat: InterfacePixelFormat<DI::Word>,
    RST: OutputPin,
{
    ///
    /// Sets the invert color flag
    ///
    #[must_use]
    pub fn invert_colors(mut self, color_inversion: ColorInversion) -> Self {
        self.options.invert_colors = color_inversion;
        self
    }

    ///
    /// Sets the [ColorOrder]
    ///
    #[must_use]
    pub fn color_order(mut self, color_order: ColorOrder) -> Self {
        self.options.color_order = color_order;
        self
    }

    ///
    /// Sets the [Orientation]
    ///
    #[must_use]
    pub fn orientation(mut self, orientation: Orientation) -> Self {
        self.options.orientation = orientation;
        self
    }

    ///
    /// Sets refresh order
    ///
    #[must_use]
    pub fn refresh_order(mut self, refresh_order: RefreshOrder) -> Self {
        self.options.refresh_order = refresh_order;
        self
    }

    /// Sets the display size.
    ///
    ///
    #[must_use]
    pub fn display_size(mut self, width: u16, height: u16) -> Self {
        self.options.display_size = (width, height);
        self
    }

    ///
    /// Sets the display offset
    ///
    #[must_use]
    pub fn display_offset(mut self, x: u16, y: u16) -> Self {
        self.options.display_offset = (x, y);
        self
    }

    /// Sets the reset pin.
    ///
    /// ### WARNING
    /// The reset pin needs to be in *high* state in order for the display to operate.
    /// If it wasn't provided the user needs to ensure this is the case.
    ///
    #[must_use]
    pub fn reset_pin<RST2: OutputPin>(self, rst: RST2) -> Builder<DI, MODEL, RST2> {
        Builder {
            di: self.di,
            model: self.model,
            rst: Some(rst),
            options: self.options,
        }
    }

    ///
    /// Consumes the builder to create a new [Display] with an optional reset [OutputPin].
    /// Blocks using the provided [DelayNs] `delay_source` to perform the display initialization.
    /// The display will be awake ready to use, no need to call [Display::wake] after init.
    ///
    /// Returns [InitError] if the area defined by the [`display_size`](Self::display_size)
    /// and [`display_offset`](Self::display_offset) settings is (partially) outside the framebuffer.
    pub fn init(
        mut self,
        delay_source: &mut impl DelayNs,
    ) -> Result<Display<DI, MODEL, RST>, InitError<DI::Error, RST::Error>> {
        let to_u32 = |(a, b)| (u32::from(a), u32::from(b));
        let (width, height) = to_u32(self.options.display_size);
        let (offset_x, offset_y) = to_u32(self.options.display_offset);
        let (max_width, max_height) = to_u32(MODEL::FRAMEBUFFER_SIZE);

        if width == 0 || height == 0 || width > max_width || height > max_height {
            return Err(InitError::InvalidConfiguration(
                ConfigurationError::InvalidDisplaySize,
            ));
        }

        if width + offset_x > max_width {
            return Err(InitError::InvalidConfiguration(
                ConfigurationError::InvalidDisplayOffset,
            ));
        }

        if height + offset_y > max_height {
            return Err(InitError::InvalidConfiguration(
                ConfigurationError::InvalidDisplayOffset,
            ));
        }

        match self.rst {
            Some(ref mut rst) => {
                rst.set_low().map_err(InitError::ResetPin)?;
                delay_source.delay_us(MODEL::RESET_DURATION);
                rst.set_high().map_err(InitError::ResetPin)?;
            }
            None => self
                .di
                .write_command(crate::dcs::SoftReset)
                .map_err(InitError::Interface)?,
        }

        let madctl = self.model.init(&mut self.di, delay_source, &self.options)?;

        let display = Display {
            di: self.di,
            model: self.model,
            rst: self.rst,
            options: self.options,
            madctl,
            sleeping: false, // TODO: init should lock state
        };

        Ok(display)
    }
}

/// Error returned by [`Builder::init`].
#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum InitError<DI, P> {
    /// Error caused by the display interface.
    Interface(DI),

    /// Error caused by the reset pin's [`OutputPin`](embedded_hal::digital::OutputPin) implementation.
    ResetPin(P),

    /// Invalid configuration error.
    ///
    /// This error is returned when the configuration passed to the builder is
    /// invalid. For example, when the combination of bit depth and interface
    /// kind isn't supported by the selected model.
    InvalidConfiguration(ConfigurationError),
}

/// Specifics of [InitError::InvalidConfiguration] if configuration was found invalid
#[non_exhaustive]
#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum ConfigurationError {
    /// Unsupported interface kind.
    ///
    /// The chosen interface isn't supported by the selected model. Note that
    /// some controller models don't support all combinations of physical
    /// interface and color formats. To resolve this, try to use another color
    /// format if available (e.g. [`ILI9486Rgb666`](crate::models::ILI9486Rgb666) instead of
    /// [`ILI9486Rgb565`](crate::models::ILI9486Rgb565) if you use a SPI connection)
    UnsupportedInterface,
    /// Invalid display size
    ///
    /// Display dimensions provided in [Builder::display_size] were invalid, e.g. width or height of 0
    InvalidDisplaySize,
    /// Invalid display offset.
    ///
    /// The active display area, defined by [`display_size`](Builder::display_size) and
    /// [`display_offset`](Builder::display_offset), extends beyond the boundaries of
    /// the controller's framebuffer. To resolve this, reduce the offset to a maximum value of
    /// [`FRAMEBUFFER_SIZE`](Model::FRAMEBUFFER_SIZE) minus [`display_size`](Builder::display_size).
    InvalidDisplayOffset,
}

impl<DiError, P> From<ModelInitError<DiError>> for InitError<DiError, P> {
    fn from(value: ModelInitError<DiError>) -> Self {
        match value {
            ModelInitError::Interface(e) => Self::Interface(e),
            ModelInitError::InvalidConfiguration(ce) => Self::InvalidConfiguration(ce),
        }
    }
}

/// Marker type for no reset pin.
pub enum NoResetPin {}

impl digital::OutputPin for NoResetPin {
    fn set_low(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn set_high(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
}

impl digital::ErrorType for NoResetPin {
    type Error = core::convert::Infallible;
}

#[cfg(test)]
mod tests {
    use crate::{
        _mock::{MockDelay, MockDisplayInterface, MockOutputPin},
        models::ILI9341Rgb565,
    };

    use super::*;

    #[test]
    fn init_without_reset_pin() {
        let _: Display<_, _, NoResetPin> = Builder::new(ILI9341Rgb565, MockDisplayInterface)
            .init(&mut MockDelay)
            .unwrap();
    }

    #[test]
    fn init_reset_pin() {
        let _: Display<_, _, MockOutputPin> = Builder::new(ILI9341Rgb565, MockDisplayInterface)
            .reset_pin(MockOutputPin)
            .init(&mut MockDelay)
            .unwrap();
    }

    #[test]
    fn error_too_wide() {
        assert!(matches!(
            Builder::new(ILI9341Rgb565, MockDisplayInterface)
                .reset_pin(MockOutputPin)
                .display_size(241, 320)
                .init(&mut MockDelay),
            Err(InitError::InvalidConfiguration(
                ConfigurationError::InvalidDisplaySize
            ))
        ))
    }

    #[test]
    fn error_too_tall() {
        assert!(matches!(
            Builder::new(ILI9341Rgb565, MockDisplayInterface)
                .reset_pin(MockOutputPin)
                .display_size(240, 321)
                .init(&mut MockDelay),
            Err(InitError::InvalidConfiguration(
                ConfigurationError::InvalidDisplaySize
            )),
        ))
    }

    #[test]
    fn error_offset_invalid_x() {
        assert!(matches!(
            Builder::new(ILI9341Rgb565, MockDisplayInterface)
                .reset_pin(MockOutputPin)
                .display_size(240, 320)
                .display_offset(1, 0)
                .init(&mut MockDelay),
            Err(InitError::InvalidConfiguration(
                ConfigurationError::InvalidDisplayOffset
            )),
        ))
    }

    #[test]
    fn error_offset_invalid_y() {
        assert!(matches!(
            Builder::new(ILI9341Rgb565, MockDisplayInterface)
                .reset_pin(MockOutputPin)
                .display_size(240, 310)
                .display_offset(0, 11)
                .init(&mut MockDelay),
            Err(InitError::InvalidConfiguration(
                ConfigurationError::InvalidDisplayOffset
            )),
        ))
    }

    #[test]
    fn error_zero_size() {
        assert!(matches!(
            Builder::new(ILI9341Rgb565, MockDisplayInterface)
                .reset_pin(MockOutputPin)
                .display_size(0, 0)
                .init(&mut MockDelay),
            Err(InitError::InvalidConfiguration(
                ConfigurationError::InvalidDisplaySize
            )),
        ))
    }
}
