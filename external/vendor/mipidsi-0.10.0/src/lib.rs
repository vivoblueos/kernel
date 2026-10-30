#![no_std]
// associated re-typing not supported in rust yet
#![allow(clippy::type_complexity)]
#![warn(missing_docs)]

//! This crate provides a generic display driver to connect to TFT displays
//! that implement the [MIPI Display Command Set](https://www.mipi.org/specifications/display-command-set).
//!
//! Uses implementations of the [interface::Interface] trait to talk to the
//! hardware via different transports. Builtin support for these transports is
//! available:
//! - SPI ([`interface::SpiInterface`])
//! - 8080 style parallel via GPIO ([`interface::ParallelInterface`])
//!
//! An optional batching of draws is supported via the `batch` feature (default on)
//!
//! ### List of supported models
//!
//! * GC9107
//! * GC9A01
//! * ILI9225
//! * ILI9341
//! * ILI9342C
//! * ILI9486
//! * ILI9488
//! * RM67162
//! * ST7735
//! * ST7789
//! * ST7796
//!
//! ## Troubleshooting
//!
//! Refer to the [troubleshooting guide](_troubleshooting)
//! if you experience problems like a blank screen or incorrect colors.
//!
//! ## Examples
//!
//! **For the ili9486 display, using the SPI interface with no chip select:**
//! ```
//! use mipidsi::interface::SpiInterface;                    // Provides the builder for DisplayInterface
//! use mipidsi::{Builder, models::ILI9486Rgb666};           // Provides the builder for Display
//! use embedded_graphics::{prelude::*, pixelcolor::Rgb666}; // Provides the required color type
//!
//! /* Define the SPI interface as the variable `spi` */
//! /* Define the DC digital output pin as the variable `dc` */
//! /* Define the Reset digital output pin as the variable `rst` */
//!# let spi = mipidsi::_mock::MockSpi;
//!# let dc = mipidsi::_mock::MockOutputPin;
//!# let rst = mipidsi::_mock::MockOutputPin;
//!# let mut delay = mipidsi::_mock::MockDelay;
//!
//! // Create a buffer
//! let mut buffer = [0_u8; 512];
//!
//! // Create a DisplayInterface from SPI and DC pin, with no manual CS control
//! let di = SpiInterface::new(spi, dc, &mut buffer);
//!
//! // Create the ILI9486 display driver from the display interface and optional RST pin
//! let mut display = Builder::new(ILI9486Rgb666, di)
//!     .reset_pin(rst)
//!     .init(&mut delay).unwrap();
//!
//! // Clear the display to black
//! display.clear(Rgb666::BLACK).unwrap();
//! ```
//!
//! **For the ili9341 display, using the Parallel port, with the RGB666 color space and the Bgr
//! color order:**
//! ```
//! // Provides the builder for DisplayInterface
//! use mipidsi::interface::{Generic8BitBus, ParallelInterface};
//! // Provides the builder for Display
//! use mipidsi::{Builder, models::ILI9341Rgb666};
//! // Provides the required color type
//! use embedded_graphics::{prelude::*, pixelcolor::Rgb666};
//!
//! /* Define digital output pins d0 - d7 for the parallel port as `lcd_dX` */
//! /* Define the D/C digital output pin as `dc` */
//! /* Define the WR and Reset digital output pins with the initial state set as High as `wr` and
//! `rst` */
//!# let lcd_d0 = mipidsi::_mock::MockOutputPin;
//!# let lcd_d1 = mipidsi::_mock::MockOutputPin;
//!# let lcd_d2 = mipidsi::_mock::MockOutputPin;
//!# let lcd_d3 = mipidsi::_mock::MockOutputPin;
//!# let lcd_d4 = mipidsi::_mock::MockOutputPin;
//!# let lcd_d5 = mipidsi::_mock::MockOutputPin;
//!# let lcd_d6 = mipidsi::_mock::MockOutputPin;
//!# let lcd_d7 = mipidsi::_mock::MockOutputPin;
//!# let wr = mipidsi::_mock::MockOutputPin;
//!# let dc = mipidsi::_mock::MockOutputPin;
//!# let rst = mipidsi::_mock::MockOutputPin;
//!# let mut delay = mipidsi::_mock::MockDelay;
//!
//! // Create the DisplayInterface from a Generic8BitBus, which is made from the parallel pins
//! let bus = Generic8BitBus::new((lcd_d0, lcd_d1, lcd_d2,
//!     lcd_d3, lcd_d4, lcd_d5, lcd_d6, lcd_d7));
//! let di = ParallelInterface::new(bus, dc, wr);
//!
//! // Create the ILI9341 display driver from the display interface with the RGB666 color space
//! let mut display = Builder::new(ILI9341Rgb666, di)
//!      .reset_pin(rst)
//!      .color_order(mipidsi::options::ColorOrder::Bgr)
//!      .init(&mut delay).unwrap();
//!
//! // Clear the display to black
//! display.clear(Rgb666::RED).unwrap();
//! ```

use dcs::SetAddressMode;

pub mod interface;

use embedded_hal::delay::DelayNs;
use embedded_hal::digital::OutputPin;

pub mod options;
use interface::InterfacePixelFormat;
use options::MemoryMapping;

mod builder;
pub use builder::*;

pub mod dcs;

pub mod models;
use models::Model;

mod graphics;

mod test_image;
pub use test_image::TestImage;

#[cfg(feature = "batch")]
mod batch;

pub mod _troubleshooting;

///
/// Display driver to connect to TFT displays.
///
pub struct Display<DI, MODEL, RST>
where
    DI: interface::Interface,
    MODEL: Model,
    MODEL::ColorFormat: InterfacePixelFormat<DI::Word>,
    RST: OutputPin,
{
    // DCS provider
    di: DI,
    // Model
    model: MODEL,
    // Reset pin
    rst: Option<RST>,
    // Model Options, includes current orientation
    options: options::ModelOptions,
    // Current MADCTL value copy for runtime updates
    madctl: SetAddressMode,
    // State monitor for sleeping TODO: refactor to a Model-connected state machine
    sleeping: bool,
}

impl<DI, M, RST> Display<DI, M, RST>
where
    DI: interface::Interface,
    M: Model,
    M::ColorFormat: InterfacePixelFormat<DI::Word>,
    RST: OutputPin,
{
    ///
    /// Returns currently set [options::Orientation]
    ///
    pub fn orientation(&self) -> options::Orientation {
        self.options.orientation
    }

    ///
    /// Sets display [options::Orientation] with mirror image parameter
    ///
    /// # Examples
    ///
    /// ```
    /// use mipidsi::options::{Orientation, Rotation};
    ///
    /// # let mut display = mipidsi::_mock::new_mock_display();
    /// display.set_orientation(Orientation::default().rotate(Rotation::Deg180)).unwrap();
    /// ```
    pub fn set_orientation(&mut self, orientation: options::Orientation) -> Result<(), DI::Error> {
        self.options.orientation = orientation;
        self.model.update_options(&mut self.di, &self.options)
    }

    ///
    /// Sets a pixel color at the given coords.
    ///
    /// # Arguments
    ///
    /// * `x` - x coordinate
    /// * `y` - y coordinate
    /// * `color` - the color value in pixel format of the display [Model]
    ///
    /// # Examples
    ///
    /// ```
    /// use embedded_graphics::pixelcolor::Rgb565;
    ///
    /// # let mut display = mipidsi::_mock::new_mock_display();
    /// display.set_pixel(100, 200, Rgb565::new(251, 188, 20)).unwrap();
    /// ```
    pub fn set_pixel(&mut self, x: u16, y: u16, color: M::ColorFormat) -> Result<(), DI::Error> {
        self.set_pixels(x, y, x, y, core::iter::once(color))
    }

    ///
    /// Sets pixel colors in a rectangular region.
    ///
    /// The color values from the `colors` iterator will be drawn to the given region starting
    /// at the top left corner and continuing, row first, to the bottom right corner. No bounds
    /// checking is performed on the `colors` iterator and drawing will wrap around if the
    /// iterator returns more color values than the number of pixels in the given region.
    ///
    /// This is a low level function, which isn't intended to be used in regular user code.
    /// Consider using the [`fill_contiguous`](https://docs.rs/embedded-graphics/latest/embedded_graphics/draw_target/trait.DrawTarget.html#method.fill_contiguous)
    /// function from the `embedded-graphics` crate as an alternative instead.
    ///
    /// # Arguments
    ///
    /// * `sx` - x coordinate start
    /// * `sy` - y coordinate start
    /// * `ex` - x coordinate end
    /// * `ey` - y coordinate end
    /// * `colors` - anything that can provide `IntoIterator<Item = u16>` to iterate over pixel data
    /// <div class="warning">
    ///
    /// The end values of the X and Y coordinate ranges are inclusive, and no
    /// bounds checking is performed on these values. Using out of range values
    /// (e.g., passing `320` instead of `319` for a 320 pixel wide display) will
    /// result in undefined behavior.
    ///
    /// </div>
    pub fn set_pixels<T>(
        &mut self,
        sx: u16,
        sy: u16,
        ex: u16,
        ey: u16,
        colors: T,
    ) -> Result<(), DI::Error>
    where
        T: IntoIterator<Item = M::ColorFormat>,
    {
        self.set_address_window(sx, sy, ex, ey)?;

        M::write_memory_start(&mut self.di)?;

        M::ColorFormat::send_pixels(&mut self.di, colors)
    }

    /// Sets the vertical scroll region.
    ///
    /// The `top_fixed_area` and `bottom_fixed_area` arguments can be used to
    /// define an area on the top and/or bottom of the display which won't be
    /// affected by scrolling.
    ///
    /// Note that this method is not affected by the current display orientation
    /// and will always scroll vertically relative to the default display
    /// orientation.
    ///
    /// The combined height of the fixed area must not larger than the
    /// height of the framebuffer height in the default orientation.
    ///
    /// After the scrolling region is defined the [`set_vertical_scroll_offset`](Self::set_vertical_scroll_offset) can be
    /// used to scroll the display.
    pub fn set_vertical_scroll_region(
        &mut self,
        top_fixed_area: u16,
        bottom_fixed_area: u16,
    ) -> Result<(), DI::Error> {
        M::set_vertical_scroll_region(&mut self.di, top_fixed_area, bottom_fixed_area)
    }

    /// Sets the vertical scroll offset.
    ///
    /// Setting the vertical scroll offset shifts the vertical scroll region
    /// upwards by `offset` pixels.
    ///
    /// Use [`set_vertical_scroll_region`](Self::set_vertical_scroll_region) to setup the scroll region, before
    /// using this method.
    pub fn set_vertical_scroll_offset(&mut self, offset: u16) -> Result<(), DI::Error> {
        M::set_vertical_scroll_offset(&mut self.di, offset)
    }

    ///
    /// Release resources allocated to this driver back.
    /// This returns the display interface, reset pin and and the model deconstructing the driver.
    ///
    pub fn release(self) -> (DI, M, Option<RST>) {
        (self.di, self.model, self.rst)
    }

    // Sets the address window for the display.
    fn set_address_window(&mut self, sx: u16, sy: u16, ex: u16, ey: u16) -> Result<(), DI::Error> {
        // add clipping offsets if present
        let mut offset = self.options.display_offset;
        let mapping = MemoryMapping::from(self.options.orientation);
        if mapping.reverse_columns {
            offset.0 = M::FRAMEBUFFER_SIZE.0 - (self.options.display_size.0 + offset.0);
        }
        if mapping.reverse_rows {
            offset.1 = M::FRAMEBUFFER_SIZE.1 - (self.options.display_size.1 + offset.1);
        }
        if mapping.swap_rows_and_columns {
            offset = (offset.1, offset.0);
        }

        let (sx, sy, ex, ey) = (sx + offset.0, sy + offset.1, ex + offset.0, ey + offset.1);

        M::update_address_window(
            &mut self.di,
            self.options.orientation.rotation,
            sx,
            sy,
            ex,
            ey,
        )
    }

    ///
    /// Configures the tearing effect output.
    ///
    pub fn set_tearing_effect(
        &mut self,
        tearing_effect: options::TearingEffect,
    ) -> Result<(), DI::Error> {
        M::set_tearing_effect(&mut self.di, tearing_effect, &self.options)
    }

    ///
    /// Returns `true` if display is currently set to sleep.
    ///
    pub fn is_sleeping(&self) -> bool {
        self.sleeping
    }

    ///
    /// Puts the display to sleep, reducing power consumption.
    /// Need to call [Self::wake] before issuing other commands
    ///
    pub fn sleep<D: DelayNs>(&mut self, delay: &mut D) -> Result<(), DI::Error> {
        M::sleep(&mut self.di, delay)?;
        self.sleeping = true;
        Ok(())
    }

    ///
    /// Wakes the display after it's been set to sleep via [Self::sleep]
    ///
    pub fn wake<D: DelayNs>(&mut self, delay: &mut D) -> Result<(), DI::Error> {
        M::wake(&mut self.di, delay)?;
        self.sleeping = false;
        Ok(())
    }

    /// Returns the DCS interface for sending raw commands.
    ///
    /// # Safety
    ///
    /// Sending raw commands to the controller can lead to undefined behaviour,
    /// because the rest of the code isn't aware of any state changes that were caused by sending raw commands.
    /// The user must ensure that the state of the controller isn't altered in a way that interferes with the normal
    /// operation of this crate.
    pub unsafe fn dcs(&mut self) -> &mut DI {
        &mut self.di
    }
}

/// Mock implementations of embedded-hal and interface traits.
///
/// Do not use types in this module outside of doc tests.
#[doc(hidden)]
pub mod _mock {
    use core::convert::Infallible;

    use embedded_hal::{delay::DelayNs, digital, spi};

    use crate::{
        interface::{Interface, InterfaceKind},
        models::ILI9341Rgb565,
        Builder, Display, NoResetPin,
    };

    pub fn new_mock_display() -> Display<MockDisplayInterface, ILI9341Rgb565, NoResetPin> {
        Builder::new(ILI9341Rgb565, MockDisplayInterface)
            .init(&mut MockDelay)
            .unwrap()
    }

    pub struct MockOutputPin;

    impl digital::OutputPin for MockOutputPin {
        fn set_low(&mut self) -> Result<(), Self::Error> {
            Ok(())
        }

        fn set_high(&mut self) -> Result<(), Self::Error> {
            Ok(())
        }
    }

    impl digital::ErrorType for MockOutputPin {
        type Error = core::convert::Infallible;
    }

    pub struct MockSpi;

    impl spi::SpiDevice for MockSpi {
        fn transaction(
            &mut self,
            _operations: &mut [spi::Operation<'_, u8>],
        ) -> Result<(), Self::Error> {
            Ok(())
        }
    }

    impl spi::ErrorType for MockSpi {
        type Error = core::convert::Infallible;
    }

    pub struct MockDelay;

    impl DelayNs for MockDelay {
        fn delay_ns(&mut self, _ns: u32) {}
    }

    pub struct MockDisplayInterface;

    impl Interface for MockDisplayInterface {
        type Word = u8;
        type Error = Infallible;

        const KIND: InterfaceKind = InterfaceKind::Serial4Line;

        fn send_command(&mut self, _command: u8, _args: &[u8]) -> Result<(), Self::Error> {
            Ok(())
        }

        fn send_pixels<const N: usize>(
            &mut self,
            _pixels: impl IntoIterator<Item = [Self::Word; N]>,
        ) -> Result<(), Self::Error> {
            Ok(())
        }

        fn send_repeated_pixel<const N: usize>(
            &mut self,
            _pixel: [Self::Word; N],
            _count: u32,
        ) -> Result<(), Self::Error> {
            Ok(())
        }
    }
}
