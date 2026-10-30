//! # Troubleshooting guide
//!
//! This guide lists common issues that can cause a blank or corrupted display.
//!
//! ## Display stays black/blank
//!
//! ### Reset pin
//!
//! The reset pin on all supported display controllers is active low, requiring
//! it to be driven **high** in order for the display to operate. It is
//! recommended to connect the reset pin to a GPIO pin and let this crate
//! control the pin by passing it to the builder via the `reset_pin` method. If
//! this isn't possible in the target application the user must make sure that
//! the reset pin on the display controller is kept in the high state before
//! `init` is called.
//!
//! ### Backlight pin
//!
//! This driver does **NOT** handle the backlight pin to keep the code simpler.
//! Users must control the backlight manually. First thing to try is to see if
//! setting the backlight pin to high fixes the issue.
//!
//! ### Transport misconfiguration (e.g. SPI)
//!
//! Make sure that the transport layer is configured correctly. Typical mistakes
//! are the use of wrong SPI MODE or too fast transfer speeds that are not
//! supported by the display
//!
//! ## Incorrect colors
//!
//! The way colors are displayed depend on the subpixel layout and technology
//! (like TN or IPS) used by the LCD panel. These physical parameters aren't
//! known by the display controller and must be manually set by the user as
//! `Builder` settings when the display is initialized.
//!
//! To make it easier to identify the correct settings the `mipidsi` crate
//! provides a [`TestImage`](crate::TestImage), which can be used to verify the
//! color settings and adjust them in case they are incorrect.
//!
//! ```
//! use embedded_graphics::prelude::*;
//! use mipidsi::{Builder, TestImage, models::ILI9486Rgb666};
//!
//! # let di = mipidsi::_mock::MockDisplayInterface;
//! # let rst = mipidsi::_mock::MockOutputPin;
//! # let mut delay = mipidsi::_mock::MockDelay;
//! let mut display = Builder::new(ILI9486Rgb666, di)
//!     .reset_pin(rst)
//!     .init(&mut delay)
//!     .unwrap();;
//!
//! TestImage::new().draw(&mut display)?;
//! # Ok::<(), core::convert::Infallible>(())
//! ```
//!
//! The expected output from drawing the test image is:
//!
#![doc = include_str!("../docs/colors_correct.svg")]
//!
//! If the test image isn't displayed as expected use one of the reference image
//! below the determine which settings need to be added to the
//! [`Builder`](crate::Builder).
//!
//! ### Wrong subpixel order
//!
#![doc = include_str!("../docs/colors_wrong_subpixel_order.svg")]
//!
//! ```
//! # use embedded_graphics::prelude::*;
//! # use mipidsi::{Builder, TestImage, models::ILI9486Rgb666};
//! #
//! # let di = mipidsi::_mock::MockDisplayInterface;
//! # let mut delay = mipidsi::_mock::MockDelay;
//! # let mut display = Builder::new(ILI9486Rgb666, di)
//! .color_order(mipidsi::options::ColorOrder::Bgr)
//! # .init(&mut delay).unwrap();
//! ```
//!
//! ### Wrong color inversion
//!
#![doc = include_str!("../docs/colors_wrong_color_inversion.svg")]
//!
//! ```
//! # use embedded_graphics::prelude::*;
//! # use mipidsi::{Builder, TestImage, models::ILI9486Rgb666};
//! #
//! # let di = mipidsi::_mock::MockDisplayInterface;
//! # let mut delay = mipidsi::_mock::MockDelay;
//! # let mut display = Builder::new(ILI9486Rgb666, di)
//! .invert_colors(mipidsi::options::ColorInversion::Inverted)
//! # .init(&mut delay).unwrap();
//! ```
//!
//! ### Wrong subpixel order and color inversion
//!
#![doc = include_str!("../docs/colors_both_wrong.svg")]
//!
//! ```
//! # use embedded_graphics::prelude::*;
//! # use mipidsi::{Builder, TestImage, models::ILI9486Rgb666};
//! #
//! # let di = mipidsi::_mock::MockDisplayInterface;
//! # let mut delay = mipidsi::_mock::MockDelay;
//! # let mut display = Builder::new(ILI9486Rgb666, di)
//! .color_order(mipidsi::options::ColorOrder::Bgr)
//! .invert_colors(mipidsi::options::ColorInversion::Inverted)
//! # .init(&mut delay).unwrap();
//! ```
