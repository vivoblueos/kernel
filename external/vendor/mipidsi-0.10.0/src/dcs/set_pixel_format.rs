//! Module for the COLMOD instruction constructors

use super::DcsCommand;

/// Set Pixel Format
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct SetPixelFormat(PixelFormat);

impl SetPixelFormat {
    /// Creates a new Set Pixel Format command.
    pub const fn new(pixel_format: PixelFormat) -> Self {
        Self(pixel_format)
    }
}

impl DcsCommand for SetPixelFormat {
    fn instruction(&self) -> u8 {
        0x3A
    }

    fn fill_params_buf(&self, buffer: &mut [u8]) -> usize {
        buffer[0] = self.0.as_u8();
        1
    }
}

///
/// Bits per pixel for DBI and DPI fields of [PixelFormat]
///
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[repr(u8)]
pub enum BitsPerPixel {
    /// 3 bits per pixel.
    Three = 0b001,
    /// 8 bits per pixel.
    Eight = 0b010,
    /// 12 bits per pixel.
    Twelve = 0b011,
    /// 16 bits per pixel.
    Sixteen = 0b101,
    /// 18 bits per pixel.
    Eighteen = 0b110,
    /// 24 bits per pixel.
    TwentyFour = 0b111,
}

///
/// Defines pixel format as combination of DPI and DBI
///
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct PixelFormat {
    dpi: BitsPerPixel,
    dbi: BitsPerPixel,
}

impl PixelFormat {
    ///
    /// Construct a new [PixelFormat] with given [BitsPerPixel] values
    /// for DPI and DBI fields
    ///
    pub const fn new(dpi: BitsPerPixel, dbi: BitsPerPixel) -> Self {
        Self { dpi, dbi }
    }

    ///
    /// Construct a new [PixelFormat] with same [BitsPerPixel] value
    /// for both DPI and DBI fields
    ///
    pub const fn with_all(bpp: BitsPerPixel) -> Self {
        Self { dpi: bpp, dbi: bpp }
    }

    ///
    /// Returns the corresponding u8 containing both DPI and DBI bits
    ///
    pub fn as_u8(&self) -> u8 {
        (self.dpi as u8) << 4 | (self.dbi as u8)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn colmod_rgb565_is_16bit() {
        let colmod = SetPixelFormat::new(PixelFormat::new(
            BitsPerPixel::Sixteen,
            BitsPerPixel::Sixteen,
        ));

        let mut bytes = [0u8];
        assert_eq!(colmod.fill_params_buf(&mut bytes), 1);
        assert_eq!(bytes, [0b0101_0101u8]);
    }

    #[test]
    fn colmod_rgb666_is_18bit() {
        let colmod = SetPixelFormat::new(PixelFormat::new(
            BitsPerPixel::Eighteen,
            BitsPerPixel::Eighteen,
        ));

        let mut bytes = [0u8];
        assert_eq!(colmod.fill_params_buf(&mut bytes), 1);
        assert_eq!(bytes, [0b0110_0110u8]);
    }

    #[test]
    fn colmod_rgb888_is_24bit() {
        let colmod = SetPixelFormat::new(PixelFormat::new(
            BitsPerPixel::Eighteen,
            BitsPerPixel::TwentyFour,
        ));

        let mut bytes = [0u8];
        assert_eq!(colmod.fill_params_buf(&mut bytes), 1);
        assert_eq!(bytes, [0b0110_0111u8]);
    }

    #[test]
    fn test_pixel_format_as_u8() {
        let pf = PixelFormat::new(BitsPerPixel::Sixteen, BitsPerPixel::TwentyFour);
        assert_eq!(pf.as_u8(), 0b0101_0111);
    }
}
