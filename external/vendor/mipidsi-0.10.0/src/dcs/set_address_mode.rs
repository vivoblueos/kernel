//! Module for the MADCTL instruction constructors

use crate::options::{
    ColorOrder, HorizontalRefreshOrder, MemoryMapping, ModelOptions, Orientation, RefreshOrder,
    VerticalRefreshOrder,
};

use super::DcsCommand;

/// Set Address Mode
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct SetAddressMode(u8);

impl SetAddressMode {
    /// Creates a new Set Address Mode command.
    pub const fn new(
        color_order: ColorOrder,
        orientation: Orientation,
        refresh_order: RefreshOrder,
    ) -> Self {
        Self(0)
            .with_color_order(color_order)
            .with_orientation(orientation)
            .with_refresh_order(refresh_order)
    }

    /// Returns this Madctl with [ColorOrder] set to new value
    #[must_use]
    pub const fn with_color_order(self, color_order: ColorOrder) -> Self {
        let mut result = self;
        match color_order {
            ColorOrder::Rgb => result.0 &= 0b1111_0111,
            ColorOrder::Bgr => result.0 |= 0b0000_1000,
        }

        result
    }

    /// Returns this Madctl with [Orientation] set to new value
    #[must_use]
    pub const fn with_orientation(self, orientation: Orientation) -> Self {
        let mut result = self.0;
        result &= 0b0001_1111;

        let mapping = MemoryMapping::from_orientation(orientation);
        if mapping.reverse_rows {
            result |= 1 << 7;
        }
        if mapping.reverse_columns {
            result |= 1 << 6;
        }
        if mapping.swap_rows_and_columns {
            result |= 1 << 5;
        }

        Self(result)
    }

    /// Returns this Madctl with [RefreshOrder] set to new value
    #[must_use]
    pub const fn with_refresh_order(self, refresh_order: RefreshOrder) -> Self {
        let mut result = self;
        let value = match (refresh_order.vertical, refresh_order.horizontal) {
            (VerticalRefreshOrder::TopToBottom, HorizontalRefreshOrder::LeftToRight) => 0b0000_0000,
            (VerticalRefreshOrder::TopToBottom, HorizontalRefreshOrder::RightToLeft) => 0b0000_0100,
            (VerticalRefreshOrder::BottomToTop, HorizontalRefreshOrder::LeftToRight) => 0b0001_0000,
            (VerticalRefreshOrder::BottomToTop, HorizontalRefreshOrder::RightToLeft) => 0b0001_0100,
        };

        result.0 = (result.0 & 0b1110_1011) | value;

        result
    }
}

impl DcsCommand for SetAddressMode {
    fn instruction(&self) -> u8 {
        0x36
    }

    fn fill_params_buf(&self, buffer: &mut [u8]) -> usize {
        buffer[0] = self.0;
        1
    }
}

impl From<&ModelOptions> for SetAddressMode {
    fn from(options: &ModelOptions) -> Self {
        Self::default()
            .with_color_order(options.color_order)
            .with_orientation(options.orientation)
            .with_refresh_order(options.refresh_order)
    }
}

#[cfg(test)]
mod tests {
    use crate::options::Rotation;

    use super::*;

    #[test]
    fn madctl_bit_operations() {
        let madctl = SetAddressMode::default()
            .with_color_order(ColorOrder::Bgr)
            .with_refresh_order(RefreshOrder::new(
                VerticalRefreshOrder::BottomToTop,
                HorizontalRefreshOrder::RightToLeft,
            ))
            .with_orientation(Orientation::default().rotate(Rotation::Deg270));

        let mut bytes = [0u8];
        assert_eq!(madctl.fill_params_buf(&mut bytes), 1);
        assert_eq!(bytes, [0b1011_1100u8]);

        let madctl = madctl.with_orientation(Orientation::default());
        assert_eq!(madctl.fill_params_buf(&mut bytes), 1);
        assert_eq!(bytes, [0b0001_1100u8]);

        let madctl = madctl.with_color_order(ColorOrder::Rgb);
        assert_eq!(madctl.fill_params_buf(&mut bytes), 1);
        assert_eq!(bytes, [0b0001_0100u8]);

        let madctl = madctl.with_refresh_order(RefreshOrder::default());
        assert_eq!(madctl.fill_params_buf(&mut bytes), 1);
        assert_eq!(bytes, [0b0000_0000u8]);
    }
}
