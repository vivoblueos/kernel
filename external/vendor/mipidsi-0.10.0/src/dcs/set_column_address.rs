//! Module for the CASET address window instruction constructors

use super::DcsCommand;

/// Set Column Address
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct SetColumnAddress {
    start_column: u16,
    end_column: u16,
}

impl SetColumnAddress {
    /// Creates a new Set Column Address command.
    pub const fn new(start_column: u16, end_column: u16) -> Self {
        Self {
            start_column,
            end_column,
        }
    }
}

impl DcsCommand for SetColumnAddress {
    fn instruction(&self) -> u8 {
        0x2A
    }

    fn fill_params_buf(&self, buffer: &mut [u8]) -> usize {
        buffer[0..2].copy_from_slice(&self.start_column.to_be_bytes());
        buffer[2..4].copy_from_slice(&self.end_column.to_be_bytes());

        4
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn caset_fills_data_properly() {
        let caset = SetColumnAddress::new(0, 320);

        let mut buffer = [0u8; 4];
        assert_eq!(caset.fill_params_buf(&mut buffer), 4);
        assert_eq!(buffer, [0, 0, 0x1, 0x40]);
    }
}
