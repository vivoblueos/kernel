//! mvendorid register

read_only_csr! {
    /// `mvendorid` register
    Mvendorid: 0xF11,
    mask: 0xffff_ffff,
    sentinel: 0,
}

read_only_csr_field! {
    Mvendorid,
    /// Represents the number of continuation bytes (`0x7f`) in the JEDEC manufacturer ID.
    bank: [7:31],
}

read_only_csr_field! {
    Mvendorid,
    /// Represents the final offset field in the JEDEC manufacturer ID.
    ///
    /// # Note
    ///
    /// The encoded value returned by `offset` does not include the odd parity bit (`0x80`).
    offset: [0:6],
}

impl Mvendorid {
    /// Represents the JEDEC manufacture continuation byte.
    pub const CONTINUATION: u8 = 0x7f;

    /// Gets the decoded JEDEC manufacturer ID from the `mvendorid` value.
    ///
    /// # Note
    ///
    /// This function returns an iterator over the decoded bytes.
    ///
    /// An iterator is needed because the encoding can theoretically return a max count (`0x1ff_ffff`) of continuation bytes (`0x7f`).
    ///
    /// The final byte in the iterator is the `offset`, including the odd parity bit (set only if even).
    pub fn jedec_manufacturer(&self) -> impl Iterator<Item = u8> {
        const DONE: usize = usize::MAX;

        let mut bank = self.bank();
        let offset = self.offset();

        core::iter::from_fn(move || match bank {
            DONE => None,
            0 => {
                bank = DONE;
                let parity = ((1 - (offset.count_ones() % 2)) << 7) as usize;
                Some((parity | offset) as u8)
            }
            _ => {
                bank -= 1;
                Some(Self::CONTINUATION)
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mvendorid() {
        (0..u32::BITS)
            .map(|r| ((1u64 << r) - 1) as usize)
            .for_each(|raw| {
                let exp_bank = raw >> 7;
                let exp_offset = raw & (Mvendorid::CONTINUATION as usize);
                let exp_parity = ((1 - (exp_offset.count_ones() % 2)) << 7) as u8;
                let exp_mvendorid = Mvendorid::from_bits(raw);

                assert_eq!(exp_mvendorid.bank(), exp_bank);
                assert_eq!(exp_mvendorid.offset(), exp_offset);

                let mut jedec_iter = exp_mvendorid.jedec_manufacturer();
                (0..exp_bank)
                    .for_each(|_| assert_eq!(jedec_iter.next(), Some(Mvendorid::CONTINUATION)));
                assert_eq!(jedec_iter.next(), Some(exp_parity | (exp_offset as u8)));
                assert_eq!(jedec_iter.next(), None);
            });

        // ISA example used as a concrete test vector.

        let exp_bank = 0xc;
        let exp_offset = 0x0a;
        let exp_decoded_offset = 0x8a;
        let raw_mvendorid = 0x60a;
        let exp_mvendorid = Mvendorid::from_bits(raw_mvendorid);

        assert_eq!(exp_mvendorid.bank(), exp_bank);
        assert_eq!(exp_mvendorid.offset(), exp_offset);

        let mut jedec_iter = exp_mvendorid.jedec_manufacturer();
        (0..exp_bank).for_each(|_| assert_eq!(jedec_iter.next(), Some(Mvendorid::CONTINUATION)));
        assert_eq!(jedec_iter.next(), Some(exp_decoded_offset));
        assert_eq!(jedec_iter.next(), None);
    }
}
