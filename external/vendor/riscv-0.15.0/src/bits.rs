/// Insert a new value into a bitfield
///
/// `value` is masked to `width` bits and inserted into `orig`.`
#[inline]
pub fn bf_insert(orig: usize, bit: usize, width: usize, value: usize) -> usize {
    let mask = (1 << width) - 1;
    orig & !(mask << bit) | ((value & mask) << bit)
}

/// Extract a value from a bitfield
///
/// Extracts `width` bits from bit offset `bit` and returns it shifted to bit 0.s
#[inline]
pub fn bf_extract(orig: usize, bit: usize, width: usize) -> usize {
    let mask = (1 << width) - 1;
    (orig >> bit) & mask
}
