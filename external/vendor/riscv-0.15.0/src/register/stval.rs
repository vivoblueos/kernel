//! stval register

read_csr_as_usize!(0x143);
write_csr!(0x143);

/// Writes the CSR
#[inline]
pub unsafe fn write(bits: usize) {
    _write(bits)
}
