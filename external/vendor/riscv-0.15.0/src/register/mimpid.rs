//! mimpid register

read_only_csr! {
    /// `mimpid` register
    Mimpid: 0xF13,
    mask: 0xffff_ffff,
    sentinel: 0,
}
