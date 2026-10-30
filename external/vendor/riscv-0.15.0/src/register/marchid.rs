//! marchid register

read_only_csr! {
    /// `marchid` register
    Marchid: 0xF12,
    mask: 0xffff_ffff,
    sentinel: 0,
}
