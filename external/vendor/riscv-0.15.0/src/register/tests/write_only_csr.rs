use crate::result::{Error, Result};

write_only_csr! {
    /// test CSR register type
    Mtest: 0x000,
    mask: 0b1111_1111_1111,
}

write_only_csr_field! {
    Mtest,
    /// setter test single-bit field
    set_single: 0,
}

write_only_csr_field! {
    Mtest,
    /// setter multiple single-bit field range
    set_multi_range: 1..=3,
}

write_only_csr_field! {
    Mtest,
    /// setter multi-bit field
    set_multi_field: [4:7],
}

csr_field_enum! {
    /// field enum type with valid field variants
    MtestFieldEnum {
        default: Field1,
        Field1 = 1,
        Field2 = 2,
        Field3 = 3,
        Field4 = 15,
    }
}

write_only_csr_field! {
    Mtest,
    /// setter multi-bit field
    set_field_enum,
    MtestFieldEnum: [8:11],
}

// we don't test the `write` function, we are only testing in-memory functions.
#[allow(unused)]
pub fn _write_csr(csr: Mtest) {
    unsafe { write(csr) };
}

#[allow(unused)]
pub fn _try_write_csr(csr: Mtest) -> Result<()> {
    unsafe { try_write(csr) }
}

#[test]
fn test_mtest_write_only() {
    let mut mtest = Mtest::from_bits(0);

    assert_eq!(mtest.bitmask(), Mtest::BITMASK);
    assert_eq!(mtest.bits(), 0);

    // check that single bit field getter/setters work.
    mtest.set_single(true);
    assert_eq!(mtest.bits(), 1);

    mtest.set_single(false);
    assert_eq!(mtest.bits(), 0);

    // check that single bit range field getter/setters work.
    for i in 1..=3 {
        mtest.set_multi_range(i, true);
        assert_ne!(mtest.bits() & (1 << i), 0);

        mtest.set_multi_range(i, false);
        assert_eq!(mtest.bits() & (1 << i), 0);
    }

    // check that multi-bit field getter/setters work.
    mtest.set_multi_field(0xf);
    assert_eq!(mtest.bits() >> 4, 0xf);

    mtest.set_multi_field(0x3);
    assert_eq!(mtest.bits() >> 4, 0x3);

    // check that only bits in the field are set.
    mtest.set_multi_field(0xff);
    assert_eq!(mtest.bits() >> 4, 0xf);

    mtest.set_multi_field(0x0);
    assert_eq!(mtest.bits() >> 4, 0x0);

    mtest = Mtest::from_bits(0);

    assert_eq!(
        MtestFieldEnum::from_usize(mtest.bits() >> 8),
        Err(Error::InvalidVariant(0))
    );

    [
        MtestFieldEnum::Field1,
        MtestFieldEnum::Field2,
        MtestFieldEnum::Field3,
        MtestFieldEnum::Field4,
    ]
    .into_iter()
    .for_each(|variant| {
        mtest.set_field_enum(variant);
        assert_eq!(MtestFieldEnum::from_usize(mtest.bits() >> 8), Ok(variant));
    });

    // check that setting an invalid variant returns `None`
    mtest = Mtest::from_bits(0xbad << 8);
    assert_eq!(
        MtestFieldEnum::from_usize(mtest.bits() >> 8),
        Err(Error::InvalidVariant(13))
    );
}
