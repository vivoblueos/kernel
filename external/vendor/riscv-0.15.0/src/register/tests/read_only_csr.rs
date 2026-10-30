use crate::result::{Error, Result};

read_only_csr! {
    /// test CSR register type
    Mtest: 0x000,
    mask: 0b1111_1111_1111,
}

read_only_csr_field! {
    Mtest,
    /// test single-bit field
    single: 0,
}

read_only_csr_field! {
    Mtest,
    /// multiple single-bit field range
    multi_range: 1..=3,
}

read_only_csr_field! {
    Mtest,
    /// multi-bit field
    multi_field: [4:7],
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

read_only_csr_field! {
    Mtest,
    /// multi-bit field
    field_enum,
    MtestFieldEnum: [8:11],
}

// we don't test the `read` function, we are only testing in-memory functions.
#[allow(unused)]
pub fn _read_csr() -> Mtest {
    read()
}

#[allow(unused)]
pub fn _try_read_csr() -> Result<Mtest> {
    try_read()
}

#[test]
fn test_mtest_read_only() {
    let mut mtest = Mtest::from_bits(0);

    assert_eq!(mtest.bitmask(), Mtest::BITMASK);
    assert_eq!(mtest.bits(), 0);

    // check that single bit field getter/setters work.
    assert!(!mtest.single());

    mtest = Mtest::from_bits(1);
    assert!(mtest.single());

    mtest = Mtest::from_bits(0);

    // check that single bit range field getter/setters work.
    for i in 1..=3 {
        assert!(!mtest.multi_range(i));
        assert_eq!(mtest.try_multi_range(i), Ok(false));

        mtest = Mtest::from_bits(1 << i);
        assert!(mtest.multi_range(i));
        assert_eq!(mtest.try_multi_range(i), Ok(true));

        mtest = Mtest::from_bits(0 << i);
        assert!(!mtest.multi_range(i));
        assert_eq!(mtest.try_multi_range(i), Ok(false));
    }

    // check that multi-bit field getter/setters work.
    assert_eq!(mtest.multi_field(), 0);

    mtest = Mtest::from_bits(0xf << 4);
    assert_eq!(mtest.multi_field(), 0xf);

    mtest = Mtest::from_bits(0x3 << 4);
    assert_eq!(mtest.multi_field(), 0x3);

    // check that only bits in the field are set.
    mtest = Mtest::from_bits(0xff << 4);
    assert_eq!(mtest.multi_field(), 0xf);
    assert_eq!(mtest.bits(), 0xff << 4);

    mtest = Mtest::from_bits(0x0 << 4);
    assert_eq!(mtest.multi_field(), 0x0);

    assert_eq!(mtest.try_field_enum(), Err(Error::InvalidVariant(0)),);

    [
        MtestFieldEnum::Field1,
        MtestFieldEnum::Field2,
        MtestFieldEnum::Field3,
        MtestFieldEnum::Field4,
    ]
    .into_iter()
    .for_each(|variant| {
        mtest = Mtest::from_bits(variant.into_usize() << 8);
        assert_eq!(mtest.field_enum(), variant);
        assert_eq!(mtest.try_field_enum(), Ok(variant));
    });

    // check that setting an invalid variant returns `None`
    mtest = Mtest::from_bits(0xbad << 8);
    assert_eq!(mtest.try_field_enum(), Err(Error::InvalidVariant(13)),);
}
