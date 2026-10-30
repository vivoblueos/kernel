#![recursion_limit = "128"]
#![allow(clippy::cognitive_complexity)]

use bitfield::{bitfield, bitfield_fields};

// We use a constant to make sure bits positions don't need to be literals but
// can also be constants or expressions.
const THREE: usize = 3;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Foo(u16);
impl From<u8> for Foo {
    fn from(value: u8) -> Foo {
        Foo(u16::from(value))
    }
}

impl From<Foo> for u8 {
    fn from(value: Foo) -> u8 {
        value.0 as u8
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct EvenU8(u8);

impl From<EvenU8> for u8 {
    fn from(value: EvenU8) -> u8 {
        value.0
    }
}

impl TryFrom<u8> for EvenU8 {
    type Error = ();

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        if value % 2 == 0 {
            Ok(EvenU8(value))
        } else {
            Err(())
        }
    }
}

bitfield! {
    #[derive(Copy, Clone)]
    /// documentation comments also work!
    struct FooBar(u32);
    impl Debug;
    impl BitOr;
    foo1, set_foo1: 0, 0;
    u8;
    foo2, set_foo2: 31, 31;
    foo3, set_foo3: THREE, 0;
    // We make sure attributes are applied to fields. If attributes were not
    // applied, the compilation would fail with a `duplicate definition`
    // error.
    #[cfg(not(test))]
    foo3, set_foo3: 3, 0;
    u16, foo4, set_foo4: 31, 28;
    foo5, set_foo5: 0, 0, 32;
    u32;
    foo6, set_foo6: 5, THREE, THREE;
    mask GETTER_MASK(u32), getter_only, _: 3, 1;
    mask SETTER_MASK(u32), _, setter_only: 2*2, 2;
    pub mask PUB_GETTER_MASK(u32), pub_getter_only, _: 3, 1;
    pub mask PUB_SETTER_MASK(u32), _, pub_setter_only: 2*2, 2;
    getter_only_array, _: 5, 3, 3;
    _, setter_only_array: 2*THREE, 4, 3;
    all_bits, set_all_bits: 31, 0;
    mask SINGLE_BIT_MASK(u32), single_bit, set_single_bit: 3;
    u8, into Foo, into_foo1, set_into_foo1: 31, 31;
    pub u8, mask PUB_MASK(u32), into Foo, into_foo2, set_into_foo2: 31, 31;
    u8, from into Foo, from_foo1, set_from_foo1: 31, 31;
    u8, from into Foo, _, set_from_foo2: 31, 31;
    u8;
    into Foo, into_foo3, set_into_foo3: 31, 31;
    pub into Foo, into_foo4, set_into_foo4: 31, 31;
    into Foo, _, set_into_foo5: 31, 31;
    into Foo, into_foo6, _: 29, 29, 3;
    from into Foo, from_foo3, set_from_foo3: 31, 31;
    from into Foo, _, set_from_foo4: 31, 31;
    from into Foo, from_foo5, set_from_foo5: 29, 29, 3;
    from into Foo, from_foo6, _: 31, 31;
    from try_into EvenU8, from_foo7, set_from_foo7: 31, 30;
    try_into EvenU8, from_foo8, set_from_foo8: 31, 30;
    try_into EvenU8, from_foo9, set_from_foo9: 8, 8, 3;

    i8;
    signed_single_bit, set_signed_single_bit: 0, 0;
    signed_two_bits, set_signed_two_bits: 1, 0;
    signed_eight_bits, set_signed_eight_bits: 7, 0;
    signed_eight_bits_unaligned, set_signed_eight_bits_unaligned: 8, 1;
    u128, mask U128_MASK(u128), u128_getter, set_u128: 8, 1;
    i128, mask I128_MASK(i128), i128_getter, set_i128: 8, 1;
    bool, bool_array_getter, bool_array_setter: 8, 8, 3;
}

impl FooBar {
    bitfield_fields! {
        // Boolean field don't need a type
        foo7, _: 1;
    }

    bitfield_fields! {
        // If all fields have a type, we don't need to specify a default type
        u8, foo8,_: 1, 0;
        u32, foo9, _: 2, 0;
    }

    bitfield_fields! {
        // We can still set a default type
        u16;
        foo10, _: 2, 0;
        u32, foo11, _: 2, 0;
        foo12, _: 2, 0;
    }

    // Check if an empty bitfield_fields compiles without errors.
    bitfield_fields! {}

    // Check if mask, from and into are allowed as getter names
    bitfield_fields! {
        u8, mask, _: 2,0;
        u8, from, _: 2,0;
        u8, into, _: 2,0;
    }

    bitfield_fields! {
        u8, lsb_msb_inverted, set_lsb_msb_inverted: 1, 3;
        u8, lsb_msb_inverted_array, set_lsb_msb_inverted_array: 2, 3, 2;
    }
}

#[test]
fn test_single_bit() {
    let mut fb = FooBar(0);

    fb.set_foo1(1);
    assert_eq!(0x1, fb.0);
    assert_eq!(0x1, fb.foo1());
    assert_eq!(0x0, fb.foo2());
    assert!(!fb.single_bit());
    assert_eq!(-1, fb.signed_single_bit());

    fb.set_foo2(1);
    assert_eq!(0x8000_0001, fb.0);
    assert_eq!(0x1, fb.foo1());
    assert_eq!(0x1, fb.foo2());
    assert!(!fb.single_bit());
    assert_eq!(-1, fb.signed_single_bit());

    fb.set_foo1(0);
    assert_eq!(0x8000_0000, fb.0);
    assert_eq!(0x0, fb.foo1());
    assert_eq!(0x1, fb.foo2());
    assert!(!fb.single_bit());
    assert_eq!(0, fb.signed_single_bit());

    fb.set_single_bit(true);
    assert_eq!(0x8000_0008, fb.0);
    assert_eq!(0x0, fb.foo1());
    assert_eq!(0x1, fb.foo2());
    assert!(fb.single_bit());
    assert_eq!(0, fb.signed_single_bit());

    fb.set_signed_single_bit(-1);
    assert_eq!(0x8000_0009, fb.0);
    assert_eq!(0x1, fb.foo1());
    assert_eq!(0x1, fb.foo2());
    assert!(fb.single_bit());
    assert_eq!(-1, fb.signed_single_bit());
}

#[test]
fn test_single_bit_plus_garbage() {
    let mut fb = FooBar(0);

    fb.set_foo1(0b10);
    assert_eq!(0x0, fb.0);
    assert_eq!(0x0, fb.foo1());
    assert_eq!(0x0, fb.foo2());

    fb.set_foo1(0b11);
    assert_eq!(0x1, fb.0);
    assert_eq!(0x1, fb.foo1());
    assert_eq!(0x0, fb.foo2());
}

#[test]
fn test_multiple_bit() {
    let mut fb = FooBar(0);

    fb.set_foo3(0x0F);
    assert_eq!(0xF, fb.0);
    assert_eq!(0xF, fb.foo3());
    assert_eq!(0x0, fb.foo4());

    fb.set_foo4(0x0F);
    assert_eq!(0xF000_000F, fb.0);
    assert_eq!(0xF, fb.foo3());
    assert_eq!(0xF, fb.foo4());

    fb.set_foo3(0);
    assert_eq!(0xF000_0000, fb.0);
    assert_eq!(0x0, fb.foo3());
    assert_eq!(0xF, fb.foo4());

    fb.set_foo3(0xA);
    assert_eq!(0xF000_000A, fb.0);
    assert_eq!(0xA, fb.foo3());
    assert_eq!(0xF, fb.foo4());
}

#[test]
fn test_bool_array_field() {
    let mut fb = FooBar(0);

    assert!(!fb.bool_array_getter(0));
    assert!(!fb.bool_array_getter(1));
    assert!(!fb.bool_array_getter(2));

    fb.bool_array_setter(1, true);

    assert_eq!(1 << 9, fb.0);
    assert!(!fb.bool_array_getter(0));
    assert!(fb.bool_array_getter(1));
    assert!(!fb.bool_array_getter(2));
}

#[test]
fn test_try_into() {
    let mut fb = FooBar(0);
    assert_eq!(fb.from_foo7(), Ok(EvenU8(0)));
    assert_eq!(fb.from_foo8(), Ok(EvenU8(0)));
    fb.set_from_foo7(EvenU8(1));
    assert_eq!(fb.from_foo7(), Err(()));
    assert_eq!(fb.from_foo8(), Err(()));
    fb.set_from_foo8(2);
    assert_eq!(fb.from_foo7(), Ok(EvenU8(2)));
    assert_eq!(fb.from_foo8(), Ok(EvenU8(2)));
}

#[test]
#[should_panic(expected = "the MSB (1) is smaller than the LSB (3), you likely inverted them")]
fn lsb_msb_inverted_should_panic_on_access_1() {
    let fb = FooBar(0);
    fb.lsb_msb_inverted();
}

#[test]
#[should_panic(expected = "the MSB (1) is smaller than the LSB (3), you likely inverted them")]
fn lsb_msb_inverted_should_panic_on_access_2() {
    let mut fb = FooBar(0);
    fb.set_lsb_msb_inverted(1);
}

#[test]
#[should_panic(expected = "the MSB (2) is smaller than the LSB (3), you likely inverted them")]
fn lsb_msb_inverted_should_panic_on_access_3() {
    let fb = FooBar(0);
    fb.lsb_msb_inverted_array(0);
}

#[test]
#[should_panic(expected = "the MSB (2) is smaller than the LSB (3), you likely inverted them")]
fn lsb_msb_inverted_should_panic_on_access_4() {
    let mut fb = FooBar(0);
    fb.set_lsb_msb_inverted_array(0, 1);
}

bitfield! {
    #[derive(Clone, Copy)]
    struct FourFields(u8);
    impl BitOr;
    impl BitAnd;
    impl BitXor;
    impl new;
    a, set_a: 0;
    b, set_b: 1;
    c, set_c: 2;
    d, set_d: 3;
}

#[test]
fn test_bitwise_ops() {
    let mut ff1 = FourFields(0);
    ff1.set_a(true);
    ff1.set_b(true);
    let mut ff2 = FourFields(0);
    ff2.set_a(true);
    ff2.set_c(true);

    let ffand = ff1 & ff2;
    assert!(ffand.a());
    assert!(!ffand.b());
    assert!(!ffand.c());
    assert!(!ffand.d());

    let ffor = ff1 | ff2;
    assert!(ffor.a());
    assert!(ffor.b());
    assert!(ffor.c());
    assert!(!ffor.d());

    let ffxor = ff1 ^ ff2;
    assert!(!ffxor.a());
    assert!(ffxor.b());
    assert!(ffxor.c());
    assert!(!ffxor.d());

    ff1 ^= ff2;
    assert!(!ff1.a());
    assert!(ff1.b());
    assert!(ff1.c());
    assert!(!ff1.d());
}

#[test]
fn test_constructor() {
    let ff1 = FourFields::new(true, false, true, false);
    assert!(ff1.a());
    assert!(!ff1.b());
    assert!(ff1.c());
    assert!(!ff1.d());
}

#[test]
fn test_getter_setter_only() {
    let mut fb = FooBar(0);
    fb.setter_only(0x7);
    assert_eq!(0x1C, fb.0);
    assert_eq!(0x6, fb.getter_only());
}

#[test]
fn test_array_field1() {
    let mut fb = FooBar(0);

    fb.set_foo5(0, 1);
    assert_eq!(0x1, fb.0);
    assert_eq!(1, fb.foo5(0));

    fb.set_foo5(0, 0);
    assert_eq!(0x0, fb.0);
    assert_eq!(0, fb.foo5(0));

    fb.set_foo5(0, 1);
    fb.set_foo5(6, 1);
    fb.set_foo5(31, 1);
    assert_eq!(0x8000_0041, fb.0);
    assert_eq!(1, fb.foo5(0));
    assert_eq!(1, fb.foo5(6));
    assert_eq!(1, fb.foo5(31));
    assert_eq!(0, fb.foo5(1));
    assert_eq!(0, fb.foo5(5));
    assert_eq!(0, fb.foo5(7));
    assert_eq!(0, fb.foo5(30));
}

#[test]
fn test_array_field2() {
    let mut fb = FooBar(0);

    fb.set_foo6(0, 1);
    assert_eq!(0x8, fb.0);
    assert_eq!(1, fb.foo6(0));
    assert_eq!(0, fb.foo6(1));
    assert_eq!(0, fb.foo6(2));

    fb.set_foo6(0, 7);
    assert_eq!(0x38, fb.0);
    assert_eq!(7, fb.foo6(0));
    assert_eq!(0, fb.foo6(1));
    assert_eq!(0, fb.foo6(2));

    fb.set_foo6(2, 7);
    assert_eq!(0xE38, fb.0);
    assert_eq!(7, fb.foo6(0));
    assert_eq!(0, fb.foo6(1));
    assert_eq!(7, fb.foo6(2));

    fb.set_foo6(0, 0);
    assert_eq!(0xE00, fb.0);
    assert_eq!(0, fb.foo6(0));
    assert_eq!(0, fb.foo6(1));
    assert_eq!(7, fb.foo6(2));
}

#[allow(clippy::identity_op)]
#[allow(clippy::erasing_op)]
#[test]
fn test_setter_only_array() {
    let mut fb = FooBar(0);

    fb.setter_only_array(0, 0);
    assert_eq!(0x0, fb.0);

    fb.setter_only_array(0, 0b111);
    assert_eq!(0b111 << (4 + 0 * 2), fb.0);

    fb.setter_only_array(0, 0);
    fb.setter_only_array(1, 0b111);
    assert_eq!(0b111 << (4 + 1 * 3), fb.0);

    fb.setter_only_array(1, 0);
    fb.setter_only_array(2, 0b111);
    assert_eq!(0b111 << (4 + 2 * 3), fb.0);
}

#[test]
fn test_getter_only_array() {
    let mut fb = FooBar(0);

    assert_eq!(0, fb.getter_only_array(0));
    assert_eq!(0, fb.getter_only_array(1));
    assert_eq!(0, fb.getter_only_array(2));

    fb.0 = !(0x1FF << 3);
    assert_eq!(0, fb.getter_only_array(0));
    assert_eq!(0, fb.getter_only_array(1));
    assert_eq!(0, fb.getter_only_array(2));

    fb.0 = 0xF << 3;
    assert_eq!(0b111, fb.getter_only_array(0));
    assert_eq!(0b001, fb.getter_only_array(1));
    assert_eq!(0, fb.getter_only_array(2));

    fb.0 = 0xF << 6;
    assert_eq!(0, fb.getter_only_array(0));
    assert_eq!(0b111, fb.getter_only_array(1));
    assert_eq!(0b001, fb.getter_only_array(2));

    fb.0 = 0xF << 8;
    assert_eq!(0, fb.getter_only_array(0));
    assert_eq!(0b100, fb.getter_only_array(1));
    assert_eq!(0b111, fb.getter_only_array(2));

    fb.0 = 0b101_010_110 << 3;
    assert_eq!(0b110, fb.getter_only_array(0));
    assert_eq!(0b010, fb.getter_only_array(1));
    assert_eq!(0b101, fb.getter_only_array(2));
}

#[test]
fn test_signed() {
    let mut fb = FooBar(0);

    assert_eq!(0, fb.signed_two_bits());
    assert_eq!(0, fb.signed_eight_bits());
    assert_eq!(0, fb.signed_eight_bits_unaligned());

    fb.set_signed_two_bits(-2);
    assert_eq!(0b10, fb.0);
    assert_eq!(-2, fb.signed_two_bits());
    assert_eq!(2, fb.signed_eight_bits());
    assert_eq!(1, fb.signed_eight_bits_unaligned());

    fb.set_signed_two_bits(-1);
    assert_eq!(0b11, fb.0);
    assert_eq!(-1, fb.signed_two_bits());
    assert_eq!(3, fb.signed_eight_bits());
    assert_eq!(1, fb.signed_eight_bits_unaligned());

    fb.set_signed_two_bits(0);
    assert_eq!(0, fb.0);
    assert_eq!(0, fb.signed_two_bits());
    assert_eq!(0, fb.signed_eight_bits());
    assert_eq!(0, fb.signed_eight_bits_unaligned());

    fb.set_signed_two_bits(1);
    assert_eq!(1, fb.0);
    assert_eq!(1, fb.signed_two_bits());
    assert_eq!(1, fb.signed_eight_bits());
    assert_eq!(0, fb.signed_eight_bits_unaligned());

    fb.set_signed_eight_bits(0);
    assert_eq!(0, fb.0);
    assert_eq!(0, fb.signed_two_bits());
    assert_eq!(0, fb.signed_eight_bits());
    assert_eq!(0, fb.signed_eight_bits_unaligned());

    fb.set_signed_eight_bits(-1);
    assert_eq!(0xFF, fb.0);
    assert_eq!(-1, fb.signed_two_bits());
    assert_eq!(-1, fb.signed_eight_bits());
    assert_eq!(127, fb.signed_eight_bits_unaligned());

    fb.set_signed_eight_bits(-128);
    assert_eq!(0x80, fb.0);
    assert_eq!(0, fb.signed_two_bits());
    assert_eq!(-128, fb.signed_eight_bits());
    assert_eq!(64, fb.signed_eight_bits_unaligned());

    fb.set_signed_eight_bits(127);
    assert_eq!(0x7F, fb.0);
    assert_eq!(-1, fb.signed_two_bits());
    assert_eq!(127, fb.signed_eight_bits());
    assert_eq!(63, fb.signed_eight_bits_unaligned());

    fb.set_signed_eight_bits_unaligned(0);
    assert_eq!(1, fb.0);
    assert_eq!(1, fb.signed_two_bits());
    assert_eq!(1, fb.signed_eight_bits());
    assert_eq!(0, fb.signed_eight_bits_unaligned());

    fb.set_signed_eight_bits(0);
    fb.set_signed_eight_bits_unaligned(-1);
    assert_eq!(0x1FE, fb.0);
    assert_eq!(-2, fb.signed_two_bits());
    assert_eq!(-2, fb.signed_eight_bits());
    assert_eq!(-1, fb.signed_eight_bits_unaligned());

    fb.set_signed_eight_bits_unaligned(-128);
    assert_eq!(0x100, fb.0);
    assert_eq!(0, fb.signed_two_bits());
    assert_eq!(0, fb.signed_eight_bits());
    assert_eq!(-128, fb.signed_eight_bits_unaligned());
    fb.set_signed_eight_bits_unaligned(127);
    assert_eq!(0xFE, fb.0);
    assert_eq!(-2, fb.signed_two_bits());
    assert_eq!(-2, fb.signed_eight_bits());
    assert_eq!(127, fb.signed_eight_bits_unaligned());
}

#[test]
fn test_field_type() {
    let fb = FooBar(0);
    let _: u32 = fb.foo1();
    let _: u8 = fb.foo2();
    let _: u8 = fb.foo3();
    let _: u16 = fb.foo4();
    let _: u8 = fb.foo5(0);
    let _: u32 = fb.foo6(0);

    let _: bool = fb.foo7();
    let _: u8 = fb.foo8();
    let _: u32 = fb.foo9();
    let _: u16 = fb.foo10();
    let _: u32 = fb.foo11();
    let _: u16 = fb.foo12();

    let _: Foo = fb.into_foo1();
    let _: Foo = fb.into_foo2();
    let _: Foo = fb.into_foo3();
    let _: Foo = fb.into_foo4();
    let _: Foo = fb.into_foo6(0);

    let _: Foo = fb.from_foo1();
    let _: Foo = fb.from_foo3();
    let _: Foo = fb.from_foo5(0);

    let _: i8 = fb.signed_single_bit();
    let _: i8 = fb.signed_two_bits();
    let _: i8 = fb.signed_eight_bits();
    let _: i8 = fb.signed_eight_bits_unaligned();

    let _: u128 = fb.u128_getter();
    let _: i128 = fb.i128_getter();
}

#[test]
fn test_into_setter() {
    let mut fb = FooBar(0);

    // We just check that the parameter type is correct
    fb.set_into_foo1(0u8);
    fb.set_into_foo2(0u8);
    fb.set_into_foo3(0u8);
    fb.set_into_foo4(0u8);
}

#[test]
fn test_from_setter() {
    let mut fb = FooBar(0);
    assert_eq!(0, fb.0);

    fb.set_from_foo1(Foo(1));
    assert_eq!(1 << 31, fb.0);
    fb.set_from_foo1(Foo(0));
    assert_eq!(0, fb.0);

    fb.set_from_foo2(Foo(1));
    assert_eq!(1 << 31, fb.0);
    fb.set_from_foo2(Foo(0));
    assert_eq!(0, fb.0);

    fb.set_from_foo3(Foo(1));
    assert_eq!(1 << 31, fb.0);
    fb.set_from_foo3(Foo(0));
    assert_eq!(0, fb.0);

    fb.set_from_foo4(Foo(1));
    assert_eq!(1 << 31, fb.0);
    fb.set_from_foo4(Foo(0));
    assert_eq!(0, fb.0);

    fb.set_from_foo5(1, Foo(1));
    assert_eq!(1 << 30, fb.0);
}

#[test]
fn test_all_bits() {
    let mut fb = FooBar(0);

    assert_eq!(0, fb.all_bits());

    fb.set_all_bits(!0u32);
    assert_eq!(!0u32, fb.0);
    assert_eq!(!0u32, fb.all_bits());

    fb.0 = 0x8000_0001;
    assert_eq!(0x8000_0001, fb.all_bits());
}

#[test]
fn test_is_copy() {
    let a = FooBar(0);
    let _b = a;
    let _c = a;
}

#[test]
fn test_debug() {
    let fb = FooBar(1_234_567_890);
    let expected = "FooBar { .0: 1234567890, foo1: 0, foo2: 0, foo3: 2, foo3: 2, foo4: 4, foo5: [0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0], foo6: [2, 3, 1], getter_only: 1, pub_getter_only: 1, getter_only_array: [2, 3, 1], all_bits: 1234567890, single_bit: false, into_foo1: Foo(0), into_foo2: Foo(0), from_foo1: Foo(0), into_foo3: Foo(0), into_foo4: Foo(0), into_foo6: [Foo(0), Foo(1), Foo(0)], from_foo3: Foo(0), from_foo5: [Foo(0), Foo(1), Foo(0)], from_foo6: Foo(0), from_foo7: Err(()), from_foo8: Err(()), from_foo9: [Ok(EvenU8(0)), Err(()), Ok(EvenU8(0))], signed_single_bit: 0, signed_two_bits: -2, signed_eight_bits: -46, signed_eight_bits_unaligned: 105, u128_getter: 105, i128_getter: 105, bool_array_getter: [false, true, false] }";
    assert_eq!(expected, format!("{:?}", fb))
}

bitfield! {
    #[derive(Clone, Copy)]
    struct ArrayBitfield([u8]);
    impl BitAnd;
    impl BitOr;
    impl BitXor;
    impl Debug;
    impl new;
    u32;
    foo1, set_foo1: 0, 0;
    foo2, set_foo2: 7, 0;
    foo3, set_foo3: 8, 1;
    foo4, set_foo4: 19, 4;
    i32;
    signed_foo1, set_signed_foo1: 0, 0;
    signed_foo2, set_signed_foo2: 7, 0;
    signed_foo3, set_signed_foo3: 8, 1;
    signed_foo4, set_signed_foo4: 19, 4;
    u128, u128_getter, set_u128: 19, 4;
    u8, from into Foo, into_from_foo1, set_into_from_foo1: 21, 20;
    u8, into Foo, into_foo2, set_into_foo2: 23, 22;
    u8, from Foo, from_foo3, set_from_foo3: 25, 24;
}

impl ArrayBitfield<[u8; 3]> {
    bitfield_fields! {
        u8, lsb_msb_inverted, set_lsb_msb_inverted: 3, 4;
        u8, lsb_msb_inverted_array, set_lsb_msb_inverted_array: 4, 5, 2;
    }
}

#[test]
fn test_arraybitfield() {
    let mut ab = ArrayBitfield([0; 3]);

    assert_eq!(0u32, ab.foo1());
    assert_eq!(0u32, ab.foo2());
    assert_eq!(0u32, ab.foo3());
    assert_eq!(0u32, ab.foo4());
    assert_eq!(0i32, ab.signed_foo1());
    assert_eq!(0i32, ab.signed_foo2());
    assert_eq!(0i32, ab.signed_foo3());
    assert_eq!(0i32, ab.signed_foo4());
    assert_eq!(0u128, ab.u128_getter());

    ab.set_foo1(1);
    assert_eq!([1, 0, 0], ab.0);
    assert_eq!(1, ab.foo1());
    assert_eq!(1, ab.foo2());
    assert_eq!(0, ab.foo3());
    assert_eq!(0, ab.foo4());
    assert_eq!(-1, ab.signed_foo1());
    assert_eq!(1, ab.signed_foo2());
    assert_eq!(0, ab.signed_foo3());
    assert_eq!(0, ab.signed_foo4());
    assert_eq!(0, ab.u128_getter());

    ab.set_foo1(0);
    ab.set_foo2(0xFF);
    assert_eq!([0xFF, 0, 0], ab.0);
    assert_eq!(1, ab.foo1());
    assert_eq!(0xFF, ab.foo2());
    assert_eq!(0x7F, ab.foo3());
    assert_eq!(0x0F, ab.foo4());
    assert_eq!(-1, ab.signed_foo1());
    assert_eq!(-1, ab.signed_foo2());
    assert_eq!(127, ab.signed_foo3());
    assert_eq!(0x0F, ab.signed_foo4());
    assert_eq!(0x0F, ab.u128_getter());

    ab.set_foo2(0);
    ab.set_foo3(0xFF);
    assert_eq!([0xFE, 0x01, 0], ab.0);
    assert_eq!(0, ab.foo1());
    assert_eq!(0xFE, ab.foo2());
    assert_eq!(0xFF, ab.foo3());
    assert_eq!(0x1F, ab.foo4());
    assert_eq!(0, ab.signed_foo1());
    assert_eq!(-2, ab.signed_foo2());
    assert_eq!(-1, ab.signed_foo3());
    assert_eq!(0x1F, ab.signed_foo4());
    assert_eq!(0x1F, ab.u128_getter());

    ab.set_foo3(0);
    ab.set_foo4(0xFFFF);
    assert_eq!([0xF0, 0xFF, 0x0F], ab.0);
    assert_eq!(0, ab.foo1());
    assert_eq!(0xF0, ab.foo2());
    assert_eq!(0xF8, ab.foo3());
    assert_eq!(0xFFFF, ab.foo4());
    assert_eq!(0, ab.signed_foo1());
    assert_eq!(-16, ab.signed_foo2());
    assert_eq!(-8, ab.signed_foo3());
    assert_eq!(-1, ab.signed_foo4());
    assert_eq!(0xFFFF, ab.u128_getter());

    ab.set_foo4(0x0);
    ab.set_signed_foo1(0);
    assert_eq!([0x00, 0x00, 0x00], ab.0);

    ab.set_signed_foo1(-1);
    assert_eq!([0x01, 0x00, 0x00], ab.0);

    ab.set_signed_foo1(0);
    ab.set_signed_foo2(127);
    assert_eq!([0x7F, 0x00, 0x00], ab.0);

    ab.set_signed_foo2(-128);
    assert_eq!([0x80, 0x00, 0x00], ab.0);

    ab.set_signed_foo2(1);
    assert_eq!([0x01, 0x00, 0x00], ab.0);

    ab.set_signed_foo2(-1);
    assert_eq!([0xFF, 0x00, 0x00], ab.0);

    ab.set_signed_foo2(0);
    ab.set_signed_foo3(127);
    assert_eq!([0xFE, 0x00, 0x00], ab.0);

    ab.set_signed_foo3(-1);
    assert_eq!([0xFE, 0x01, 0x00], ab.0);

    ab.set_signed_foo3(0);
    ab.set_signed_foo4(-1);
    assert_eq!([0xF0, 0xFF, 0x0F], ab.0);

    ab.set_signed_foo4(0);
    ab.set_u128(0xFFFF);
    assert_eq!([0xF0, 0xFF, 0x0F], ab.0);
}

#[test]
#[should_panic(expected = "the MSB (3) is smaller than the LSB (4), you likely inverted them")]
fn lsb_msb_inverted_should_panic_on_access_with_array_bitfield_1() {
    let ab = ArrayBitfield([0; 3]);
    ab.lsb_msb_inverted();
}

#[test]
#[should_panic(expected = "the MSB (3) is smaller than the LSB (4), you likely inverted them")]
fn lsb_msb_inverted_should_panic_on_access_with_array_bitfield_2() {
    let mut ab = ArrayBitfield([0; 3]);
    ab.set_lsb_msb_inverted(1);
}

#[test]
#[should_panic(expected = "the MSB (4) is smaller than the LSB (5), you likely inverted them")]
fn lsb_msb_inverted_should_panic_on_access_with_array_bitfield_3() {
    let ab = ArrayBitfield([0; 3]);
    ab.lsb_msb_inverted_array(0);
}

#[test]
#[should_panic(expected = "the MSB (4) is smaller than the LSB (5), you likely inverted them")]
fn lsb_msb_inverted_should_panic_on_access_with_array_bitfield_4() {
    let mut ab = ArrayBitfield([0; 3]);
    ab.set_lsb_msb_inverted_array(1, 1);
}

#[test]
fn test_arraybitfield2() {
    // Check that the macro can be called from a function.
    bitfield! {
        struct ArrayBitfield2([u16]);
        impl Debug;
        u32;
        foo1, set_foo1: 0, 0;
        foo2, set_foo2: 7, 0;
        foo3, set_foo3: 8, 1;
        foo4, set_foo4: 20, 4;
        bool, bool_array_getter, bool_array_setter: 0, 0, 3;
    }
    let mut ab = ArrayBitfield2([0; 2]);

    assert_eq!(0, ab.foo1());
    assert_eq!(0, ab.foo2());
    assert_eq!(0, ab.foo3());
    assert_eq!(0, ab.foo4());

    ab.set_foo1(1);
    assert_eq!([1, 0], ab.0);
    assert_eq!(1, ab.foo1());
    assert_eq!(1, ab.foo2());
    assert_eq!(0, ab.foo3());
    assert_eq!(0, ab.foo4());

    ab.set_foo1(0);
    ab.set_foo2(0xFF);
    assert_eq!([0xFF, 0], ab.0);
    assert_eq!(1, ab.foo1());
    assert_eq!(0xFF, ab.foo2());
    assert_eq!(0x7F, ab.foo3());
    assert_eq!(0x0F, ab.foo4());

    ab.set_foo2(0);
    ab.set_foo3(0xFF);
    assert_eq!([0x1FE, 0x0], ab.0);
    assert_eq!(0, ab.foo1());
    assert_eq!(0xFE, ab.foo2());
    assert_eq!(0xFF, ab.foo3());
    assert_eq!(0x1F, ab.foo4());

    ab.set_foo3(0);
    ab.set_foo4(0xFFFF);
    assert_eq!([0xFFF0, 0xF], ab.0);
    assert_eq!(0, ab.foo1());
    assert_eq!(0xF0, ab.foo2());
    assert_eq!(0xF8, ab.foo3());
    assert_eq!(0xFFFF, ab.foo4());
}

bitfield! {
    pub(self) struct ArrayBitfieldMsb0(MSB0 [u8]);
    impl Debug;
    u32;
    foo1, set_foo1: 0, 0;
    foo2, set_foo2: 7, 0;
    foo3, set_foo3: 8, 1;
    foo4, set_foo4: 19, 4;
    i32;
    signed_foo1, set_signed_foo1: 0, 0;
    signed_foo2, set_signed_foo2: 7, 0;
    signed_foo3, set_signed_foo3: 8, 1;
    signed_foo4, set_signed_foo4: 19, 4;
}

impl ArrayBitfieldMsb0<[u8; 3]> {
    bitfield_fields! {
        u8, lsb_msb_inverted, set_lsb_msb_inverted: 3, 4;
        u8, lsb_msb_inverted_array, set_lsb_msb_inverted_array: 4, 5, 2;
    }
}

#[test]
fn test_arraybitfield_msb0() {
    let mut ab = ArrayBitfieldMsb0([0; 3]);

    assert_eq!(0, ab.foo1());
    assert_eq!(0, ab.foo2());
    assert_eq!(0, ab.foo3());
    assert_eq!(0, ab.foo4());
    assert_eq!(0, ab.signed_foo1());
    assert_eq!(0, ab.signed_foo2());
    assert_eq!(0, ab.signed_foo3());
    assert_eq!(0, ab.signed_foo4());

    ab.set_foo1(1);
    assert_eq!([0b1000_0000, 0, 0], ab.0);
    assert_eq!(1, ab.foo1());
    assert_eq!(0b1000_0000, ab.foo2());
    assert_eq!(0, ab.foo3());
    assert_eq!(0, ab.foo4());
    assert_eq!(-1, ab.signed_foo1());
    assert_eq!(-128, ab.signed_foo2());
    assert_eq!(0, ab.signed_foo3());
    assert_eq!(0, ab.signed_foo4());

    ab.set_foo1(0);
    ab.set_foo2(0xFF);
    assert_eq!([0b1111_1111, 0, 0], ab.0);
    assert_eq!(1, ab.foo1());
    assert_eq!(0b1111_1111, ab.foo2());
    assert_eq!(0b1111_1110, ab.foo3());
    assert_eq!(0b1111_0000_0000_0000, ab.foo4());
    assert_eq!(-1, ab.signed_foo1());
    assert_eq!(-1, ab.signed_foo2());
    assert_eq!(-2, ab.signed_foo3());
    assert_eq!(-4096, ab.signed_foo4());

    ab.set_foo2(0);
    ab.set_foo3(0xFF);
    assert_eq!([0b0111_1111, 0b1000_0000, 0], ab.0);
    assert_eq!(0, ab.foo1());
    assert_eq!(0b0111_1111, ab.foo2());
    assert_eq!(0xFF, ab.foo3());
    assert_eq!(0b1111_1000_0000_0000, ab.foo4());
    assert_eq!(0, ab.signed_foo1());
    assert_eq!(127, ab.signed_foo2());
    assert_eq!(-1, ab.signed_foo3());
    assert_eq!(-2048, ab.signed_foo4());

    ab.set_foo3(0);
    ab.set_foo4(0xFFFF);
    assert_eq!([0x0F, 0xFF, 0xF0], ab.0);
    assert_eq!(0, ab.foo1());
    assert_eq!(0x0F, ab.foo2());
    assert_eq!(0b0001_1111, ab.foo3());
    assert_eq!(0xFFFF, ab.foo4());
    assert_eq!(0, ab.signed_foo1());
    assert_eq!(0x0F, ab.signed_foo2());
    assert_eq!(0b0001_1111, ab.signed_foo3());
    assert_eq!(-1, ab.signed_foo4());

    ab.set_foo4(0x0);
    ab.set_signed_foo1(0);
    assert_eq!([0x00, 0x00, 0x00], ab.0);

    ab.set_signed_foo1(-1);
    assert_eq!([0b1000_0000, 0x00, 0x00], ab.0);

    ab.set_signed_foo1(0);
    ab.set_signed_foo2(127);
    assert_eq!([0x7F, 0x00, 0x00], ab.0);

    ab.set_signed_foo2(-128);
    assert_eq!([0x80, 0x00, 0x00], ab.0);

    ab.set_signed_foo2(1);
    assert_eq!([0x01, 0x00, 0x00], ab.0);

    ab.set_signed_foo2(-1);
    assert_eq!([0xFF, 0x00, 0x00], ab.0);

    ab.set_signed_foo2(0);
    ab.set_signed_foo3(127);
    assert_eq!([0b0011_1111, 0b1000_0000, 0], ab.0);

    ab.set_signed_foo3(-1);
    assert_eq!([0b0111_1111, 0b1000_0000, 0], ab.0);

    ab.set_signed_foo3(0);
    ab.set_signed_foo4(-1);
    assert_eq!([0x0F, 0xFF, 0xF0], ab.0);
}

#[test]
#[should_panic(expected = "the MSB (3) is smaller than the LSB (4), you likely inverted them")]
fn lsb_msb_inverted_should_panic_on_access_with_array_msb0_bitfield_1() {
    let ab = ArrayBitfieldMsb0([0; 3]);
    ab.lsb_msb_inverted();
}

#[test]
#[should_panic(expected = "the MSB (3) is smaller than the LSB (4), you likely inverted them")]
fn lsb_msb_inverted_should_panic_on_access_with_array_msb0_bitfield_2() {
    let mut ab = ArrayBitfieldMsb0([0; 3]);
    ab.set_lsb_msb_inverted(1);
}

#[test]
#[should_panic(expected = "the MSB (4) is smaller than the LSB (5), you likely inverted them")]
fn lsb_msb_inverted_should_panic_on_access_with_array_msb0_bitfield_3() {
    let ab = ArrayBitfieldMsb0([0; 3]);
    ab.lsb_msb_inverted_array(0);
}

#[test]
#[should_panic(expected = "the MSB (4) is smaller than the LSB (5), you likely inverted them")]
fn lsb_msb_inverted_should_panic_on_access_with_array_msb0_bitfield_4() {
    let mut ab = ArrayBitfieldMsb0([0; 3]);
    ab.set_lsb_msb_inverted_array(1, 1);
}

#[test]
fn test_arraybitfield_bitops() {
    let mut a = ArrayBitfield([1u8; 3]);
    let b = ArrayBitfield([1u8, 2u8, 4u8]);

    let c = a | b;
    assert_eq!(c.0, [1, 3, 5]);

    let d = a & b;
    assert_eq!(d.0, [1, 0, 0]);

    let e = a ^ b;
    assert_eq!(e.0, [0, 3, 5]);

    a ^= b;
    assert_eq!(a.0, [0, 3, 5]);

    let mut vec_a = ArrayBitfield(vec![1u8; 3]);
    let vec_b = ArrayBitfield(vec![1u8, 2u8, 4u8]);

    let vec_c = vec_a.clone() | vec_b.clone();
    assert_eq!(vec_c.0, [1, 3, 5]);

    let vec_d = vec_a.clone() & vec_b.clone();
    assert_eq!(vec_d.0, [1, 0, 0]);

    let vec_e = vec_a.clone() ^ vec_b.clone();
    assert_eq!(vec_e.0, [0, 3, 5]);

    vec_a ^= vec_b;
    assert_eq!(vec_a.0, [0, 3, 5]);
}

#[test]
fn test_arraybitfield_constructor() {
    let a: ArrayBitfield<[u8; 4]> =
        ArrayBitfield::new(1, 2, 3, 4, -1, -2, -3, -4, 0b0001_0000, Foo(1), 2u8, Foo(3));
    println!("{:b}", a.0[0]);
    assert_eq!(a.foo1(), 0);
    assert_eq!(a.foo2(), 10);
    assert_eq!(a.foo3(), 133);
    assert_eq!(a.foo4(), 16);
    assert_eq!(a.into_from_foo1(), Foo(1));
    assert_eq!(a.into_foo2(), Foo(2));
    assert_eq!(a.from_foo3(), 3);
}

mod some_module {
    use bitfield::bitfield;
    bitfield! {
        pub(super) struct PubBitFieldInAModule(u32);
        impl Debug;
        /// Attribute works on pub fields
        pub field1, set_field1: 1;
        pub field2, _: 1;
        pub _, set_field3: 1;
        pub u16, field4, set_field4: 1;
        /// Check if multiple attributes are applied
        #[cfg(not(test))]
        pub u16, field4, set_field4: 1;
        pub u16, _, set_field5: 1;
        pub u16, field6, _: 1;
        pub field7, set_field7: 1;
        pub field8, set_field8: 1, 1;
        #[cfg(not(test))]
        /// And make sure not only the last attributes is applied
        pub field8, set_field8: 1, 1;
        pub field9, set_field9: 1, 1, 1;
        pub u32, field10, set_field10: 1;
        pub u32, field11, set_field11: 1, 1;
        pub u32, field12, set_field12: 1, 1, 1;
    }
}

#[test]
fn struct_can_be_public() {
    let _ = some_module::PubBitFieldInAModule(0);
}
#[test]
fn field_can_be_public() {
    let mut a = some_module::PubBitFieldInAModule(0);
    let _ = a.field1();
    a.set_field1(true);
    let _ = a.field2();
    a.set_field3(true);
    let _ = a.field4();
    a.set_field4(true);
    a.set_field5(true);
    let _ = a.field6();
    let _ = a.field7();
    a.set_field7(true);
    let _ = a.field8();
    a.set_field8(0);
    let _ = a.field9(0);
    a.set_field9(0, 0);
    let _ = a.field10();
    a.set_field10(true);
    let _ = a.field11();
    a.set_field11(0);
    let _ = a.field12(0);
    a.set_field12(0, 0);
}

// Everything in this module is to make sure that its possible to specify types
// in most of the possible ways.
#[allow(dead_code)]
mod test_types {
    use bitfield::{bitfield_fields, BitRange, BitRangeMut};
    use std::sync::atomic::{self, AtomicUsize};

    struct Foo;

    impl Foo {
        bitfield_fields! {
            std::sync::atomic::AtomicUsize, field1, set_field1: 0, 0;
            std::sync::atomic::AtomicUsize;
            field2, set_field2: 0, 0;
            ::std::sync::atomic::AtomicUsize, field3, set_field3: 0, 0;
            ::std::sync::atomic::AtomicUsize;
            field4, set_field4: 0, 0;
            atomic::AtomicUsize, field5, set_field5: 0, 0;
            atomic::AtomicUsize;
            field6, set_field6: 0, 0;
            AtomicUsize, field7, set_field7: 0, 0;
            AtomicUsize;
            field8, set_field8: 0, 0;
            Vec<std::sync::atomic::AtomicUsize>, field9, set_field9: 0, 0;
            Vec<std::sync::atomic::AtomicUsize>;
            field10, set_field10: 0, 0;
            Vec<::std::sync::atomic::AtomicUsize>, field11, set_field11: 0, 0;
            Vec<::std::sync::atomic::AtomicUsize>;
            field12, set_field12: 0, 0;
            Vec<atomic::AtomicUsize>, field13, set_field13: 0, 0;
            Vec<atomic::AtomicUsize>;
            field14, set_field14: 0, 0;
            Vec<AtomicUsize>, field15, set_field15: 0, 0;
            Vec<AtomicUsize>;
            field16, set_field16: 0, 0;
            &str, field17, set_field17: 0, 0;
            &str;
            field18, set_field18: 0, 0;
            &'static str, field19, set_field19: 0, 0;
            &'static str;
            field20, set_field20: 0, 0;
        }
    }

    impl BitRange<AtomicUsize> for Foo {
        fn bit_range(&self, _msb: usize, _lsb: usize) -> AtomicUsize {
            AtomicUsize::new(0)
        }
    }

    impl BitRangeMut<AtomicUsize> for Foo {
        fn set_bit_range(&mut self, _msb: usize, _lsb: usize, _value: AtomicUsize) {}
    }

    impl BitRange<Vec<AtomicUsize>> for Foo {
        fn bit_range(&self, _msb: usize, _lsb: usize) -> Vec<AtomicUsize> {
            vec![AtomicUsize::new(0)]
        }
    }

    impl BitRangeMut<Vec<AtomicUsize>> for Foo {
        fn set_bit_range(&mut self, _msb: usize, _lsb: usize, _value: Vec<AtomicUsize>) {}
    }

    impl<'a> BitRange<&'a str> for Foo {
        fn bit_range(&self, _msb: usize, _lsb: usize) -> &'a str {
            ""
        }
    }

    impl<'a> BitRangeMut<&'a str> for Foo {
        fn set_bit_range(&mut self, _msb: usize, _lsb: usize, _value: &'a str) {}
    }

    #[test]
    fn test_field_type() {
        let test = Foo;
        let _: AtomicUsize = test.field1();
        let _: AtomicUsize = test.field2();
        let _: AtomicUsize = test.field3();
        let _: AtomicUsize = test.field4();
        let _: AtomicUsize = test.field5();
        let _: AtomicUsize = test.field6();
        let _: AtomicUsize = test.field7();
        let _: AtomicUsize = test.field8();
        let _: Vec<AtomicUsize> = test.field9();
        let _: Vec<AtomicUsize> = test.field10();
        let _: Vec<AtomicUsize> = test.field11();
        let _: Vec<AtomicUsize> = test.field12();
        let _: Vec<AtomicUsize> = test.field13();
        let _: Vec<AtomicUsize> = test.field14();
        let _: Vec<AtomicUsize> = test.field15();
        let _: Vec<AtomicUsize> = test.field16();
        let _: &str = test.field17();
        let _: &str = test.field18();
        let _: &'static str = test.field19();
        let _: &'static str = test.field20();
    }
}

#[allow(dead_code)]
mod test_no_default_bitrange {
    use bitfield::{bitfield, BitRange, BitRangeMut};
    use std::fmt::Debug;
    use std::fmt::Error;
    use std::fmt::Formatter;

    use crate::FooBar;
    bitfield! {
      #[derive(Eq, PartialEq)]
      pub struct BitField1(u16);
      no default BitRange;
      impl Debug;
      u8;
      field1, set_field1: 10, 0;
      pub field2, _ : 12, 3;
      field3, set_field3: 2;
    }

    impl BitRange<u8> for BitField1 {
        fn bit_range(&self, msb: usize, lsb: usize) -> u8 {
            (msb + lsb) as u8
        }
    }

    impl BitRangeMut<u8> for BitField1 {
        fn set_bit_range(&mut self, msb: usize, lsb: usize, value: u8) {
            self.0 = msb as u16 + lsb as u16 + u16::from(value)
        }
    }

    #[allow(clippy::identity_op)]
    #[test]
    fn custom_bitrange_implementation_is_used() {
        let mut bf = BitField1(0);
        assert_eq!(bf.field1(), 10 + 0);
        assert_eq!(bf.field2(), 12 + 3);
        assert!(bf.field3());
        bf.set_field1(42);
        assert_eq!(bf, BitField1(10 + 0 + 42));
    }

    bitfield! {
      pub(crate) struct BitField2(u16);
      no default BitRange;
      u8;
      field1, set_field1: 10, 0;
      pub field2, _ : 12, 3;
      field3, set_field3: 0;
    }

    impl BitRange<u8> for BitField2 {
        fn bit_range(&self, _msb: usize, _lsb: usize) -> u8 {
            0
        }
    }

    impl BitRangeMut<u8> for BitField2 {
        fn set_bit_range(&mut self, _msb: usize, _lsb: usize, _value: u8) {}
    }

    // Make sure Debug wasn't implemented by implementing it.
    impl Debug for BitField2 {
        fn fmt(&self, _: &mut Formatter) -> Result<(), Error> {
            unimplemented!()
        }
    }

    // Check that we can put `impl Debug` before `no default BitRange`
    bitfield! {
      pub struct BitField3(u16);
      impl Debug;
      no default BitRange;
      u8;
      field1, set_field1: 10, 0;
      pub field2, _ : 12, 3;
      field3, set_field3: 0;
    }

    impl BitRange<u8> for BitField3 {
        fn bit_range(&self, _msb: usize, _lsb: usize) -> u8 {
            0
        }
    }

    impl BitRangeMut<u8> for BitField3 {
        fn set_bit_range(&mut self, _msb: usize, _lsb: usize, _value: u8) {}
    }

    bitfield! {
      #[derive(Eq, PartialEq)]
      pub struct BitField4([u16]);
      no default BitRange;
      impl Debug;
      u8;
      field1, set_field1: 10, 0;
      pub field2, _ : 12, 3;
      field3, set_field3: 2;
    }

    impl<T> BitRange<u8> for BitField4<T> {
        fn bit_range(&self, _msb: usize, _lsb: usize) -> u8 {
            0
        }
    }

    impl<T> BitRangeMut<u8> for BitField4<T> {
        fn set_bit_range(&mut self, _msb: usize, _lsb: usize, _value: u8) {}
    }

    bitfield! {
      pub struct BitField5([u16]);
      no default BitRange;
      u8;
      field1, set_field1: 10, 0;
      pub field2, _ : 12, 3;
      field3, set_field3: 0;
    }

    impl<T> BitRange<u8> for BitField5<T> {
        fn bit_range(&self, _msb: usize, _lsb: usize) -> u8 {
            0
        }
    }

    impl<T> BitRangeMut<u8> for BitField5<T> {
        fn set_bit_range(&mut self, _msb: usize, _lsb: usize, _value: u8) {}
    }

    // Make sure Debug wasn't implemented by implementing it.
    impl<T> Debug for BitField5<T> {
        fn fmt(&self, _: &mut Formatter) -> Result<(), Error> {
            unimplemented!()
        }
    }

    // Check that we can put `impl Debug` before `no default BitRange`
    bitfield! {
      pub struct BitField6([u16]);
      impl Debug;
      no default BitRange;
      u8;
      field1, set_field1: 10, 0;
      pub field2, _ : 12, 3;
      field3, set_field3: 0;
    }

    impl<T> BitRange<u8> for BitField6<T> {
        fn bit_range(&self, _msb: usize, _lsb: usize) -> u8 {
            0
        }
    }

    impl<T> BitRangeMut<u8> for BitField6<T> {
        fn set_bit_range(&mut self, _msb: usize, _lsb: usize, _value: u8) {}
    }

    bitfield! {
      #[derive(Eq, PartialEq)]
      pub struct BitField7(MSB0 [u16]);
      no default BitRange;
      impl Debug;
      u8;
      field1, set_field1: 10, 0;
      pub field2, _ : 12, 3;
      field3, set_field3: 2;
    }

    impl<T> BitRange<u8> for BitField7<T> {
        fn bit_range(&self, _msb: usize, _lsb: usize) -> u8 {
            0
        }
    }

    impl<T> BitRangeMut<u8> for BitField7<T> {
        fn set_bit_range(&mut self, _msb: usize, _lsb: usize, _value: u8) {}
    }

    bitfield! {
      pub struct BitField8(MSB0 [u16]);
      no default BitRange;
      u8;
      field1, set_field1: 10, 0;
      pub field2, _ : 12, 3;
      field3, set_field3: 0;
    }

    impl<T> BitRange<u8> for BitField8<T> {
        fn bit_range(&self, _msb: usize, _lsb: usize) -> u8 {
            0
        }
    }

    impl<T> BitRangeMut<u8> for BitField8<T> {
        fn set_bit_range(&mut self, _msb: usize, _lsb: usize, _value: u8) {}
    }

    // Make sure Debug wasn't implemented by implementing it.
    impl<T> Debug for BitField8<T> {
        fn fmt(&self, _: &mut Formatter) -> Result<(), Error> {
            unimplemented!()
        }
    }

    // Check that we can put `impl Debug` before `no default BitRange`
    bitfield! {
      pub struct BitField9([u16]);
      impl Debug;
      no default BitRange;
      u8;
      field1, set_field1: 10, 0;
      pub field2, _ : 12, 3;
      field3, set_field3: 0;
    }

    impl<T> BitRange<u8> for BitField9<T> {
        fn bit_range(&self, _msb: usize, _lsb: usize) -> u8 {
            0
        }
    }

    impl<T> BitRangeMut<u8> for BitField9<T> {
        fn set_bit_range(&mut self, _msb: usize, _lsb: usize, _value: u8) {}
    }

    #[test]
    fn test_debug_is_implemented_with_no_default_bitrange() {
        let _ = format!("{:?}", BitField1(0));
        let _ = format!("{:?}", BitField3(0));
        let _ = format!("{:?}", BitField4([0; 1]));
        let _ = format!("{:?}", BitField6([0; 1]));
        let _ = format!("{:?}", BitField7([0; 1]));
        let _ = format!("{:?}", BitField9([0; 1]));
    }

    #[test]
    fn masks() {
        assert_eq!(FooBar::I128_MASK, 0b111111110i128);
        assert_eq!(FooBar::U128_MASK, 0b111111110u128);
        assert_eq!(FooBar::SETTER_MASK, 0b11100u32);
        assert_eq!(FooBar::GETTER_MASK, 0b1110u32);
        assert_eq!(FooBar::PUB_SETTER_MASK, 0b11100u32);
        assert_eq!(FooBar::PUB_GETTER_MASK, 0b1110u32);
        assert_eq!(FooBar::SINGLE_BIT_MASK, 1 << 3);
        assert_eq!(FooBar::PUB_MASK, 1 << 31);
    }
}

#[deny(missing_docs)]
/// A module to test that `impl new` works with `#[deny(missing_docs)]`
pub mod deny_missing_docs {
    use bitfield::bitfield;

    bitfield! {
        /// A doc comment for the struct
        pub struct BitField10(u8);

        impl new;

        /// A doc comment for the methods
        pub field1, set_field1: 0;
    }
}

bitfield! {
    #[derive(Copy, Clone)]
    /// documentation comments also work!
    struct FooBarSigned(i32);
    impl Debug;
    impl BitOr;
    foo1, set_foo1: 31, 8;
    foo2, set_foo2: 10, 10, 2;
    mask A_MASK(u32), foo3, set_foo3: 3, 1;
    u8;
    foo4, set_foo4: THREE, 0;
    u32, foo5, set_foo5: 31,8;
}

#[test]
fn field_type_signed() {
    let fbs = FooBarSigned(0);
    let _: i32 = fbs.foo1();
    let _: i32 = fbs.foo2(0);
    let _: i32 = fbs.foo3();
    let _: u8 = fbs.foo4();
    let _: u32 = fbs.foo5();
}

#[test]
fn value_signed() {
    let initial_value = 0b1101_0101_1010_1010_1010_1010_0110_0010u32 as i32;
    let fbs = FooBarSigned(initial_value);
    assert_eq!(
        fbs.foo1(),
        0b1111_1111_1101_0101_1010_1010_1010_1010u32 as i32
    );
    assert_eq!(fbs.foo5(), 0b1101_0101_1010_1010_1010_1010u32);
}

#[test]
fn mask_signed() {
    assert_eq!(FooBarSigned::A_MASK, 0b1110u32);
}
