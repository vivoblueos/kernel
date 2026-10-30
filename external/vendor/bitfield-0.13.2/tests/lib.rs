#![recursion_limit = "128"]

#[macro_use]
extern crate bitfield;

// We use a constant to make sure bits positions don't need to be literals but
// can also be constants or expressions.
const THREE: usize = 3;

#[derive(Copy, Clone, Debug)]
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

bitfield! {
    #[derive(Copy, Clone)]
    /// documentation comments also work!
    struct FooBar(u32);
    impl Debug;
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
    getter_only, _: 3, 1;
    _, setter_only: 2*2, 2;
    getter_only_array, _: 5, 3, 3;
    _, setter_only_array: 2*THREE, 4, 3;
    all_bits, set_all_bits: 31, 0;
    single_bit, set_single_bit: 3;
    u8, into Foo, into_foo1, set_into_foo1: 31, 31;
    pub u8, into Foo, into_foo2, set_into_foo2: 31, 31;
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
    i8;
    signed_single_bit, set_signed_single_bit: 0, 0;
    signed_two_bits, set_signed_two_bits: 1, 0;
    signed_eight_bits, set_signed_eight_bits: 7, 0;
    signed_eight_bits_unaligned, set_signed_eight_bits_unaligned: 8, 1;
    u128, u128_getter, set_u128: 8, 1;
    i128, i128_getter, set_i128: 8, 1;
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
}

#[test]
fn test_single_bit() {
    let mut fb = FooBar(0);

    fb.set_foo1(1);
    assert_eq!(0x1, fb.0);
    assert_eq!(0x1, fb.foo1());
    assert_eq!(0x0, fb.foo2());
    assert_eq!(false, fb.single_bit());
    assert_eq!(-1, fb.signed_single_bit());

    fb.set_foo2(1);
    assert_eq!(0x8000_0001, fb.0);
    assert_eq!(0x1, fb.foo1());
    assert_eq!(0x1, fb.foo2());
    assert_eq!(false, fb.single_bit());
    assert_eq!(-1, fb.signed_single_bit());

    fb.set_foo1(0);
    assert_eq!(0x8000_0000, fb.0);
    assert_eq!(0x0, fb.foo1());
    assert_eq!(0x1, fb.foo2());
    assert_eq!(false, fb.single_bit());
    assert_eq!(0, fb.signed_single_bit());

    fb.set_single_bit(true);
    assert_eq!(0x8000_0008, fb.0);
    assert_eq!(0x0, fb.foo1());
    assert_eq!(0x1, fb.foo2());
    assert_eq!(true, fb.single_bit());
    assert_eq!(0, fb.signed_single_bit());

    fb.set_signed_single_bit(-1);
    assert_eq!(0x8000_0009, fb.0);
    assert_eq!(0x1, fb.foo1());
    assert_eq!(0x1, fb.foo2());
    assert_eq!(true, fb.single_bit());
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

#[allow(unknown_lints)]
#[allow(identity_op)]
#[allow(erasing_op)]
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
    let expected = "FooBar { .0: 1234567890, foo1: 0, foo2: 0, foo3: 2, foo3: 2, foo4: 4, foo5: [0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0], foo6: [2, 3, 1], getter_only: 1, getter_only_array: [2, 3, 1], all_bits: 1234567890, single_bit: false, into_foo1: Foo(0), into_foo2: Foo(0), from_foo1: Foo(0), into_foo3: Foo(0), into_foo4: Foo(0), into_foo6: [Foo(0), Foo(1), Foo(0)], from_foo3: Foo(0), from_foo5: [Foo(0), Foo(1), Foo(0)], from_foo6: Foo(0), signed_single_bit: 0, signed_two_bits: -2, signed_eight_bits: -46, signed_eight_bits_unaligned: 105, u128_getter: 105, i128_getter: 105 }";
    assert_eq!(expected, format!("{:?}", fb))
}

bitfield! {
    struct ArrayBitfield([u8]);
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
    struct ArrayBitfieldMsb0(MSB0 [u8]);
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

mod some_module {
    bitfield! {
        pub struct PubBitFieldInAModule(u32);
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
    use bitfield::BitRange;
    use std;
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
        fn set_bit_range(&mut self, _msb: usize, _lsb: usize, _value: AtomicUsize) {}
    }

    impl BitRange<Vec<AtomicUsize>> for Foo {
        fn bit_range(&self, _msb: usize, _lsb: usize) -> Vec<AtomicUsize> {
            vec![AtomicUsize::new(0)]
        }
        fn set_bit_range(&mut self, _msb: usize, _lsb: usize, _value: Vec<AtomicUsize>) {}
    }

    impl<'a> BitRange<&'a str> for Foo {
        fn bit_range(&self, _msb: usize, _lsb: usize) -> &'a str {
            ""
        }
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
    use bitfield::BitRange;
    use std::fmt::Debug;
    use std::fmt::Error;
    use std::fmt::Formatter;
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
        fn set_bit_range(&mut self, msb: usize, lsb: usize, value: u8) {
            self.0 = msb as u16 + lsb as u16 + u16::from(value)
        }
    }

    #[allow(unknown_lints)]
    #[allow(identity_op)]
    #[test]
    fn custom_bitrange_implementation_is_used() {
        let mut bf = BitField1(0);
        assert_eq!(bf.field1(), 10 + 0);
        assert_eq!(bf.field2(), 12 + 3);
        assert_eq!(bf.field3(), true);
        bf.set_field1(42);
        assert_eq!(bf, BitField1(10 + 0 + 42));
    }

    bitfield! {
      pub struct BitField2(u16);
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
        fn set_bit_range(&mut self, _msb: usize, _lsb: usize, _value: u8) {}
    }

    #[test]
    fn test_debug_is_implemented_with_no_default_bitrange() {
        format!("{:?}", BitField1(0));
        format!("{:?}", BitField3(0));
        format!("{:?}", BitField4([0; 1]));
        format!("{:?}", BitField6([0; 1]));
        format!("{:?}", BitField7([0; 1]));
        format!("{:?}", BitField9([0; 1]));
    }
}
