#[allow(unused_attributes)]
#[cfg(feature = "std")]
#[rustversion::attr(not(nightly), ignore)]
#[test]
fn compile_test_std() {
    let t = trybuild::TestCases::new();

    t.pass("tests/no_std/enum_prefix.rs");
    t.pass("tests/no_std/multi_line_allow.rs");
    t.pass("tests/no_std/multi_line.rs");
    t.pass("tests/no_std/multiple.rs");
    t.pass("tests/no_std/with.rs");

    t.compile_fail("tests/std/without.rs");
    t.compile_fail("tests/std/enum_prefix_missing.rs");
}

#[allow(unused_attributes)]
#[cfg(not(feature = "std"))]
#[rustversion::attr(not(nightly), ignore)]
#[test]
fn compile_test_no_std() {
    let t = trybuild::TestCases::new();

    t.pass("tests/no_std/enum_prefix.rs");
    t.pass("tests/no_std/multi_line_allow.rs");
    t.pass("tests/no_std/multi_line.rs");
    t.pass("tests/no_std/multiple.rs");
    t.pass("tests/no_std/with.rs");

    t.compile_fail("tests/no_std/without.rs");
    t.compile_fail("tests/no_std/enum_prefix_missing.rs");
}
