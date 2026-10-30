use indoc::indoc;

#[test]
fn c_string() {
    let indoc = indoc! {c"
        a

            \\b
        c"
    };
    let expected = c"a\n\n    \\b\nc";
    assert_eq!(indoc, expected);
}

#[test]
fn raw_c_string() {
    let indoc = indoc! {cr#"
        "a"

            \\b
        c"#
    };
    let expected = c"\"a\"\n\n    \\\\b\nc";
    assert_eq!(indoc, expected);
}
