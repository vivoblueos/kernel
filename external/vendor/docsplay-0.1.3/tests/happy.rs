use docsplay::Display;

#[cfg(feature = "std")]
use std::path::PathBuf;

use std::ops::Range;

#[derive(Display)]
/// Just a basic struct {thing}
struct HappyStruct {
    thing: &'static str,
}

#[derive(Display)]
#[ignore_extra_doc_attributes]
/// Just a basic struct {thing}
/// and this line should get ignored
struct HappyStruct2 {
    thing: &'static str,
}

#[derive(Display)]
enum Happy {
    /// I really like Variant1
    Variant1,
    /// Variant2 is pretty swell 2
    Variant2,
    /// Variant3 is okay {sometimes}
    Variant3 { sometimes: &'static str },
    /**
     * Variant4 wants to have a lot of lines
     *
     * Lets see how this works out for it
     */
    Variant4,
    /// Variant5 has a parameter {0} and some regular comments
    // A regular comment that won't get picked
    Variant5(u32),

    /// The path {0}
    #[cfg(feature = "std")]
    Variant6(PathBuf),

    /// These docs are ignored
    #[display("Variant7 has a parameter {0} and uses #[display]")]
    /// These docs are also ignored
    Variant7(u32),

    /// {range.start} to {range.end}
    Variant8 { range: Range<u32> },

    /// These docs are ignored
    #[display("Variant9 has a range: {range.start} to {range.end}")]
    Variant9 { range: Range<u32> },

    /// Variant9 has a range:
    /// {range.start}
    /// {range.end}
    Variant10 { range: Range<u32> },
}

// Used for testing indented doc comments
mod inner_mod {
    use super::Display;

    #[derive(Display)]
    pub enum InnerHappy {
        /// I really like Variant1
        Variant1,
        /// Variant2 is pretty swell 2
        Variant2,
        /// Variant3 is okay {sometimes}
        Variant3 { sometimes: &'static str },
        /**
         * Variant4 wants to have a lot of lines
         *
         * Lets see how this works out for it
         */
        Variant4,
        /// Variant5 has a parameter {0} and some regular comments
        // A regular comment that won't get picked
        Variant5(u32),

        /** what happens if we
         * put text on the first line?
         */
        Variant6,

        /**
        what happens if we don't use *?
        */
        Variant7,

        /**
         *
         * what about extra new lines?
         */
        Variant8,

        /// what about
        /// multiple lines?
        ///
        /// multiple paragraphs?
        Variant9,

        /// what about
        /// multiple lines?
        ///
        /// multiple paragraphs? but only first one should be used
        #[ignore_extra_doc_attributes]
        Variant10,
    }
}

fn assert_display<T: std::fmt::Display>(input: T, expected: &'static str) {
    use pretty_assertions::assert_eq;
    let out = format!("{}", input);
    assert_eq!(expected, out);
}

#[test]
fn does_it_print() {
    assert_display(Happy::Variant1, "I really like Variant1");
    assert_display(Happy::Variant2, "Variant2 is pretty swell 2");
    assert_display(Happy::Variant3 { sometimes: "hi" }, "Variant3 is okay hi");
    assert_display(
        Happy::Variant4,
        "Variant4 wants to have a lot of lines\n\nLets see how this works out for it",
    );
    assert_display(
        Happy::Variant5(2),
        "Variant5 has a parameter 2 and some regular comments",
    );
    assert_display(
        Happy::Variant7(2),
        "Variant7 has a parameter 2 and uses #[display]",
    );

    assert_display(Happy::Variant8 { range: 1..4 }, "1 to 4");
    assert_display(
        Happy::Variant9 { range: 1..4 },
        "Variant9 has a range: 1 to 4",
    );
    assert_display(
        Happy::Variant10 { range: 1..4 },
        "Variant9 has a range:\n1\n4",
    );

    assert_display(HappyStruct { thing: "hi" }, "Just a basic struct hi");

    assert_display(HappyStruct2 { thing: "hi2" }, "Just a basic struct hi2");

    assert_display(inner_mod::InnerHappy::Variant1, "I really like Variant1");
    assert_display(
        inner_mod::InnerHappy::Variant2,
        "Variant2 is pretty swell 2",
    );
    assert_display(
        inner_mod::InnerHappy::Variant3 { sometimes: "hi" },
        "Variant3 is okay hi",
    );
    assert_display(
        inner_mod::InnerHappy::Variant4,
        "Variant4 wants to have a lot of lines\n\nLets see how this works out for it",
    );
    assert_display(
        inner_mod::InnerHappy::Variant5(2),
        "Variant5 has a parameter 2 and some regular comments",
    );
    assert_display(
        inner_mod::InnerHappy::Variant6,
        "what happens if we\nput text on the first line?",
    );
    assert_display(
        inner_mod::InnerHappy::Variant7,
        "what happens if we don\'t use *?",
    );
    assert_display(
        inner_mod::InnerHappy::Variant8,
        "what about extra new lines?",
    );
    assert_display(
        inner_mod::InnerHappy::Variant9,
        "what about\nmultiple lines?\n\nmultiple paragraphs?",
    );
    assert_display(inner_mod::InnerHappy::Variant10, "what about");
}

#[test]
#[cfg(feature = "std")]
fn does_it_print_path() {
    assert_display(
        Happy::Variant6(PathBuf::from("/var/log/happy")),
        "The path /var/log/happy",
    );
}
