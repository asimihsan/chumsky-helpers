use chumsky::Parser;
mod common;

use chumsky_helpers::stateful_strings::{cooked_string, interpolated_string, raw_multi_line, raw_single_line, Segment};
// (indoc not currently used; left in dev-dependencies for future multi-line test cases)

// Input / expected pairs for raw strings.
const RAW_CASES: &[(&str, &str)] = &[
    ("\"hello\"", "hello"),
    ("###\"abc\"###", "abc"),
];

#[test]
fn raw_single_line_cases() {
    for (src, want) in RAW_CASES {
        assert_parses_to!(raw_single_line(), src, *want);
    }
}

#[test]
fn raw_missing_closing_delimiter_is_error() {
    assert_fails!(raw_single_line(), "##\"abc");
}

#[test]
fn raw_multi_line_indent_preserved_for_now() {
    let src = "#\"\"\"\n    foo\n    bar\n    \"\"\"#";
    assert_parses_to!(raw_multi_line(), src, "\n    foo\n    bar\n");
}

#[test]
fn cooked_basic_escapes() {
    assert_parses_to!(cooked_string(), "\"a\\n\\t\\\"b\"", "a\n\t\"b");
}

#[test]
fn interpolation_basic() {
    let parts = interpolated_string()
        .parse("foo \\#(bar + 1) baz")
        .into_result()
        .unwrap();
    assert_eq!(
        parts,
        vec![Segment::Text("foo "), Segment::Expr("bar + 1"), Segment::Text(" baz")]
    );
}
