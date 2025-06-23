use chumsky::Parser;
use chumsky_helpers::stateful_strings::{cooked_string, interpolated_string, raw_multi_line, raw_single_line, Segment};

#[test]
fn raw_single_line_zero_hash() {
    let out = raw_single_line().parse("\"hello\"").into_result().unwrap();
    assert_eq!(out, "hello");
}

#[test]
fn raw_single_line_three_hashes() {
    let out = raw_single_line().parse("###\"abc\"###").into_result().unwrap();
    assert_eq!(out, "abc");
}

#[test]
fn raw_missing_closing_delimiter_is_error() {
    assert!(raw_single_line().parse("##\"abc").has_errors());
}

#[test]
fn raw_multi_line_indent_preserved_for_now() {
    let src = "#\"\"\"\n    foo\n    bar\n    \"\"\"#";
    let out = raw_multi_line().parse(src).into_result().unwrap();
    // Until indent stripping is implemented we expect the leading spaces.
    assert_eq!(out, "\n    foo\n    bar\n");
}

#[test]
fn cooked_basic_escapes() {
    let out = cooked_string().parse("\"a\\n\\t\\\"b\"").into_result().unwrap();
    assert_eq!(out, "a\n\t\"b");
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
