use chumsky::Parser;
mod common;

use chumsky_helpers::stateful_strings::Lang;
use chumsky_helpers::stateful_strings::{Segment, StringParserConfig};
// (indoc not currently used; left in dev-dependencies for future multi-line test cases)

// Input / expected pairs for raw strings.
const RAW_CASES: &[(&str, &str)] = &[("\"hello\"", "hello"), ("###\"abc\"###", "abc")];

#[test]
fn raw_single_line_cases() {
    let cfg = StringParserConfig::default();
    for (src, want) in RAW_CASES {
        assert_parses_to!(cfg.raw_single_line(), src, *want);
    }
}

#[test]
fn raw_missing_closing_delimiter_is_error() {
    let cfg = StringParserConfig::default();
    assert_fails!(cfg.raw_single_line(), "##\"abc");
}

#[test]
fn raw_multi_line_indent_preserved_for_now() {
    let src = "#\"\"\"\n    foo\n    bar\n    \"\"\"#";
    let cfg = StringParserConfig::default();
    assert_parses_to!(cfg.raw_multi_line(), src, "\nfoo\nbar\n");
}

#[test]
fn raw_multi_line_no_strip_indent() {
    let src = "#\"\"\"\n    foo\n    bar\n    \"\"\"#";
    let cfg = StringParserConfig::builder()
        .lang(Lang::Rust)
        .strip_indent(false)
        .build();
    assert_parses_to!(cfg.raw_multi_line(), src, "\n    foo\n    bar\n");
}

#[test]
fn cooked_basic_escapes() {
    let cfg = StringParserConfig::default();
    assert_parses_to!(cfg.cooked_string(), "\"a\\n\\t\\\"b\"", "a\n\t\"b");
}

#[test]
fn interpolation_basic() {
    let cfg = StringParserConfig::default();
    let parts = cfg
        .interpolated_string()
        .parse("foo \\#(bar + 1) baz")
        .into_result()
        .unwrap();
    assert_eq!(
        parts,
        vec![Segment::Text("foo "), Segment::Expr("bar + 1"), Segment::Text(" baz")]
    );
}
