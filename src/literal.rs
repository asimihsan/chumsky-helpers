// Copyright 2025 Asim Ihsan
//
// This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
// If a copy of the MPL was not distributed with this file, You can obtain one at https://mozilla.org/MPL/2.0/.
//
// SPDX-License-Identifier: MPL-2.0

//! # Literal Parsing
//!
//! This module provides parsers for literal values, including string literals with different
//! quoting styles and number literals. The literal parser is configurable, allowing you to
//! control which types of string literals are supported.
//!
//! ## Features
//!
//! * Parse double-quoted string literals with escape sequences (`"hello\nworld"`)
//! * Optionally parse single-quoted string literals (`'hello\tworld'`)
//! * Optionally parse raw string literals (`` `raw string` ``)
//! * Parse number literals (integers, floats, scientific notation)
//! * Error reporting with clear messages and spans
//!
//! ## Examples
//!
//! ```
//! use chumsky_helpers::literal::{LiteralParserBuilder, Expr};
//! use chumsky::prelude::*;
//!
//! // Create a parser that allows all string literal styles
//! let parser = LiteralParserBuilder::new()
//!     .single_quote(true)
//!     .raw_string(true)
//!     .build();
//!
//! // Parse a double-quoted string with escape sequences
//! let result = parser.parse("\"hello\\nworld\"").into_result().unwrap();
//! match result {
//!     Expr::LiteralStr((s, _)) => assert_eq!(s, "hello\nworld"),
//!     _ => panic!("Expected string literal"),
//! }
//!
//! // Parse a single-quoted string
//! let result = parser.parse("'escaped \\'quote\\''").into_result().unwrap();
//! match result {
//!     Expr::LiteralStr((s, _)) => assert_eq!(s, "escaped 'quote'"),
//!     _ => panic!("Expected string literal"),
//! }
//!
//! // Parse a raw string
//! let result = parser.parse("`raw \\n string`").into_result().unwrap();
//! match result {
//!     Expr::LiteralStr((s, _)) => assert_eq!(s, "raw \\n string"),
//!     _ => panic!("Expected string literal"),
//! }
//!
//! // Parse a number
//! let result = parser.parse("42").into_result().unwrap();
//! match result {
//!     Expr::LiteralNum(_) => (),
//!     _ => panic!("Expected number literal"),
//! }
//! ```

use crate::number::{NumberParserBuilder, NumberValue};
use crate::Spanned;
use chumsky::{error::Rich, prelude::*};

/// Represents a parsed literal expression.
///
/// This enum captures the result of parsing a literal value, which can be
/// a string, a number, or an error (used when a disallowed literal type is encountered).
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// An error with a message and span, used when a disallowed literal type is encountered.
    Error(Spanned<String>),

    /// A string literal with its value and span.
    LiteralStr(Spanned<String>),

    /// A numeric literal with its value and span.
    LiteralNum(Spanned<NumberValue>),
}

/// Builder for configuring and creating a literal parser.
///
/// This builder allows you to customize which types of string literals are
/// allowed in the parser, such as single-quoted strings and raw strings.
#[derive(Debug, Default)]
pub struct LiteralParserBuilder {
    allow_single_quote: bool,
    allow_raw_string: bool,
}

impl LiteralParserBuilder {
    /// Create a new builder with default settings.
    ///
    /// By default, double-quoted strings are always allowed, but
    /// single-quoted strings and raw strings are disabled and must
    /// be explicitly enabled.
    pub fn new() -> Self {
        Self::default()
    }

    /// Configure whether single-quoted strings are allowed.
    ///
    /// When enabled, the parser will accept strings like `'hello\tworld'`.
    /// When disabled, these will be parsed as `Expr::Error` with an appropriate message.
    pub fn single_quote(mut self, allow: bool) -> Self {
        self.allow_single_quote = allow;
        self
    }

    /// Configure whether raw strings are allowed.
    ///
    /// When enabled, the parser will accept strings like `` `raw string` ``.
    /// When disabled, these will be parsed as `Expr::Error` with an appropriate message.
    pub fn raw_string(mut self, allow: bool) -> Self {
        self.allow_raw_string = allow;
        self
    }

    /// Build the configured literal parser.
    ///
    /// Creates a parser based on the current configuration that can
    /// parse literal values into the `Expr` enum. Double-quoted strings
    /// and numbers are always supported, while single-quoted strings and
    /// raw strings can be enabled or disabled.
    pub fn build<'a>(self) -> impl Parser<'a, &'a str, Expr, extra::Err<Rich<'a, char>>> {
        // Number parser with span
        let number = NumberParserBuilder::new()
            .negative(true)
            .rational(true)
            .scientific(true)
            .build()
            .map_with(|n, e| Expr::LiteralNum((n, e.span())));

        // Double-quoted strings with span
        let normal_dq = none_of("\\\"").map(|c: char| c.to_string());
        let escaped_dq = just("\\")
            .ignore_then(choice((
                just("\\").to("\\"),
                just("/").to("/"),
                just("\"").to("\""),
                just("n").to("\n"),
                just("r").to("\r"),
                just("t").to("\t"),
            )))
            .map(|s: &str| s.to_string());

        let dq_content =
            choice((normal_dq, escaped_dq)).repeated().collect::<Vec<String>>().map(|v| v.concat());

        let double_quoted = just("\"")
            .ignore_then(dq_content)
            .then_ignore(just('"').or_not().try_map(|opt_quote, span| {
                opt_quote.ok_or_else(|| Rich::custom(span, "Unclosed double quote"))
            }))
            .map_with(|s, e| Expr::LiteralStr((s, e.span())));

        // Raw string parser
        let raw_string = just("`")
            .ignore_then(none_of("`").repeated().collect::<String>())
            .then_ignore(just("`"))
            .map_with(move |s, e| {
                if self.allow_raw_string {
                    Expr::LiteralStr((s, e.span()))
                } else {
                    Expr::Error(("raw string literals are not allowed".to_string(), e.span()))
                }
            });

        // Single-quoted string parser
        let single_quoted = just("'")
            .ignore_then(
                choice((
                    none_of("\\'").map(|c: char| c.to_string()),
                    just("\\")
                        .ignore_then(choice((
                            just("\\").to("\\"),
                            just("'").to("'"),
                            just("n").to("\n"),
                            just("r").to("\r"),
                            just("t").to("\t"),
                        )))
                        .map(|s: &str| s.to_string()),
                ))
                .repeated()
                .collect::<Vec<_>>()
                .map(|v| v.concat()),
            )
            .then_ignore(just('\''))
            .map_with(move |s, e| {
                if self.allow_single_quote {
                    Expr::LiteralStr((s, e.span()))
                } else {
                    Expr::Error((
                        "single-quoted string literals are not allowed".to_string(),
                        e.span(),
                    ))
                }
            });

        choice((number, double_quoted, raw_string, single_quoted)).boxed()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::number::ExplicitSign;
    use chumsky::Parser;
    use num_bigint::BigInt;
    use proptest::prelude::*;

    #[test]
    fn test_double_quoted_literal() {
        let parser = LiteralParserBuilder::new().build();
        let input = r#""hello\nworld""#;
        let expected = Expr::LiteralStr(("hello\nworld".to_string(), (0..14).into()));
        assert_eq!(parser.parse(input).into_result(), Ok(expected));
    }

    #[test]
    fn test_invalid_double_quote_unclosed() {
        let parser = LiteralParserBuilder::new().build();
        let input = r#""unclosed string"#;
        assert!(parser.parse(input).has_errors());
    }

    #[test]
    fn test_number_literal() {
        let parser = LiteralParserBuilder::new().build();
        let input = "42";
        let expected = Expr::LiteralNum((
            NumberValue::new_integer(42, ExplicitSign::None),
            (0..2).into(),
        ));
        assert_eq!(parser.parse(input).into_result(), Ok(expected));
    }

    #[test]
    fn test_single_quoted_literal_allowed() {
        let parser = LiteralParserBuilder::new().single_quote(true).build();
        let input = r#"'hello\tworld'"#;
        let expected = Expr::LiteralStr(("hello\tworld".to_string(), (0..14).into()));
        assert_eq!(parser.parse(input).into_result(), Ok(expected));
    }

    #[test]
    fn test_single_quoted_literal_disallowed() {
        let parser = LiteralParserBuilder::new().single_quote(false).build();
        let input = r#"'hello'"#;
        match parser.parse(input).into_result() {
            Ok(Expr::Error((msg, _))) => {
                assert_eq!(msg, "single-quoted string literals are not allowed");
            }
            _ => panic!("Expected Expr::Error"),
        }
    }

    #[test]
    fn test_single_quoted_literal_disallowed_explicit() {
        // Create a parser with single-quoted strings disabled.
        let parser = LiteralParserBuilder::new().single_quote(false).build();
        let input = "'example'";
        // We expect the parser to return an error variant for single-quoted literals.
        match parser.parse(input).into_result() {
            Ok(Expr::Error((msg, span))) => {
                assert_eq!(msg, "single-quoted string literals are not allowed");
                // Optionally, verify that the span covers the input.
                assert_eq!(span, (0..input.len()).into());
            }
            other => panic!(
                "Expected Expr::Error for a disallowed single-quoted literal, got {:?}",
                other
            ),
        }
    }

    #[test]
    fn test_raw_string_literal_allowed() {
        let parser = LiteralParserBuilder::new().raw_string(true).build();
        let input = "`raw \\n string`";
        let expected = Expr::LiteralStr(("raw \\n string".to_string(), (0..15).into()));
        assert_eq!(parser.parse(input).into_result(), Ok(expected));
    }

    #[test]
    fn test_raw_string_literal_disallowed() {
        let parser = LiteralParserBuilder::new().raw_string(false).build();
        let input = "`raw string`";
        match parser.parse(input).into_result() {
            Ok(Expr::Error((msg, _))) => {
                assert_eq!(msg, "raw string literals are not allowed");
            }
            _ => panic!("Expected Expr::Error"),
        }
    }

    #[test]
    fn test_raw_string_literal_disallowed_explicit() {
        // Create a parser with raw strings disabled.
        let parser = LiteralParserBuilder::new().raw_string(false).build();
        let input = "`some raw string`";
        // We expect the parser to return an error variant for raw strings.
        match parser.parse(input).into_result() {
            Ok(Expr::Error((msg, span))) => {
                assert_eq!(msg, "raw string literals are not allowed");
                // Optionally, verify that the span covers the input (or a part of it)
                assert_eq!(span, (0..input.len()).into());
            }
            other => panic!(
                "Expected Expr::Error for a disallowed raw string literal, got {:?}",
                other
            ),
        }
    }

    #[test]
    fn test_empty_double_quoted_literal() {
        let parser = LiteralParserBuilder::new().build();
        // An empty double-quoted literal: ""
        let input = r#""""#;
        // The span covers both double quotes (0..2)
        let expected = Expr::LiteralStr(("".to_string(), (0..2).into()));
        assert_eq!(parser.parse(input).into_result(), Ok(expected));
    }

    #[test]
    fn test_empty_single_quoted_literal_allowed() {
        let parser = LiteralParserBuilder::new().single_quote(true).build();
        // An empty single-quoted literal: ''
        let input = "''";
        // The span covers both single quotes (0..2)
        let expected = Expr::LiteralStr(("".to_string(), (0..2).into()));
        assert_eq!(parser.parse(input).into_result(), Ok(expected));
    }

    #[test]
    fn test_empty_raw_string_literal_allowed() {
        let parser = LiteralParserBuilder::new().raw_string(true).build();
        // An empty raw string literal: ``
        let input = "``";
        // The span covers both backticks (0..2)
        let expected = Expr::LiteralStr(("".to_string(), (0..2).into()));
        assert_eq!(parser.parse(input).into_result(), Ok(expected));
    }

    #[test]
    fn test_error_unclosed_double_quoted() {
        let parser = LiteralParserBuilder::new().build();
        // Input with an unclosed double quote
        let input = r#""unclosed"#;
        match parser.parse(input).into_result() {
            Err(errs) => {
                // We expect one error, and its reason should match our expected message.
                let first_err = &errs[0];
                // Get error message as string
                let msg = format!("{:?}", first_err.reason());
                assert!(
                    msg.contains("Unclosed double quote"),
                    "Unexpected error message: {}",
                    msg
                )
            }
            Ok(_) => panic!("Expected an error for an unclosed double-quoted string"),
        }
    }

    #[test]
    fn test_unclosed_double_quote_error_message() {
        // Create a parser with the default configuration.
        let parser = LiteralParserBuilder::new().build();
        // Supply an input with an unclosed double quote.
        let input = r#""unclosed"#;
        // Parse and expect an error.
        let err = parser.parse(input).into_errors();

        // The parser returns a vector of errors. Check the first one.
        // Get error message as string and check its content
        let msg = format!("{:?}", err[0].reason());
        assert!(
            msg.contains("Unclosed double quote"),
            "Expected error message with 'Unclosed double quote', got: {}",
            msg
        )
    }

    #[test]
    fn test_double_quoted_with_consecutive_escapes() {
        let parser = LiteralParserBuilder::new().build();
        // Test with multiple consecutive escape sequences:

        // Test with multiple consecutive escape sequences.
        // The input is:
        //   "line1\nline2\tend"
        //
        // Here's a breakdown by index:
        //   0: "          -> opening quote
        //   1: l
        //   2: i
        //   3: n
        //   4: e
        //   5: 1
        //   6: \          -> backslash (escaping the n)
        //   7: n          -> newline escape, becomes \n in parsed string
        //   8: l
        //   9: i
        //  10: n
        //  11: e
        //  12: 2
        //  13: \          -> backslash (escaping the t)
        //  14: t          -> tab escape, becomes \t in parsed string
        //  15: e
        //  16: n
        //  17: d
        //  18: "          -> closing quote
        //
        // Thus, the overall span of the literal is 0..19.
        let input = r#""line1\nline2\tend""#;

        let expected = Expr::LiteralStr(("line1\nline2\tend".to_string(), (0..19).into()));

        assert_eq!(parser.parse(input).into_result(), Ok(expected));
    }

    #[test]
    fn test_single_quoted_with_escapes() {
        let parser = LiteralParserBuilder::new().single_quote(true).build();
        let input = r#"'hello\'\\\n\r\tworld'"#;
        let expected = Expr::LiteralStr(("hello'\\\n\r\tworld".to_string(), (0..22).into()));
        assert_eq!(parser.parse(input).into_result(), Ok(expected));
    }

    #[test]
    fn test_all_escape_sequences() {
        let parser = LiteralParserBuilder::new().build();
        // Test all escape sequences in double-quoted strings
        let input = r#""\\\/\"\n\r\t""#;
        let expected = Expr::LiteralStr(("\\/\"\n\r\t".to_string(), (0..14).into()));
        assert_eq!(parser.parse(input).into_result(), Ok(expected));
    }

    #[test]
    fn test_mixed_literal_types() {
        let parser = LiteralParserBuilder::new().single_quote(true).raw_string(true).build();

        // Test all types of literals sequentially
        let test_cases = [
            (
                "42",
                Expr::LiteralNum((
                    NumberValue::new_integer(42, ExplicitSign::None),
                    (0..2).into(),
                )),
            ),
            (
                r#""double""#,
                Expr::LiteralStr(("double".to_string(), (0..8).into())),
            ),
            (
                r#"'single'"#,
                Expr::LiteralStr(("single".to_string(), (0..8).into())),
            ),
            (
                r#"`raw`"#,
                Expr::LiteralStr(("raw".to_string(), (0..5).into())),
            ),
        ];

        for (input, expected) in test_cases {
            assert_eq!(parser.parse(input).into_result(), Ok(expected));
        }
    }

    // Property-based tests for numeric literals.
    proptest! {
        #[test]
        fn prop_numeric_literals(input in (-1000i64..1000).prop_map(|n| n.to_string())) {
            let parser = LiteralParserBuilder::new().build();
            let expected = BigInt::from(input.parse::<i64>().unwrap());
            // Check if the number has an explicit sign (starts with + or -)
            let explicit_sign = match input.chars().next() {
                Some('+') => ExplicitSign::Positive,
                Some('-') => ExplicitSign::Negative,
                _ => ExplicitSign::None,
            };
            let result = parser.parse(&input).into_result().unwrap();
            prop_assert_eq!(result, Expr::LiteralNum((NumberValue::new_integer(expected, explicit_sign), (0..input.len()).into())));
        }
    }

    // Property-based tests for double-quoted string literals with escapes.
    proptest! {
        #[test]
        fn prop_double_quoted_literals(s in "[a-zA-Z0-9\\n\\r\\t\\\\]*") {
            // Replace backslashes to ensure they are doubled in the literal.
            let escaped = s.replace("\\", "\\\\");
            let input = format!("\"{}\"", escaped);
            let parser = LiteralParserBuilder::new().build();
            let parsed = parser.parse(input.as_str()).into_result().unwrap();
            match parsed {
                Expr::LiteralStr((res, _)) => prop_assert_eq!(res, s),
                _ => prop_assert!(false, "Not a literal string")
            }
        }
    }
}
