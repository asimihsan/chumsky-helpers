// Copyright 2025 Asim Ihsan
//
// This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
// If a copy of the MPL was not distributed with this file, You can obtain one at https://mozilla.org/MPL/2.0/.
//
// SPDX-License-Identifier: MPL-2.0

use crate::number::{NumberParserBuilder, NumberValue};
use crate::Spanned;
use chumsky::error::LabelError;
use chumsky::error::LabelError;
use chumsky::error::Simple;
use chumsky::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Error(Spanned<String>),
    LiteralStr(Spanned<String>),
    LiteralNum(Spanned<NumberValue>),
}

#[derive(Debug, Default)]
pub struct LiteralParserBuilder {
    allow_single_quote: bool,
    allow_raw_string: bool,
}

impl LiteralParserBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn single_quote(mut self, allow: bool) -> Self {
        self.allow_single_quote = allow;
        self
    }

    pub fn raw_string(mut self, allow: bool) -> Self {
        self.allow_raw_string = allow;
        self
    }

    pub fn build<'a>(self) -> impl Parser<'a, &'a str, Expr> {
        // Number parser with span
        let number = NumberParserBuilder::new()
            .negative(true)
            .float(true)
            .scientific(true)
            .build()
            .map_with(|n, span| Expr::LiteralNum(Spanned(n, span.clone())));

        // Double-quoted strings with span
        let normal_dq = none_of("\\\"").map(|c| c.to_string());
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
            .then_ignore(
                just('"').or_not().try_map(|opt_quote, span| match opt_quote {
                    Some(_) => Ok(()),
                    None => Err(Simple::merge_expected_found(
                        vec!["Unclosed double quote".to_string()],
                        None,
                        span,
                    )),
                }),
            )
            .map_with(|s, span| Expr::LiteralStr(Spanned(s, span)));

        // Raw string parser – always attempt to parse, then decide allowed vs. disallowed.
        let raw_string = just("`")
            .ignore_then(none_of("`").repeated().collect::<String>())
            .then_ignore(just("`"))
            .map_with(move |s, span| {
                if self.allow_raw_string {
                    Expr::LiteralStr((s, span))
                } else {
                    Expr::Error(("raw string literals are not allowed".to_string(), span))
                }
            })
            .boxed();

        // Single-quoted string parser – always attempt to parse.
        let single_quoted = just("'")
            .ignore_then(
                choice((
                    none_of("\\'").map(|c| c.to_string()),
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
                .map(|v: Vec<String>| v.concat()),
            )
            .then_ignore(just('\''))
            .map_with_span(move |s, span| {
                if self.allow_single_quote {
                    Expr::LiteralStr((s, span))
                } else {
                    Expr::Error((
                        "single-quoted string literals are not allowed".to_string(),
                        span,
                    ))
                }
            })
            .boxed();

        let choices = vec![
            number.boxed(),
            double_quoted.boxed(),
            raw_string,
            single_quoted,
        ];

        choice(choices).boxed()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use chumsky::error::SimpleReason;
    use chumsky::Parser;
    use proptest::prelude::*;

    #[test]
    fn test_double_quoted_literal() {
        let parser = LiteralParserBuilder::new().build();
        let input = r#""hello\nworld""#;
        let expected = Expr::LiteralStr(Spanned("hello\nworld".to_string(), 0..14));
        assert_eq!(parser.parse(input), Ok(expected));
    }

    #[test]
    fn test_invalid_double_quote_unclosed() {
        let parser = LiteralParserBuilder::new().build();
        let input = r#""unclosed string"#;
        assert!(parser.parse(input).is_err());
    }

    #[test]
    fn test_number_literal() {
        let parser = LiteralParserBuilder::new().build();
        let input = "42";
        let expected = Expr::LiteralNum(Spanned(NumberValue::Integer(42), 0..2));
        assert_eq!(parser.parse(input), Ok(expected));
    }

    #[test]
    fn test_single_quoted_literal_allowed() {
        let parser = LiteralParserBuilder::new().single_quote(true).build();
        let input = r#"'hello\tworld'"#;
        let expected = Expr::LiteralStr(Spanned("hello\tworld".to_string(), 0..14));
        assert_eq!(parser.parse(input), Ok(expected));
    }

    #[test]
    fn test_single_quoted_literal_disallowed() {
        let parser = LiteralParserBuilder::new().single_quote(false).build();
        let input = r#"'hello'"#;
        match parser.parse(input) {
            Ok(Expr::Error(Spanned(msg, _))) => {
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
        match parser.parse(input) {
            Ok(Expr::Error(Spanned(msg, span))) => {
                assert_eq!(msg, "single-quoted string literals are not allowed");
                // Optionally, verify that the span covers the input.
                assert_eq!(span, 0..input.len());
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
        let expected = Expr::LiteralStr(Spanned("raw \\n string".to_string(), 0..15));
        assert_eq!(parser.parse(input), Ok(expected));
    }

    #[test]
    fn test_raw_string_literal_disallowed() {
        let parser = LiteralParserBuilder::new().raw_string(false).build();
        let input = "`raw string`";
        match parser.parse(input) {
            Ok(Expr::Error(Spanned(msg, _))) => {
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
        match parser.parse(input) {
            Ok(Expr::Error(Spanned(msg, span))) => {
                assert_eq!(msg, "raw string literals are not allowed");
                // Optionally, verify that the span covers the input (or a part of it)
                assert_eq!(span, 0..input.len());
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
        let expected = Expr::LiteralStr(Spanned("".to_string(), 0..2));
        assert_eq!(parser.parse(input), Ok(expected));
    }

    #[test]
    fn test_empty_single_quoted_literal_allowed() {
        let parser = LiteralParserBuilder::new().single_quote(true).build();
        // An empty single-quoted literal: ''
        let input = "''";
        // The span covers both single quotes (0..2)
        let expected = Expr::LiteralStr(Spanned("".to_string(), 0..2));
        assert_eq!(parser.parse(input), Ok(expected));
    }

    #[test]
    fn test_empty_raw_string_literal_allowed() {
        let parser = LiteralParserBuilder::new().raw_string(true).build();
        // An empty raw string literal: ``
        let input = "``";
        // The span covers both backticks (0..2)
        let expected = Expr::LiteralStr(Spanned("".to_string(), 0..2));
        assert_eq!(parser.parse(input), Ok(expected));
    }

    #[test]
    fn test_error_unclosed_double_quoted() {
        let parser = LiteralParserBuilder::new().build();
        // Input with an unclosed double quote
        let input = r#""unclosed"#;
        match parser.parse(input) {
            Err(errs) => {
                // We expect one error, and its reason should match our expected message.
                let first_err = &errs[0];
                match first_err.reason() {
                    // We expect a custom error message.
                    SimpleReason::Custom(msg) => {
                        assert!(
                            msg.contains("Unclosed double quote"),
                            "Unexpected error message: {}",
                            msg
                        );
                    }
                    // If the error is of any other type, that's unexpected.
                    other => panic!("Expected a Custom error reason, got {:?}", other),
                }
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
        let err = parser.parse(input).unwrap_err();

        // The parser returns a vector of errors. Check the first one.
        match err[0].reason() {
            chumsky::error::SimpleReason::Custom(msg) => {
                assert_eq!(msg, "Unclosed double quote");
            }
            other => panic!("Expected a custom error reason, got {:?}", other),
        }
    }

    #[test]
    fn test_double_quoted_with_consecutive_escapes() {
        let parser = LiteralParserBuilder::new().build();
        // Test with multiple consecutive escape sequences:

        // Test with multiple consecutive escape sequences.
        // The input is:
        //   "line1\nline2\tend"
        //
        // Here’s a breakdown by index:
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

        let expected = Expr::LiteralStr(Spanned("line1\nline2\tend".to_string(), 0..19));

        assert_eq!(parser.parse(input), Ok(expected));
    }

    // Property-based tests for numeric literals.
    proptest! {
        #[test]
        fn prop_numeric_literals(n in -1000i64..1000) {
            let parser = LiteralParserBuilder::new().build();
            let input = n.to_string();
            let parsed = parser.parse(&*input).unwrap();
            match parsed {
                Expr::LiteralNum(Spanned(NumberValue::Integer(i), _)) => prop_assert_eq!(i, n),
                _ => prop_assert!(false, "Expected integer literal"),
            }
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
            let parsed = parser.parse(&*input).unwrap();
            match parsed {
                Expr::LiteralStr(Spanned(res, _)) => prop_assert_eq!(res, s),
                _ => prop_assert!(false, "Not a literal string")
            }
        }
    }
}
