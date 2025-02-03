// Copyright 2025 Asim Ihsan
//
// This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
// If a copy of the MPL was not distributed with this file, You can obtain one at https://mozilla.org/MPL/2.0/.
//
// SPDX-License-Identifier: MPL-2.0

use crate::number::{NumberParserBuilder, NumberValue};
use crate::Spanned;
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

    pub fn build(self) -> impl Parser<char, Expr, Error = Simple<char>> {
        // Number parser with span
        let number = NumberParserBuilder::new()
            .negative(true)
            .float(true)
            .scientific(true)
            .build()
            .map_with_span(|n, span| Expr::LiteralNum(Spanned(n, span)));

        // Double-quoted strings with span
        let normal_dq = none_of("\\\"").map(|c: char| c.to_string());
        let escaped_dq = just('\\')
            .ignore_then(choice((
                just('\\').to("\\"),
                just('/').to("/"),
                just('"').to("\""),
                just('n').to("\n"),
                just('r').to("\r"),
                just('t').to("\t"),
            )))
            .map(|s: &str| s.to_string());
        let dq_content =
            choice((normal_dq, escaped_dq)).repeated().map(|v: Vec<String>| v.concat());
        let double_quoted = just('"')
            .ignore_then(dq_content)
            .then_ignore(
                just('"').or_not().try_map(|opt_quote, span| match opt_quote {
                    Some(_) => Ok(()),
                    None => Err(Simple::custom(span, "Unclosed double quote")),
                }),
            )
            .map_with_span(|s, span| Expr::LiteralStr(Spanned(s, span)));

        // Raw string parser – always attempt to parse, then decide allowed vs. disallowed.
        let raw_string = just('`')
            .ignore_then(filter(|&c| c != '`').repeated().collect::<String>())
            .then_ignore(just('`'))
            .map_with_span(move |s, span| {
                if self.allow_raw_string {
                    Expr::LiteralStr(Spanned(s, span))
                } else {
                    Expr::Error(Spanned(
                        "raw string literals are not allowed".to_string(),
                        span,
                    ))
                }
            })
            .boxed();

        // Single-quoted string parser – always attempt to parse.
        let single_quoted = just('\'')
            .ignore_then(
                choice((
                    none_of("\\'").map(|c: char| c.to_string()),
                    just('\\')
                        .ignore_then(choice((
                            just('\\').to("\\"),
                            just('\'').to("'"),
                            just('n').to("\n"),
                            just('r').to("\r"),
                            just('t').to("\t"),
                        )))
                        .map(|s: &str| s.to_string()),
                ))
                .repeated()
                .map(|v: Vec<String>| v.concat()),
            )
            .then_ignore(just('\''))
            .map_with_span(move |s, span| {
                if self.allow_single_quote {
                    Expr::LiteralStr(Spanned(s, span))
                } else {
                    Expr::Error(Spanned(
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
