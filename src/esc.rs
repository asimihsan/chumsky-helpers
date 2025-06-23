// Copyright 2025 Asim Ihsan
//
// This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
// If a copy of the MPL was not distributed with this file, You can obtain one at https://mozilla.org/MPL/2.0/.
//
// SPDX-License-Identifier: MPL-2.0

//! # Escape Sequence Parsing
//!
//! This module provides shared parsers for character escape sequences that can be reused
//! across different string literal parsers. It supports both basic character escapes
//! (like `\n`, `\t`) and Unicode escapes (like `\u{1F600}`).
//!
//! The parsers are hash-aware, meaning they can handle custom string delimiters where
//! the escape prefix changes from `\` to `\#`, `\##`, etc. based on the number of hash
//! characters used to open the string literal.
//!
//! ## Examples
//!
//! ```rust
//! use chumsky_helpers::esc::{char_escape_err, unicode_escape_err};
//! use chumsky::prelude::*;
//!
//! // Basic escape with no hash prefix (hash_cnt = 0)
//! let parser = char_escape_err(0);
//! let result = parser.parse("\\n").into_result().unwrap();
//! assert_eq!(result, '\n');
//!
//! // Hash-aware escape (hash_cnt = 1, so escape is \#n)
//! let parser = char_escape_err(1);
//! let result = parser.parse("\\#n").into_result().unwrap();
//! assert_eq!(result, '\n');
//!
//! // Unicode escape
//! let parser = unicode_escape_err(0);
//! let result = parser.parse("\\u{26}").into_result().unwrap();
//! assert_eq!(result, '&');
//! ```

use chumsky::{error::Rich, extra, prelude::*};

/// Generic character escape parser.
pub fn char_escape<'src, E>(hash_cnt: usize) -> impl Parser<'src, &'src str, char, E>
where
    E: chumsky::extra::ParserExtra<'src, &'src str, Error = Rich<'src, char>>,
{
    let prefix = just('\\').then(just('#').repeated().exactly(hash_cnt)).ignored();

    prefix.ignore_then(choice((
        just('n').to('\n'),
        just('r').to('\r'),
        just('t').to('\t'),
        just('"').to('"'),
        just('\'').to('\''),
        just('\\').to('\\'),
        just('/').to('/'),
        just('0').to('\0'),
    )))
}

/// Generic Unicode escape parser.
pub fn unicode_escape<'src, E>(hash_cnt: usize) -> impl Parser<'src, &'src str, char, E>
where
    E: chumsky::extra::ParserExtra<'src, &'src str, Error = Rich<'src, char>>,
{
    let prefix = just('\\').then(just('#').repeated().exactly(hash_cnt)).ignored();

    prefix
        .ignore_then(just('u'))
        .ignore_then(just('{'))
        .ignore_then(text::digits(16).to_slice().try_map(|hex_str: &str, span| {
            let code_point =
                u32::from_str_radix(hex_str, 16).map_err(|_| Rich::custom(span, "Invalid hexadecimal number"))?;

            if code_point > 0x10FFFF {
                return Err(Rich::custom(span, "Unicode code point out of range (> 0x10FFFF)"));
            }
            if (0xD800..=0xDFFF).contains(&code_point) {
                return Err(Rich::custom(span, "Unicode code point in surrogate range"));
            }

            char::from_u32(code_point).ok_or_else(|| Rich::custom(span, "Invalid Unicode code point"))
        }))
        .then_ignore(just('}'))
}

/// Generic hexadecimal escape parser.
pub fn hex_escape<'src, E>(hash_cnt: usize) -> impl Parser<'src, &'src str, char, E>
where
    E: chumsky::extra::ParserExtra<'src, &'src str, Error = Rich<'src, char>>,
{
    let prefix = just('\\').then(just('#').repeated().exactly(hash_cnt)).ignored();

    prefix
        .ignore_then(just('x'))
        .ignore_then(text::digits(16).exactly(2).to_slice().try_map(|hex_str: &str, span| {
            let byte_val =
                u8::from_str_radix(hex_str, 16).map_err(|_| Rich::custom(span, "Invalid hexadecimal number"))?;
            Ok(byte_val as char)
        }))
}

/// Combined escape parser.
pub fn any_escape<'src, E>(
    hash_cnt: usize,
    unicode_enabled: bool,
    hex_enabled: bool,
) -> impl Parser<'src, &'src str, char, E>
where
    E: chumsky::extra::ParserExtra<'src, &'src str, Error = Rich<'src, char>>,
{
    let mut choices: Vec<_> = vec![char_escape::<E>(hash_cnt).boxed()];

    if unicode_enabled {
        choices.push(unicode_escape::<E>(hash_cnt).boxed());
    }
    if hex_enabled {
        choices.push(hex_escape::<E>(hash_cnt).boxed());
    }

    choice(choices)
}

// Convenience wrappers for the two common extra types used in this crate.
pub type RichErr<'src> = extra::Err<Rich<'src, char>>;

pub fn char_escape_err<'src>(hash_cnt: usize) -> impl Parser<'src, &'src str, char, RichErr<'src>> {
    char_escape::<RichErr<'src>>(hash_cnt)
}

pub fn unicode_escape_err<'src>(hash_cnt: usize) -> impl Parser<'src, &'src str, char, RichErr<'src>> {
    unicode_escape::<RichErr<'src>>(hash_cnt)
}

pub fn hex_escape_err<'src>(hash_cnt: usize) -> impl Parser<'src, &'src str, char, RichErr<'src>> {
    hex_escape::<RichErr<'src>>(hash_cnt)
}

pub fn any_escape_err<'src>(
    hash_cnt: usize,
    unicode_enabled: bool,
    hex_enabled: bool,
) -> impl Parser<'src, &'src str, char, RichErr<'src>> {
    any_escape::<RichErr<'src>>(hash_cnt, unicode_enabled, hex_enabled)
}

#[cfg(test)]
mod tests {
    use super::*;
    use chumsky::Parser;

    #[test]
    fn test_basic_char_escapes() {
        let parser = char_escape_err(0);

        assert_eq!(parser.parse("\\n").into_result().unwrap(), '\n');
        assert_eq!(parser.parse("\\r").into_result().unwrap(), '\r');
        assert_eq!(parser.parse("\\t").into_result().unwrap(), '\t');
        assert_eq!(parser.parse("\\\"").into_result().unwrap(), '"');
        assert_eq!(parser.parse("\\'").into_result().unwrap(), '\'');
        assert_eq!(parser.parse("\\\\").into_result().unwrap(), '\\');
        assert_eq!(parser.parse("\\/").into_result().unwrap(), '/');
        assert_eq!(parser.parse("\\0").into_result().unwrap(), '\0');
    }

    #[test]
    fn test_hash_aware_char_escapes() {
        let parser = char_escape_err(1);

        assert_eq!(parser.parse("\\#n").into_result().unwrap(), '\n');
        assert_eq!(parser.parse("\\#t").into_result().unwrap(), '\t');

        let parser = char_escape_err(2);
        assert_eq!(parser.parse("\\##n").into_result().unwrap(), '\n');
    }

    #[test]
    fn test_unicode_escapes() {
        let parser = unicode_escape_err(0);

        assert_eq!(parser.parse("\\u{26}").into_result().unwrap(), '&');
        assert_eq!(parser.parse("\\u{E9}").into_result().unwrap(), 'é');
        assert_eq!(parser.parse("\\u{1F600}").into_result().unwrap(), '😀');
    }

    #[test]
    fn test_hash_aware_unicode_escapes() {
        let parser = unicode_escape_err(1);
        assert_eq!(parser.parse("\\#u{26}").into_result().unwrap(), '&');

        let parser = unicode_escape_err(2);
        assert_eq!(parser.parse("\\##u{1F600}").into_result().unwrap(), '😀');
    }

    #[test]
    fn test_unicode_validation() {
        let parser = unicode_escape_err(0);

        // Test out of range
        assert!(parser.parse("\\u{110000}").has_errors());

        // Test surrogate range
        assert!(parser.parse("\\u{D800}").has_errors());
        assert!(parser.parse("\\u{DFFF}").has_errors());
    }

    #[test]
    fn test_hex_escapes() {
        let parser = hex_escape_err(0);

        assert_eq!(parser.parse("\\x41").into_result().unwrap(), 'A');
        assert_eq!(parser.parse("\\x20").into_result().unwrap(), ' ');
        assert_eq!(parser.parse("\\x00").into_result().unwrap(), '\0');
    }

    #[test]
    fn test_hash_aware_hex_escapes() {
        let parser = hex_escape_err(1);
        assert_eq!(parser.parse("\\#x41").into_result().unwrap(), 'A');

        let parser = hex_escape_err(2);
        assert_eq!(parser.parse("\\##x20").into_result().unwrap(), ' ');
    }

    #[test]
    fn test_hex_validation() {
        let parser = hex_escape_err(0);

        // Test wrong length
        assert!(parser.parse("\\x1").has_errors());
        assert!(parser.parse("\\x123").has_errors());

        // Test invalid hex
        assert!(parser.parse("\\xGG").has_errors());
    }

    #[test]
    fn test_any_escape() {
        let parser = any_escape_err(0, true, true);

        // Test character escapes
        assert_eq!(parser.parse("\\n").into_result().unwrap(), '\n');

        // Test unicode escapes
        assert_eq!(parser.parse("\\u{26}").into_result().unwrap(), '&');

        // Test hex escapes
        assert_eq!(parser.parse("\\x41").into_result().unwrap(), 'A');
    }

    #[test]
    fn test_any_escape_disabled_features() {
        let parser = any_escape_err(0, false, false);

        // Character escapes should still work
        assert_eq!(parser.parse("\\n").into_result().unwrap(), '\n');

        // Unicode and hex should fail
        assert!(parser.parse("\\u{26}").has_errors());
        assert!(parser.parse("\\x41").has_errors());
    }
}
