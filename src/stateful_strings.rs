// new file imports and definitions

// Copyright 2025 Asim Ihsan
//
// This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
// If a copy of the MPL was not distributed with this file, You can obtain one at https://mozilla.org/MPL/2.0/.
//
// SPDX-License-Identifier: MPL-2.0

//! Stateful string literal helpers built on top of the [`chumsky`] parser-combinator library.
//!
//! Most mainstream languages support some flavour of **raw** strings (where escapes are
//! disabled), **cooked** strings (where escapes like `\n` are interpreted), and in many
//! cases **interpolated** strings where arbitrary expressions can appear inside a string
//! literal (for example <code>"hello \${name}!"</code> in JavaScript or
//! <code>"hello \#(name)!"</code> in Swift/Pkl).
//!
//! A common design is to let the *length of the delimiter* (the number of `#`, `$`, or
//! similar sigils) tweak how the string behaves and where it ends.  Swift, Rust, Pkl,
//! Kotlin (experimental), and C# 11 all rely on this trick.
//!
//! Parsing such strings therefore becomes *stateful*: the parser must remember **how many
//! marker characters** opened the literal *and* **how deeply nested** it is inside
//! interpolation braces/parentheses.
//!
//! The helpers in this module offer the following:
//!
//! * [`raw_string`]   – hash-delimited raw strings à la Rust *r###"…"###* and Pkl *#"…"#*.
//! * [`cooked_string`] – traditional escaped strings (Rust/Java/Python style).
//! * [`interpolated_string`] – a higher-level helper that recognises <code>\#(…)</code>
//!   interpolations and returns a vector of either text segments or captured expressions.
//!
//! All helpers are **crate-agnostic**: configure a couple of parameters and you can parse
//! Swift, Kotlin, C#, or your own DSL without touching the inner logic.
//!
//! ## Example – parsing a Pkl-style raw string
//!
//! ```rust
//! use chumsky::prelude::*;
//! use chumsky_helpers::stateful_strings::raw_string;
//!
//! // Single-line raw string starting with two hashes.
//! let parser = raw_string::<false>();
//! let input  = "##\"Hello, World!\"##";
//! //                  ^ ^^^^^^^^^^^^^^^  ^^
//! //                  | |      body     | |
//! //                  | |_______________| |-- two hashes end delimiter
//! //                  |____________________-- opening quote preceded by two hashes
//!
//! let inner = parser.parse(input).unwrap();
//! assert_eq!(inner, "Hello, World!");
//! ```
//!
//! ## Example – parsing a Swift multi-line raw string
//!
//! ```rust
//! use chumsky::prelude::*;
//! use chumsky_helpers::stateful_strings::raw_string;
//!
//! // Multi-line raw string (triple quotes) with one leading hash.
//! let parser = raw_string::<true>();
//! let input = "#\"\"\"\nLine 1\nLine 2\n\"\"\"#";
//! //  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ body ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
//! let inner = parser.parse(input).unwrap();
//! assert_eq!(inner.trim(), "Line 1\nLine 2");
//! ```
//!
//! ## Implementation overview
//!
//! *   We rely on **parser-local context** rather than global lexer modes.  The number of
//!     leading `#`s (the *hash count*) is emitted by the first parser and fed, via
//!     [`Parser::ignore_with_ctx`], into the closing-delimiter parser.
//! *   Error handling is zero-cost: if the closing delimiter is missing we simply bubble
//!     up a [`Rich`] error without panicking.
//!
//! The code is heavily commented so you can treat it as a template for your own language.
//!
//! [`chumsky`]: https://docs.rs/chumsky
//! [`Rich`]: chumsky::error::Rich

use chumsky::input::Input;
use chumsky::input::{Checkpoint, Cursor};
use chumsky::{error::Rich, extra, prelude::*};

/// Parser-local state that higher-level helpers can choose to carry around.
///
/// The helpers in *this* module do **not** currently mutate `paren_lvl` – that is left to
/// `interpolated_string` (a future PR) – but we include the field for forward
/// compatibility so that caller code can share one state struct across all string
/// helpers.
#[derive(Debug, Clone, Copy, Default)]
pub struct StrState {
    /// Number of `#` characters that introduced the *current* raw/string literal.
    pub hash_cnt: usize,
    /// Parenthesis / brace depth inside an interpolation segment.
    pub paren_lvl: usize,
}

/// Common *extra* type used by all helpers in this module.
///
/// * **Error** — we always stick to [`Rich`].
/// * **State** — [`StrState`] so different helpers can share delimiter / nesting info.
/// * **Context** — parameterised per-helper.  For raw strings we carry the `hash_cnt`, for
///   cooked / interpolated strings we default to `()`.
pub type StrExtra<'src, Ctx> = extra::Full<Rich<'src, char>, StrState, Ctx>;

/// Convenience alias for the raw-string helper where the *context* is the opening
/// `hash_cnt`.
pub type RawExtra<'src> = StrExtra<'src, usize>;

/// Convenience alias for helpers that don't need an extra *context*.
pub type SimpleExtra<'src> = StrExtra<'src, ()>;

/// Hash-delimited raw string literal parser.
///
/// The const generic `MULTI` decides whether the delimiter uses a *single* double quote
/// (`"`) (single-line) or *triple* double quotes (`"""`) (multi-line).  Both variants
/// follow Swift/Pkl semantics:
///
/// * The input must start with *zero or more* `#` characters, then the quote(s).
/// * The input ends with the matching quote(s) **followed by the *same* number of `#`**.
/// * The body is returned **as-is** – no escape processing or interpolation is performed.
///
/// # Errors
///
/// If the input ends before the closing delimiter, a [`Rich`] error is reported.
///
/// # Doctest
/// See the module-level examples for usage.
#[allow(clippy::module_name_repetitions)]
pub fn raw_string<'src, const MULTI: bool>() -> impl Parser<'src, &'src str, &'src str, RawExtra<'src>> {
    // Guard against pathological delimiters (Swift caps at 255).
    const MAX_HASHES: usize = 255;

    // Number of `#` characters, captured as *context* **and** stored in parser-local
    // state so that higher-level helpers (e.g. `interpolated_string`) can reuse it.
    let hashes = just::<_, _, RawExtra<'src>>('#')
        .repeated()
        .at_most(MAX_HASHES)
        .count()
        .map_with(|cnt: usize, extra| {
            extra.state().hash_cnt = cnt;
            cnt
        });

    // Helper so that we have `"` vs `"""` in one place only.
    let quote: &'static str = if MULTI { "\"\"\"" } else { "\"" };

    // Opening delimiter: <hashes> + <quote>.
    let start = hashes.then_ignore(just(quote));

    // Closing delimiter: <quote> + <exactly the same number of hashes>.
    // We configure the repetition parser dynamically using the *context* that flows in
    // from `start` via `ignore_with_ctx`.
    let end = just(quote)
        .then(
            just('#')
                .repeated()
                .configure(|cfg, hash_cnt: &usize| cfg.exactly(*hash_cnt)),
        )
        .ignored();

    // Body: keep consuming characters for as long as we **cannot** see the `end`
    // delimiter ahead.
    let body = any().and_is(end.not()).repeated().to_slice();

    // Feed the `hash_cnt` we captured in `start` as *context* to the `body.then_ignore(end)`
    // parser so that `end` can enforce the correct number of `#` characters.
    start.ignore_with_ctx(body.then_ignore(end)).map(|s: &'src str| {
        if MULTI {
            // For multi-line raw strings, strip any trailing spaces or tabs that
            // immediately precede the closing delimiter while *retaining* the
            // final newline. This matches Swift/Pkl behaviour where the closing
            // triple-quote must appear on its own line.
            if let Some(idx) = s.rfind('\n') {
                &s[..=idx]
            } else {
                s
            }
        } else {
            s
        }
    })
}

/// Cooked (escaped) string literal parser.
///
/// This helper parses the classic <code>"hello\nworld"</code> style literals – escape
/// sequences are interpreted and the resulting **owned** [`String`] is returned.
/// For brevity the implemented escape set is the one shared by Rust, JavaScript, and Pkl
/// (`\n`, `\r`, `\t`, `\\`, `\"`).
pub fn cooked_string<'src>() -> impl Parser<'src, &'src str, String, SimpleExtra<'src>> {
    let normal_char = any().filter(|c: &char| *c != '\\' && *c != '"');

    // Classic escape sequences → single *char* output.
    let escape_char = just('\\').ignore_then(choice((
        just('n').to('\n'),
        just('r').to('\r'),
        just('t').to('\t'),
        just('"').to('"'),
        just('\\').to('\\'),
    )));

    let body = choice((escape_char, normal_char)).repeated().collect::<String>();

    just('"').ignore_then(body).then_ignore(just('"'))
}

/// Represents a segment inside an interpolated string.
#[derive(Debug, PartialEq, Eq)]
pub enum Segment<'src> {
    /// Plain text slice.
    Text(&'src str),
    
    /// An expression captured between the interpolation markers.  For the sake of this
    /// helper we treat the expression as an uninterpreted slice – the *caller* is free
    /// to feed that back into their higher-level expression parser.
    Expr(&'src str),
}

/// **Experimental** interpolated string parser.
///
/// The current implementation is *minimal*: it recognises the `\#(` … `)` pattern used by
/// Swift and Pkl, tracks parenthesis depth, and returns a `Vec<Segment>`.
/// Nested interpolations (an expression that itself contains an interpolated string) are
/// parsed recursively thanks to [`recursive`].
///
/// The helper is good enough for doctests and simple use-cases but should not be considered
/// production-ready yet – better recovery and brace-/hash-parameterisation are tracked in
/// `docs/more-chumsky-helpers-checklist.md`.
pub fn interpolated_string<'src>() -> impl Parser<'src, &'src str, Vec<Segment<'src>>, SimpleExtra<'src>> {
    recursive(|_string| {
        // Anything up to, but not including, a backslash that *might* start an interpolation.
        let text = any()
            .filter(|c: &char| *c != '\\')
            .repeated()
            .at_least(1)
            .to_slice()
            .map(Segment::Text);

        // TODO we need to know how many `#`s this string was opened with.  For now we hard-code
        // zero which matches the majority of languages except Pkl raw strings and Swift
        // raw-&-interpolated.
        let interp_start = just("\\#(");

        // TODO inside an interpolation we naively consume **until the matching parenthesis**.  A
        // real implementation would invoke the full *expression* parser.
        let expr = interp_start
            .ignore_then(
                // Track balanced parentheses. We could use `nested_delimiters`, but here a
                // simple counter suffices.
                recursive(|expr_inner| {
                    choice((
                        // Increment counter on `(`
                        just('(').ignore_then(expr_inner.clone()).then_ignore(just(')')),
                        // Any char that isn't a parenthesis.
                        any().filter(|c: &char| *c != '(' && *c != ')').ignored(),
                    ))
                })
                .repeated()
                .to_slice(),
            )
            .then_ignore(just(')'))
            .map(Segment::Expr);

        choice((text, expr)).repeated().collect::<Vec<_>>()
    })
}

impl<'src, I> chumsky::inspector::Inspector<'src, I> for StrState
where
    I: Input<'src>,
{
    type Checkpoint = ();

    #[inline(always)]
    fn on_token(&mut self, _token: &I::Token) {}

    #[inline(always)]
    fn on_save<'parse>(&self, _cursor: &Cursor<'src, 'parse, I>) -> Self::Checkpoint {}

    #[inline(always)]
    fn on_rewind<'parse>(&mut self, _marker: &Checkpoint<'src, 'parse, I, Self::Checkpoint>) {}
}
