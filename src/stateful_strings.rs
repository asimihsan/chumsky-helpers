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
//! use chumsky_helpers::stateful_strings::raw_single_line;
//!
//! // Single-line raw string starting with two hashes.
//! let parser = raw_single_line();
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
//! use chumsky_helpers::stateful_strings::raw_multi_line;
//!
//! // Multi-line raw string (triple quotes) with one leading hash.
//! let parser = raw_multi_line();
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

use bon::bon;
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

/// Which delimiter style should the raw string parser expect.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum RawStringMode {
    /// A single `"` quote – e.g. `#"hello"#`.
    #[default]
    SingleLine,
    /// Triple quotes `"""` – e.g. `#"""hello"""#`.
    MultiLine,
}

/// User-facing configuration for the raw string helper.
///
/// The API is intentionally kept *exhaustive-future-proof*: new fields can be
/// added with `#[builder(default)]` without breaking callers that rely on the
/// generated builder.
#[derive(Debug, Clone, Copy)]
pub struct RawStringConfig {
    pub mode: RawStringMode,
    /// Whether to strip indentation in multi-line mode (planned feature).
    pub strip_indent: bool,
    /// Whether to recognise `\#(` interpolations inside the string (future).
    pub allow_interp: bool,
}

impl Default for RawStringConfig {
    fn default() -> Self {
        Self {
            mode: RawStringMode::SingleLine,
            strip_indent: false,
            allow_interp: false,
        }
    }
}

// Generate a typestate builder via `bon`.
#[bon]
impl RawStringConfig {
    #[builder]
    pub fn new(
        #[builder(default)] mode: RawStringMode,
        #[builder(default)] strip_indent: bool,
        #[builder(default)] allow_interp: bool,
    ) -> Self {
        Self {
            mode,
            strip_indent,
            allow_interp,
        }
    }

    /// Convert the configuration into an actual parser instance.
    pub fn into_parser<'src>(&self) -> Box<dyn Parser<'src, &'src str, &'src str, RawExtra<'src>> + 'src> {
        match self.mode {
            RawStringMode::SingleLine => Box::new(raw_string_impl::<false>()),
            RawStringMode::MultiLine => Box::new(raw_string_impl::<true>()),
        }
    }
}

/// Convenient free function that accepts a `RawStringConfig` and returns the
/// corresponding parser.  This keeps call-sites concise:
///
/// ```rust
/// use chumsky_helpers::stateful_strings::{raw_string, RawStringConfig, RawStringMode};
/// use chumsky::prelude::*;
///
/// // Build a parser for multi-line raw strings using the builder.
/// let parser = raw_string(
///     RawStringConfig::builder()
///         .mode(RawStringMode::MultiLine)
///         .build(),
/// );
///
/// let input = "#\"\"\"\nHello\n\"\"\"#";
/// let inner = parser.parse(input).unwrap();
/// assert_eq!(inner.trim(), "Hello");
/// ```
pub fn raw_string<'src>(cfg: RawStringConfig) -> Box<dyn Parser<'src, &'src str, &'src str, RawExtra<'src>> + 'src> {
    cfg.into_parser()
}

/// Convenience helper: single-line raw string parser without any configuration.
pub fn raw_single_line<'src>() -> impl Parser<'src, &'src str, &'src str, RawExtra<'src>> {
    raw_string_impl::<false>()
}

/// Convenience helper: multi-line raw string parser without any configuration.
pub fn raw_multi_line<'src>() -> impl Parser<'src, &'src str, &'src str, RawExtra<'src>> {
    raw_string_impl::<true>()
}

/// Internal implementation shared by the user-facing configuration API above.
#[allow(clippy::module_name_repetitions)]
fn raw_string_impl<'src, const MULTI: bool>() -> impl Parser<'src, &'src str, &'src str, RawExtra<'src>> {
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
    start
        .ignore_with_ctx(body.then_ignore(end))
        .map_with(|s: &'src str, _extra| {
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Lang {
    /// Swift-style defaults.
    #[default]
    Swift,
    /// Pkl language defaults.
    Pkl,
    /// C# 11 raw-string dialect.
    CSharp11,
    /// Kotlin experimental multi-dollar strings.
    Kotlin,
    /// Rust raw & cooked strings (no interpolation by default).
    Rust,
    /// Python triple-quote and r"…" literals (no interpolation).
    Python,
}

/// High-level configuration builder that can cover all string helper variants.
/// ⤷ In this first scaffold it merely records the requested toggles; the next
///   PRs will wire these into the actual parser combinators.
#[derive(Debug, Clone)]
pub struct StringParserConfig {
    /// Chosen language preset – fills the rest of the fields with sensible
    /// defaults that callers can still override.
    pub lang: Lang,

    /// Whether multi-line raw strings should strip the common indentation that
    /// precedes the closing delimiter.  Swift & Pkl do, Rust does not.
    pub strip_indent: bool,

    /// Enable `\u{…}` and friends in *cooked* literals.
    pub unicode_escape: bool,

    /// Enable `\#(` … interpolation support.
    pub allow_interpolation: bool,
}

// Generate a typestate builder via `bon` so callers can fluently tweak knobs.
#[bon]
impl StringParserConfig {
    #[builder]
    pub fn new(
        #[builder(default = Lang::Swift)] lang: Lang,
        #[builder(default)] strip_indent: bool,
        #[builder(default)] unicode_escape: bool,
        #[builder(default)] allow_interpolation: bool,
    ) -> Self {
        // Language presets override caller defaults unless the caller explicitly
        // flips the boolean *after* dialling the language (the builder lets
        // them do that). For now we assume the caller invokes the preset
        // first, so we simply force the defaults here.
        let (strip_indent, unicode_escape, allow_interpolation) = if matches!(lang, Lang::Swift | Lang::Pkl) {
            (true, true, true)
        } else {
            (strip_indent, unicode_escape, allow_interpolation)
        };

        Self {
            lang,
            strip_indent,
            unicode_escape,
            allow_interpolation,
        }
    }

    /// Single-line raw string parser according to this configuration.
    pub fn raw_single_line<'src>(&self) -> impl Parser<'src, &'src str, &'src str, RawExtra<'src>> {
        // TODO integrate config flags (strip_indent, allow_interpolation, etc.)
        raw_string_impl::<false>()
    }

    /// Multi-line raw string parser according to this configuration.
    pub fn raw_multi_line<'src>(&self) -> impl Parser<'src, &'src str, String, RawExtra<'src>> {
        let strip = self.strip_indent;
        raw_string_impl::<true>().map(move |s: &'src str| {
            if strip {
                // Strip indentation following Swift/Pkl rules.
                strip_multiline_indent(s)
            } else {
                s.to_string()
            }
        })
    }

    /// Cooked (escaped) string literal parser according to this configuration.
    pub fn cooked_string<'src>(&self) -> impl Parser<'src, &'src str, String, SimpleExtra<'src>> {
        cooked_string()
    }

    /// Interpolated string parser according to this configuration.
    pub fn interpolated_string<'src>(&self) -> impl Parser<'src, &'src str, Vec<Segment<'src>>, SimpleExtra<'src>> {
        interpolated_string()
    }
}

impl Default for StringParserConfig {
    fn default() -> Self {
        Self::builder().build()
    }
}

/// Utility that strips the common indentation from a multi-line raw string body.
/// Assumes the string starts with a newline and ends with a newline (as ensured
/// by `raw_string_impl::<true>`).  Tabs are treated as one indentation unit.
fn strip_multiline_indent(s: &str) -> String {
    // Split but preserve newline at start; the first slice will be empty.
    let mut lines: Vec<&str> = s.split('\n').collect();
    if lines.is_empty() {
        return String::new();
    }

    // Last element after split corresponds to text after final newline (empty).
    if lines.last() == Some(&"") {
        lines.pop();
    }

    // Compute minimal indent (spaces or tabs) across non-empty lines ignoring the first empty slice.
    let min_indent = lines
        .iter()
        .filter(|line| !line.trim().is_empty())
        .map(|line| line.chars().take_while(|c| *c == ' ' || *c == '\t').count())
        .min()
        .unwrap_or(0);

    // Reconstruct string with first newline and stripped indentation.
    let mut out = String::with_capacity(s.len());
    out.push('\n');
    for (idx, line) in lines.iter().enumerate() {
        if idx == 0 {
            // first slice was empty, already emitted newline.
            continue;
        }
        let trimmed = if line.len() >= min_indent {
            &line[min_indent..]
        } else {
            ""
        };
        out.push_str(trimmed);
        out.push('\n');
    }
    out
}

// Placeholder: later we will attach `into_parser()` style helpers here.
