// Copyright 2025 Asim Ihsan
//
// This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
// If a copy of the MPL was not distributed with this file, You can obtain one at https://mozilla.org/MPL/2.0/.
//
// SPDX-License-Identifier: MPL-2.0

//! # Chumsky Helpers
//!
//! A collection of reusable parsers and utilities built on top of the
//! [chumsky](https://github.com/zesterer/chumsky) parser combinator library.
//!
//! This crate provides ready-to-use parsers for common data formats and literals,
//! designed to be composable, configurable, and robust with comprehensive error handling.
//!
//! ## Features
//!
//! * **Number parsing** - Parse integers, floating point numbers, and scientific notation
//!   with configurable options and high-precision component preservation.
//! * **Date and duration parsing** - Parse ISO 8601 dates, ISO 8601 durations, and Go-style
//!   time duration formats.
//! * **Literal parsing** - Parse string literals with various quoting styles and escape sequences.
//!
//! ## Usage
//!
//! Each module provides builder-style APIs that let you configure the parsers according to your needs.
//!
//! ```rust
//! use chumsky_helpers::number::{NumberParserBuilder, NumberValue};
//! use chumsky::prelude::*;
//!
//! // Create a parser for numbers that allows negative values, floats, and scientific notation
//! let parser = NumberParserBuilder::new()
//!     .negative(true)
//!     .float(true)
//!     .scientific(true)
//!     .build();
//!
//! // Parse a number and access both the calculated value and original components
//! let result = parser.parse("123.456e-7").into_result().unwrap();
//! match result {
//!     NumberValue::Float { value, base, decimal, exponent } => {
//!         println!("Value: {}", value);
//!         println!("Base: {}", base);
//!         println!("Decimal part: {:?}", decimal);
//!         println!("Exponent: {:?}", exponent);
//!     },
//!     _ => panic!("Expected Float variant"),
//! }
//! ```
//!
//! ## Examples
//!
//! ### Parsing ISO 8601 Dates
//!
//! ```rust
//! use chumsky_helpers::datetime::parse_iso_date;
//!
//! // Parse a basic ISO date format
//! let date = parse_iso_date("20240204").unwrap();
//! assert_eq!(date.year(), 2024);
//! assert_eq!(date.month(), time::Month::February);
//! assert_eq!(date.day(), 4);
//!
//! // Parse an extended ISO date format
//! let date = parse_iso_date("2024-02-04").unwrap();
//! assert_eq!(date.year(), 2024);
//! assert_eq!(date.month(), time::Month::February);
//! assert_eq!(date.day(), 4);
//! ```
//!
//! ### Parsing String Literals
//!
//! ```rust
//! use chumsky_helpers::literal::{LiteralParserBuilder, Expr};
//! use chumsky::prelude::*;
//!
//! // Create a parser for literals with support for single quotes and raw strings
//! let parser = LiteralParserBuilder::new()
//!     .single_quote(true)
//!     .raw_string(true)
//!     .build();
//!
//! // Parse different types of string literals
//! let double_quoted = parser.parse("\"hello\\nworld\"").into_result().unwrap();
//! let single_quoted = parser.parse("'hello\\tworld'").into_result().unwrap();
//! let raw_string = parser.parse("`raw string`").into_result().unwrap();
//! ```
//!
//! ## High-Precision Number Handling
//!
//! The number parser preserves the original components of parsed numbers, allowing for
//! high-precision operations that might be lost in floating-point representation:
//!
//! ```rust
//! use chumsky_helpers::number::{NumberParserBuilder, NumberValue};
//! use chumsky::prelude::*;
//!
//! let parser = NumberParserBuilder::new()
//!     .float(true)
//!     .scientific(true)
//!     .negative(true)
//!     .build();
//!
//! let result = parser.parse("123.456789012345678901234567890e-10").into_result().unwrap();
//! match result {
//!     NumberValue::Float { value: _, base, decimal, exponent } => {
//!         // Access original string components for arbitrary precision arithmetic
//!         println!("Base: {}", base);
//!         println!("Decimal: {:?}", decimal);
//!         println!("Exponent: {:?}", exponent);
//!     },
//!     _ => panic!("Expected Float variant"),
//! }
//! ```

pub mod datetime;
pub mod expr;
pub mod literal;
pub mod number;

use chumsky::span::SimpleSpan;

/// A simple type alias for spans in the chumsky parser.
pub type Span = SimpleSpan;

/// A type representing a value along with its position in the source text.
pub type Spanned<T> = (T, Span);

// Re-export the public API
pub use expr::{Error, EvalResult};
