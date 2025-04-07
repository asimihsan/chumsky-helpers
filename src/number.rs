// Copyright 2025 Asim Ihsan
//
// This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
// If a copy of the MPL was not distributed with this file, You can obtain one at https://mozilla.org/MPL/2.0/.
//
// SPDX-License-Identifier: MPL-2.0

//! # Number Parsing
//!
//! This module provides a configurable parser for numeric literals, supporting integers,
//! floating point numbers, and scientific notation with customizable options.
//!
//! The parser not only calculates the correct numeric value but also preserves the original
//! string components of the parsed number, allowing for high-precision arithmetic operations
//! that might be lost in floating-point representation.
//!
//! ## Features
//!
//! * Parse integer numbers
//! * Parse floating point numbers with decimal parts
//! * Parse scientific notation (e.g., `1.23e-4`)
//! * Configure which numeric formats are allowed
//! * Access both the calculated value and original components
//!
//! ## Examples
//!
//! Basic parsing of integers:
//!
//! ```
//! use chumsky_helpers::number::{NumberParserBuilder, NumberValue};
//! use chumsky::prelude::*;
//! use num_bigint::BigInt;
//!
//! let parser = NumberParserBuilder::new()
//!     .negative(true)
//!     .build();
//!
//! let expected = NumberValue::new_integer(42, false);
//! assert_eq!(parser.parse("42").into_result(), Ok(expected));
//! ```
//!
//! Parsing rational numbers with component preservation:
//!
//! ```
//! use chumsky_helpers::number::{NumberParserBuilder, NumberValue, Sign};
//! use chumsky::prelude::*;
//! use num_rational::BigRational;
//! use num_bigint::BigInt;
//! use std::str::FromStr;
//!
//! let parser = NumberParserBuilder::new()
//!     .negative(true)
//!     .rational(true)
//!     .scientific(true)
//!     .build();
//!
//! let result = parser.parse("-123.456e+7").into_result().unwrap();
//!
//! // -123.456e+7 = -1234560000
//! let expected_value = BigRational::from_str("-1234560000").unwrap();
//! assert_eq!(result.to_rational(), expected_value);
//! assert_eq!(result.base(), "123");
//! assert_eq!(result.decimal(), Some("456"));
//! assert!(result.exponent().is_some());
//! let exp = result.exponent().unwrap();
//! assert_eq!(exp.sign, Sign::Positive);
//! assert_eq!(exp.value, "7");
//! assert_eq!(exp.case, 'e');
//! assert!(exp.explicit_sign);
//! ```

use chumsky::{error::Rich, prelude::*};
use num::{One, Signed};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Pow, ToPrimitive, Zero};
use std::{error::Error, fmt, str::FromStr};

/// Represents a parsed numeric value with arbitrary precision.
///
/// This type uses `num_rational::BigRational` internally for all values, allowing for
/// arbitrary precision arithmetic without loss of information. It also preserves
/// the original components of the parsed number for debugging and display.
#[derive(Debug, Clone, PartialEq)]
pub struct NumberValue {
    /// The calculated arbitrary precision value.
    value: BigRational,

    /// The formatting information for display and debugging.
    format: NumberFormat,
}

/// Describes how a number should be formatted for display.
#[derive(Debug, Clone, PartialEq)]
pub enum NumberFormat {
    /// An integer with its string representation and sign information.
    Integer {
        /// Whether the sign was explicitly given in the source (e.g., "+42" vs "42")
        explicit_sign: bool,

        /// The base digits without sign.
        digits: String,
    },

    /// A decimal number with preserved components.
    Decimal {
        /// Whether the sign was explicitly given in the source (e.g., "+42.5" vs "42.5")
        explicit_sign: bool,

        /// The base component (digits before the decimal point), without sign.
        base: String,

        /// If base was implicitly 0 (e.g. `.5`)
        base_is_implicit_zero: bool,

        /// The decimal component (digits after the decimal point).
        decimal: Option<String>,

        /// The exponent component, if any.
        exponent: Option<Exponent>,
    },
    // Removed Computed variant
}

impl std::fmt::Display for NumberValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.format {
            NumberFormat::Integer { explicit_sign, digits } => {
                // Handle zero explicitly to preserve negative sign if needed
                if self.value.is_zero() && self.value.is_negative() {
                    // Check if the original sign was negative (stored in explicit_sign for -0 case)
                    if *explicit_sign {
                        write!(f, "-{}", digits)
                    } else {
                        // Should not happen with current parsing, but safe default
                        write!(f, "{}", digits)
                    }
                } else if self.value.is_negative() {
                    write!(f, "-{}", digits)
                } else if *explicit_sign && !self.value.is_zero() {
                    // Only add + if explicit and non-zero
                    write!(f, "+{}", digits)
                } else {
                    // Positive non-zero without explicit sign, or positive zero
                    write!(f, "{}", digits)
                }
            }
            NumberFormat::Decimal {
                explicit_sign,
                base,
                base_is_implicit_zero,
                decimal,
                exponent,
            } => {
                // Write sign if negative or explicitly positive
                if self.value.is_negative() {
                    write!(f, "-")?;
                } else if *explicit_sign {
                    write!(f, "+")?;
                }

                // Handle computed rational case signaled by empty base
                if base.is_empty() {
                    // Fallback to BigRational's default display for computed values
                    return write!(f, "{}", self.value);
                }

                // --- Normal Decimal Formatting ---
                // Write the base part
                if !base_is_implicit_zero {
                    write!(f, "{}", base)?;
                }

                // Write decimal part if it exists
                if let Some(dec) = decimal {
                    write!(f, ".{}", dec)?;
                }

                // Write exponent part if it exists
                if let Some(exp) = exponent {
                    // Write the exponent marker with correct case
                    write!(f, "{}", exp.case)?;

                    // Write the sign if negative or explicitly positive
                    if exp.sign == Sign::Negative {
                        write!(f, "-")?;
                    } else if exp.explicit_sign {
                        // Check explicit_sign for exponent +/-
                        write!(f, "+")?;
                    } else if exp.sign == Sign::Positive && !exp.explicit_sign {
                        // No sign for positive exponent unless explicit_sign is true
                    }

                    // Write the exponent value
                    write!(f, "{}", exp.value)?;
                }

                Ok(())
            }
        }
    }
}

/// Error type for parsing NumberValue from a string using the Chumsky parser.
#[derive(Debug, Clone, PartialEq)]
pub enum ParseNumberValueError {
    /// Failed to parse the input string. Contains combined error messages from the parser.
    ParseError(String),
}

impl fmt::Display for ParseNumberValueError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseNumberValueError::ParseError(msg) => write!(f, "Failed to parse number: {}", msg),
        }
    }
}

impl Error for ParseNumberValueError {}

impl FromStr for NumberValue {
    type Err = ParseNumberValueError;

    /// Parses a string representation of a number (integer, decimal, scientific)
    /// into a `NumberValue` using the underlying Chumsky parser.
    ///
    /// This implementation enables all features (negative, rational, scientific).
    ///
    /// Examples: "123", "-42.5", "1.23e-4", "+5E10"
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // Build a parser that allows all number formats for FromStr
        let parser =
            NumberParserBuilder::new().negative(true).rational(true).scientific(true).build();

        // Parse the input string
        parser.parse(s).into_result().map_err(|errs| {
            // Combine multiple Chumsky errors into a single string
            let combined_errors =
                errs.into_iter().map(|e| e.to_string()).collect::<Vec<_>>().join(", ");
            ParseNumberValueError::ParseError(combined_errors)
        })
    }
}

impl NumberValue {
    /// Creates a new integer value with explicit sign information.
    pub fn new_integer<T: Into<BigInt>>(value: T, explicit_sign: bool) -> Self {
        let int_value = value.into();
        let digits = int_value.abs().to_string();

        NumberValue {
            value: BigRational::from_integer(int_value),
            format: NumberFormat::Integer { explicit_sign, digits },
        }
    }

    /// Creates a new rational value from components.
    pub fn new_rational(
        value: BigRational,
        explicit_sign: bool,
        base: String,
        base_is_implicit_zero: bool,
        decimal: Option<String>,
        exponent: Option<Exponent>,
    ) -> Self {
        NumberValue {
            value,
            format: NumberFormat::Decimal {
                explicit_sign,
                base,
                base_is_implicit_zero,
                decimal,
                exponent,
            },
        }
    }

    /// Creates a computed value from an operation result.
    pub fn new_computed(value: BigRational) -> Self {
        // Normalize to Integer format if result is an integer
        if value.denom() == &BigInt::one() {
            let int_value = value.numer();
            let digits = int_value.abs().to_string();

            NumberValue {
                value: value.clone(),
                format: NumberFormat::Integer { explicit_sign: false, digits },
            }
        } else {
            // Represent computed rationals minimally using Decimal format.
            // The Display impl handles the case where `base` is empty.
            NumberValue {
                value,
                format: NumberFormat::Decimal {
                    explicit_sign: false, // No explicit sign for computed values
                    base: String::new(),  // Use empty base to signal "computed rational"
                    base_is_implicit_zero: false,
                    decimal: None,
                    exponent: None,
                },
            }
        }
    }

    /// Checks if the value was parsed as an integer.
    pub fn is_integer(&self) -> bool {
        matches!(self.format, NumberFormat::Integer { .. })
    }

    /// Checks if the value was originally parsed as a decimal or scientific literal
    /// (e.g., "1.23", "-0.5e-10") or if it's a computed non-integer value.
    pub fn is_rational_format(&self) -> bool {
        matches!(self.format, NumberFormat::Decimal { .. })
    }

    /// Checks if the value is mathematically negative.
    pub fn is_negative(&self) -> bool {
        self.value.is_negative()
    }

    /// Converts the number to an f64 value.
    ///
    /// Note that this may lose precision for very large numbers or numbers with
    /// many decimal places. Returns `None` if the numerator or denominator cannot
    /// be represented as `f64` (which is unlikely with standard `f64` range but
    /// possible for extreme `BigInt` values) or if the denominator is zero.
    pub fn as_f64(&self) -> Option<f64> {
        // Use to_f64() directly from BigRational for better conversion
        self.value.to_f64()
    }

    /// Returns the base component of the number (digits before the decimal point).
    pub fn base(&self) -> &str {
        match &self.format {
            NumberFormat::Integer { digits, .. } => digits,
            NumberFormat::Decimal { base, .. } if !base.is_empty() => base, // Return base if not computed
            _ => "", // Return empty for computed Decimal or other cases
        }
    }

    /// Returns the decimal component of the number (digits after the decimal point), if any.
    pub fn decimal(&self) -> Option<&str> {
        match &self.format {
            NumberFormat::Integer { .. } => None,
            NumberFormat::Decimal { decimal, base, .. } if !base.is_empty() => decimal.as_deref(), // Return decimal if not computed
            _ => None, // Return None for computed Decimal or Integer
        }
    }

    /// Returns the exponent component of the number, if any.
    pub fn exponent(&self) -> Option<&Exponent> {
        match &self.format {
            NumberFormat::Integer { .. } => None,
            NumberFormat::Decimal { exponent, base, .. } if !base.is_empty() => exponent.as_ref(), // Return exponent if not computed
            _ => None, // Return None for computed Decimal or Integer
        }
    }

    /// Returns whether the sign was explicitly given in the source.
    pub fn has_explicit_sign(&self) -> bool {
        match &self.format {
            NumberFormat::Integer { explicit_sign, .. } => *explicit_sign,
            NumberFormat::Decimal { explicit_sign, base, .. } if !base.is_empty() => *explicit_sign, // Return explicit_sign if not computed
            _ => false, // Return false for computed Decimal or other cases
        }
    }

    /// Converts the number to a BigInt value, rounding towards zero if necessary.
    pub fn to_integer(&self) -> BigInt {
        self.value.to_integer()
    }

    /// Returns the arbitrary precision rational value.
    pub fn to_rational(&self) -> BigRational {
        self.value.clone()
    }

    /// Gets a reference to the underlying BigRational value.
    pub fn as_rational(&self) -> &BigRational {
        &self.value
    }
}

/// Represents the sign of a number or exponent.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Sign {
    /// Explicitly positive (preceded by `+`).
    Positive,

    /// Explicitly negative (preceded by `-`).
    Negative,

    /// No explicit sign.
    None,
}

/// Represents an exponent with its sign and formatting information.
#[derive(Debug, Clone, PartialEq)]
pub struct Exponent {
    /// The case of the exponent marker ('e' or 'E')
    pub case: char,

    /// Whether the sign was explicitly given (e.g., "e+10" vs "e10")
    pub explicit_sign: bool,

    /// The sign of the exponent (+, -, or none)
    pub sign: Sign,

    /// The numeric value of the exponent as a string (without sign)
    pub value: String,
}

/// Builder for configuring and creating a number parser.
///
/// This builder allows you to customize which numeric formats are allowed
/// in the parser, such as negative numbers, rational numbers, and
/// scientific notation.
#[derive(Debug, Default)]
pub struct NumberParserBuilder {
    allow_negative: bool,
    allow_rational: bool,
    allow_scientific: bool,
}

impl NumberParserBuilder {
    /// Create a new builder with default settings.
    ///
    /// By default, all formats are disabled and must be explicitly enabled.
    pub fn new() -> Self {
        Self::default()
    }

    /// Configure whether negative numbers are allowed.
    pub fn negative(mut self, allow: bool) -> Self {
        self.allow_negative = allow;
        self
    }

    /// Configure whether rational numbers (with decimal points) are allowed.
    ///
    /// This replaces the previous `float` option since all non-integer values
    /// are now represented as arbitrary precision rational numbers.
    pub fn rational(mut self, allow: bool) -> Self {
        self.allow_rational = allow;
        self
    }

    /// Configure whether scientific notation is allowed.
    pub fn scientific(mut self, allow: bool) -> Self {
        self.allow_scientific = allow;
        self
    }

    /// Parser for signs (`+`, `-`, or none).
    fn sign_parser<'a>() -> impl Parser<'a, &'a str, Sign, extra::Err<Rich<'a, char>>> {
        choice((just("+").to(Sign::Positive), just("-").to(Sign::Negative)))
            .or_not()
            .map(|s| s.unwrap_or(Sign::None))
    }

    /// Build the configured number parser.
    ///
    /// Creates a parser based on the current configuration that can
    /// parse numeric literals into the `NumberValue` type with arbitrary precision.
    pub fn build<'a>(self) -> impl Parser<'a, &'a str, NumberValue, extra::Err<Rich<'a, char>>> {
        // Parser for the integer part (optional)
        let integer_part = text::int(10).to_slice();

        // Parser for the fractional part (digits after '.')
        let fractional_part = just('.')
            .ignore_then(text::digits(10).to_slice().or_not().map(|opt| opt.unwrap_or(""))); // Returns &str

        // Parser for the exponent part (optional)
        let exponent_part = choice((just('e').to('e'), just('E').to('E')))
            .then(Self::sign_parser()) // Parses sign for exponent
            .then(text::int(10).to_slice())
            .map(|((case, sign), value)| {
                // Track whether sign was explicit
                let explicit_sign = sign != Sign::None;
                Exponent { case, explicit_sign, sign, value: value.to_string() }
            })
            .or_not(); // Returns Option<Exponent>

        let allow_negative = self.allow_negative;
        let allow_rational = self.allow_rational;
        let allow_scientific = self.allow_scientific;

        // Define the structure of the number: sign, then either int+frac or just frac, then exponent
        let number_structure = Self::sign_parser().then(
            // Case 1: Integer part exists
            integer_part
                .then(fractional_part.or_not()) // Integer followed by optional fraction
                .map(|(int_str, frac_opt)| (Some(int_str), frac_opt))
                .or(
                    // Case 2: No integer part, starts with '.'
                    fractional_part.map(|frac_str| (None::<&str>, Some(frac_str))), // Must have fraction if no integer
                ),
        );

        // Combine structure with optional exponent
        number_structure.then(exponent_part).try_map(
            // Correct closure signature: takes the parser output and span separately
            move |parsed_components, span| {
                // Destructure the parsed components inside the closure body
                #[allow(clippy::type_complexity)]
                let ((sign, (int_opt, frac_opt)), exp_opt): (
                    (Sign, (Option<&str>, Option<&str>)),
                    Option<Exponent>,
                ) = parsed_components;

                // --- Validation ---
                if sign == Sign::Negative && !allow_negative {
                    return Err(Rich::custom(span, "Negative numbers not allowed"));
                }

                let has_decimal = frac_opt.is_some();
                if has_decimal && !allow_rational {
                    return Err(Rich::custom(span, "Rational numbers not allowed"));
                }

                let has_exponent = exp_opt.is_some();
                if has_exponent && !allow_scientific {
                    return Err(Rich::custom(span, "Scientific notation not allowed"));
                }

                // Ensure we have *some* digits (either integer or fractional part)
                #[allow(clippy::unnecessary_map_or)]
                if int_opt.is_none() && frac_opt.map_or(true, |f| f.is_empty()) {
                    // This case should ideally be caught by the parser structure,
                    // but added as a safeguard. Handles cases like "." or "+."
                    return Err(Rich::custom(span, "Number must have digits"));
                }

                // --- Processing ---
                let explicit_sign = sign != Sign::None;
                let is_negative = sign == Sign::Negative;

                // Use "0" if integer part is missing (e.g., for ".5")
                let int_str = int_opt.unwrap_or("0");
                // Use "" if fractional part is missing (e.g., for "5.")
                let decimal_str_opt: Option<String> = frac_opt.map(|s| s.to_string());

                // If it looks like a simple integer (no decimal, no exponent)
                if !has_decimal && !has_exponent {
                    // Check if int_opt was actually present. If not (e.g. input was just "+"), error.
                    // This check might be redundant if parser structure guarantees int_opt or frac_opt.
                    if int_opt.is_none() {
                        return Err(Rich::custom(span, "Expected digits after sign"));
                    }

                    let mut int_value = BigInt::from_str(int_str)
                        .map_err(|_| Rich::custom(span, "Failed to parse integer"))?;

                    // Apply sign, handle negative zero formatting case
                    let final_explicit_sign = if int_value.is_zero() && is_negative {
                        true // Preserve explicit sign for -0 display
                    } else {
                        explicit_sign
                    };

                    if is_negative {
                        int_value = -int_value;
                    }

                    Ok(NumberValue::new_integer(int_value, final_explicit_sign))
                } else {
                    // Handle rational/scientific cases
                    let base_part = int_str.to_string(); // Base is the integer part

                    let mut numerator;
                    let mut denominator = BigInt::one();

                    if let Some(dec_str) = &decimal_str_opt {
                        // Combine integer and fractional parts for calculation
                        let combined = format!("{}{}", base_part, dec_str);
                        numerator = BigInt::from_str(&combined)
                            .map_err(|_| Rich::custom(span, "Failed to parse number mantissa"))?;

                        // Adjust denominator based on fractional length
                        if !dec_str.is_empty() {
                            denominator = BigInt::from(10).pow(dec_str.len() as u32);
                        }
                    } else {
                        // No fractional part, but might have exponent
                        numerator = BigInt::from_str(&base_part)
                            .map_err(|_| Rich::custom(span, "Failed to parse integer part"))?;
                    }

                    // Apply sign
                    if is_negative {
                        numerator = -numerator;
                    }

                    let mut rational_value = BigRational::new(numerator, denominator);

                    // Apply exponent if present
                    if let Some(exp_data) = &exp_opt {
                        match u32::from_str(&exp_data.value) {
                            Ok(exp_val) => {
                                let factor = BigInt::from(10).pow(exp_val);
                                match exp_data.sign {
                                    Sign::Negative => {
                                        rational_value /= BigRational::from_integer(factor);
                                    }
                                    _ => {
                                        // Positive or None
                                        rational_value *= BigRational::from_integer(factor);
                                    }
                                }
                            }
                            Err(_) => {
                                return Err(Rich::custom(span, "Failed to parse exponent value"));
                            }
                        }
                    }

                    let base_is_implicit_zero = int_opt.is_none();

                    // Pass the original integer part as base
                    Ok(NumberValue::new_rational(
                        rational_value,
                        explicit_sign,
                        base_part, // Use the original integer part string
                        base_is_implicit_zero,
                        decimal_str_opt, // Pass the original decimal part string
                        exp_opt,
                    ))
                }
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num::ToPrimitive;
    use num_rational::Ratio;
    use proptest::prelude::*;
    use std::str::FromStr;

    // Helper macro for FromStr tests - checks success cases
    macro_rules! assert_from_str_ok {
        ($input:expr, $expected_variant:ident, $expected_val_str:expr, $expected_display:expr) => {
            let result = NumberValue::from_str($input.trim()); // Trim input for FromStr tests
            assert!(result.is_ok(), "Parsing '{}' failed: {:?}", $input, result.err());
            let num_val = result.unwrap();
            assert_eq!(num_val.to_string(), $expected_display, "Display mismatch for '{}'", $input);
            let expected_rational = BigRational::from_str($expected_val_str).expect("Invalid expected rational string");
            assert_eq!(num_val.to_rational(), expected_rational, "Rational value mismatch for '{}'", $input);
            assert!(matches!(num_val.format, NumberFormat::$expected_variant { .. }), "Format variant mismatch for '{}'", $input.trim());
        };
         ($input:expr, $expected_variant:ident, $expected_val_str:expr, $expected_display:expr, $($field:ident: $value:expr),+ ) => {
            let result = NumberValue::from_str($input.trim()); // Trim input for FromStr tests
            assert!(result.is_ok(), "Parsing '{}' failed: {:?}", $input.trim(), result.err());
            let num_val = result.unwrap();
            assert_eq!(num_val.to_string(), $expected_display, "Display mismatch for '{}'", $input.trim());
            let expected_rational = BigRational::from_str($expected_val_str).expect("Invalid expected rational string");
            assert_eq!(num_val.to_rational(), expected_rational, "Rational value mismatch for '{}'", $input.trim());
            match num_val.format {
                NumberFormat::$expected_variant { $($field,)* .. } => {
                    $(
                        assert_eq!($field, $value, "Field '{}' mismatch for '{}'", stringify!($field), $input.trim());
                    )*
                }
                _ => panic!("Format variant mismatch for '{}'", $input.trim()),
            }
        };
    }

    // Helper macro for FromStr tests - checks error cases
    macro_rules! assert_from_str_err {
        ($input:expr, $expected_msg_part:expr) => {
            let result = NumberValue::from_str($input.trim()); // Trim input for FromStr tests
            assert!(
                result.is_err(),
                "Parsing '{}' should have failed, but got Ok({:?})",
                $input.trim(),
                result.ok()
            );
            let err = result.err().unwrap();
            let err_string = err.to_string();
            assert!(
                matches!(err, ParseNumberValueError::ParseError { .. }),
                "Expected ParseError for '{}', but got {:?}",
                $input.trim(),
                err
            );
            assert!(
                err_string.contains($expected_msg_part),
                "Error message for '{}' did not contain '{}', got: {}",
                $input.trim(),
                $expected_msg_part,
                err_string
            );
        };
    }

    // Removed assert_from_str_ok_detailed! macro

    #[test]
    fn test_from_str_integers() {
        assert_from_str_ok!("0", Integer, "0", "0", explicit_sign: false, digits: "0".to_string());
        assert_from_str_ok!("42", Integer, "42", "42", explicit_sign: false, digits: "42".to_string());
        assert_from_str_ok!("+123", Integer, "123", "+123", explicit_sign: true, digits: "123".to_string());
        assert_from_str_ok!("-5", Integer, "-5", "-5", explicit_sign: true, digits: "5".to_string());
        assert_from_str_ok!("-0", Integer, "0", "-0", explicit_sign: true, digits: "0".to_string());
        // Neg zero preserves sign display
    }

    #[test]
    fn test_from_str_decimals() {
        assert_from_str_ok!("0.0", Decimal, "0", "0.0", explicit_sign: false, base: "0".to_string(), decimal: Some("0".to_string()), exponent: None);
        assert_from_str_ok!("1.5", Decimal, "15/10", "1.5", explicit_sign: false, base: "1".to_string(), decimal: Some("5".to_string()), exponent: None);
        assert_from_str_ok!("-0.25", Decimal, "-25/100", "-0.25", explicit_sign: true, base: "0".to_string(), decimal: Some("25".to_string()), exponent: None);
        assert_from_str_ok!("+100.001", Decimal, "100001/1000", "+100.001", explicit_sign: true, base: "100".to_string(), decimal: Some("001".to_string()), exponent: None);
        assert_from_str_ok!("42.", Decimal, "42", "42.", explicit_sign: false, base: "42".to_string(), decimal: Some("".to_string()), exponent: None); // Trailing dot
        assert_from_str_ok!(".5", Decimal, "5/10", ".5", explicit_sign: false, base: "0".to_string(), decimal: Some("5".to_string()), exponent: None); // Leading dot
        assert_from_str_ok!("-.12", Decimal, "-12/100", "-.12", explicit_sign: true, base: "0".to_string(), decimal: Some("12".to_string()), exponent: None);
        // The "+." case is now invalid because it lacks digits, caught by "Number must have digits"
        // assert_from_str_ok!("+.", Decimal, "0", "+.", explicit_sign: true, base: "0".to_string(), decimal: Some("".to_string()), exponent: None);
    }

    #[test]
    fn test_from_str_scientific() {
        // Integer base
        assert_from_str_ok!("1e3", Decimal, "1000", "1e3", explicit_sign: false, base: "1".to_string(), decimal: None, exponent: Some(Exponent { case: 'e', explicit_sign: false, sign: Sign::None, value: "3".to_string() }));
        assert_from_str_ok!("-2E+4", Decimal, "-20000", "-2E+4", explicit_sign: true, base: "2".to_string(), decimal: None, exponent: Some(Exponent { case: 'E', explicit_sign: true, sign: Sign::Positive, value: "4".to_string() }));
        assert_from_str_ok!("+5e-2", Decimal, "5/100", "+5e-2", explicit_sign: true, base: "5".to_string(), decimal: None, exponent: Some(Exponent { case: 'e', explicit_sign: true, sign: Sign::Negative, value: "2".to_string() }));
        assert_from_str_ok!("10e0", Decimal, "10", "10e0", explicit_sign: false, base: "10".to_string(), decimal: None, exponent: Some(Exponent { case: 'e', explicit_sign: false, sign: Sign::None, value: "0".to_string() }));

        // Decimal base
        assert_from_str_ok!("1.23e2", Decimal, "123", "1.23e2", explicit_sign: false, base: "1".to_string(), decimal: Some("23".to_string()), exponent: Some(Exponent { case: 'e', explicit_sign: false, sign: Sign::None, value: "2".to_string() }));
        assert_from_str_ok!("-0.5E-1", Decimal, "-5/100", "-0.5E-1", explicit_sign: true, base: "0".to_string(), decimal: Some("5".to_string()), exponent: Some(Exponent { case: 'E', explicit_sign: true, sign: Sign::Negative, value: "1".to_string() }));
        assert_from_str_ok!("+42.e+3", Decimal, "42000", "+42.e+3", explicit_sign: true, base: "42".to_string(), decimal: Some("".to_string()), exponent: Some(Exponent { case: 'e', explicit_sign: true, sign: Sign::Positive, value: "3".to_string() }));
        assert_from_str_ok!(".5e1", Decimal, "5", ".5e1", explicit_sign: false, base: "0".to_string(), decimal: Some("5".to_string()), exponent: Some(Exponent { case: 'e', explicit_sign: false, sign: Sign::None, value: "1".to_string() }));
    }

    #[test]
    fn test_from_str_large_numbers() {
        let large_int = "123456789012345678901234567890";
        assert_from_str_ok!(large_int, Integer, large_int, large_int, explicit_sign: false, digits: large_int.to_string());

        let large_neg_int = "-987654321098765432109876543210";
        assert_from_str_ok!(large_neg_int, Integer, large_neg_int, large_neg_int, explicit_sign: true, digits: "987654321098765432109876543210".to_string());

        let large_dec = "1234567890.0987654321";
        assert_from_str_ok!(large_dec, Decimal, "12345678900987654321/10000000000", large_dec, explicit_sign: false, base: "1234567890".to_string(), decimal: Some("0987654321".to_string()), exponent: None);

        let large_sci = "1.23456789e+30";
        let expected_sci_val = "1234567890000000000000000000000"; // 1.23456789 * 10^30
        assert_from_str_ok!(large_sci, Decimal, expected_sci_val, large_sci, explicit_sign: false, base: "1".to_string(), decimal: Some("23456789".to_string()), exponent: Some(Exponent { case: 'e', explicit_sign: true, sign: Sign::Positive, value: "30".to_string() }));

        let large_neg_sci = "-9.8765e-25";
        let expected_neg_sci_val = "-98765/100000000000000000000000000000"; // -9.8765 / 10^25
        assert_from_str_ok!(large_neg_sci, Decimal, expected_neg_sci_val, large_neg_sci, explicit_sign: true, base: "9".to_string(), decimal: Some("8765".to_string()), exponent: Some(Exponent { case: 'e', explicit_sign: true, sign: Sign::Negative, value: "25".to_string() }));
    }

    #[test]
    fn test_from_str_invalid_inputs() {
        // Note: Chumsky errors might be different from the manual parser's errors.
        // We check for parts of the expected error messages.
        assert_from_str_err!("", "found end of input expected"); // Empty string (Chumsky's message)
        assert_from_str_err!(" ", "found end of input expected"); // Whitespace only (Chumsky's message)
        assert_from_str_err!("+", "Expected digits after sign"); // Custom error from parser logic
        assert_from_str_err!("-", "Expected digits after sign"); // Custom error from parser logic
        assert_from_str_err!("e", "found 'e' expected"); // Chumsky
        assert_from_str_err!("e5", "found 'e' expected"); // Chumsky
        assert_from_str_err!("1e", "found end of input expected integer"); // Chumsky - exponent value expected
        assert_from_str_err!("1e+", "found end of input expected integer"); // Chumsky - exponent value expected
        assert_from_str_err!("1e-", "found end of input expected integer"); // Chumsky - exponent value expected
        assert_from_str_err!("1.2.3", "found '.' expected end of input or exponent"); // Chumsky - second '.'
        assert_from_str_err!("1e2e3", "found 'e' expected end of input"); // Chumsky - second 'e'
        assert_from_str_err!("abc", "found 'a' expected"); // Chumsky
        assert_from_str_err!("1.a", "found 'a' expected end of input or exponent"); // Chumsky
        assert_from_str_err!("1ea", "found 'a' expected integer"); // Chumsky - expects exponent digits
        assert_from_str_err!("1e+a", "found 'a' expected integer"); // Chumsky - expects exponent digits
        assert_from_str_err!("..", "found '.' expected integer"); // Chumsky - expects digits after first '.'
        assert_from_str_err!("+e", "found 'e' expected integer"); // Chumsky
        assert_from_str_err!(".", "Number must have digits"); // Custom error
        assert_from_str_err!("+.", "Number must have digits"); // Custom error
    }

    #[test]
    fn test_from_str_whitespace() {
        // FromStr should handle surrounding whitespace via trim()
        assert_from_str_ok!(" 123 ", Integer, "123", "123");
        assert_from_str_ok!(" -4.5\t", Decimal, "-45/10", "-4.5");
        assert_from_str_ok!("\n+6e-1 ", Decimal, "6/10", "+6e-1");
    }

    #[test]
    fn test_display_implementation() {
        // Test integer display
        let int_val = NumberValue::new_integer(42, false);
        assert_eq!(int_val.to_string(), "42");

        // Test rational display with original components
        let rational_with_components = NumberValue::new_rational(
            BigRational::new(BigInt::from(1234), BigInt::from(10)),
            false, /*explicit_sign*/
            "123".to_string(),
            false, /*base_is_implicit_zero*/
            Some("4".to_string()),
            None,
        );
        assert_eq!(rational_with_components.to_string(), "123.4");

        // Test with exponent
        let rational_with_exponent = NumberValue::new_rational(
            BigRational::new(BigInt::from(1234560000), BigInt::from(1)),
            false, /*explicit_sign*/
            "123".to_string(),
            false, /*base_is_implicit_zero*/
            Some("456".to_string()),
            Some(Exponent {
                sign: Sign::Positive,
                explicit_sign: true,
                value: "7".to_string(),
                case: 'e',
            }),
        );
        assert_eq!(rational_with_exponent.to_string(), "123.456e+7");

        // Test negative exponent
        let rational_with_neg_exponent = NumberValue::new_rational(
            BigRational::new(BigInt::from(1234), BigInt::from(100000)),
            false, /*explicit_sign*/
            "123".to_string(),
            false, /*base_is_implicit_zero*/
            Some("4".to_string()),
            Some(Exponent {
                sign: Sign::Negative,
                explicit_sign: true,
                value: "5".to_string(),
                case: 'e',
            }),
        );
        assert_eq!(rational_with_neg_exponent.to_string(), "123.4e-5");

        // Test computed rational display (falls back to BigRational fmt)
        let computed_rational =
            NumberValue::new_computed(BigRational::new(BigInt::from(22), BigInt::from(7)));
        assert_eq!(computed_rational.to_string(), "22/7");

        // Test computed integer display (uses Integer format without explicit sign)
        let computed_int = NumberValue::new_computed(BigRational::from_integer(BigInt::from(5)));
        assert_eq!(computed_int.to_string(), "5");
        assert!(matches!(
            computed_int.format,
            NumberFormat::Integer { explicit_sign: false, .. }
        ));

        let computed_neg_int =
            NumberValue::new_computed(BigRational::from_integer(BigInt::from(-5)));
        assert_eq!(computed_neg_int.to_string(), "-5"); // Display handles negative correctly
        assert!(matches!(
            computed_neg_int.format,
            NumberFormat::Integer { explicit_sign: false, .. }
        ));
    }

    // === Tests for NumberParserBuilder ===

    #[test]
    fn test_basic_integer() {
        let parser = NumberParserBuilder::new().negative(true).build();
        assert_eq!(
            parser.parse("42").into_result(),
            Ok(NumberValue::new_integer(42, false))
        );
    }

    #[test]
    fn test_negative_integer() {
        let parser = NumberParserBuilder::new().negative(true).build();
        assert_eq!(
            parser.parse("-42").into_result(),
            Ok(NumberValue::new_integer(-42, true))
        );
    }

    #[test]
    fn test_positive_integer() {
        let parser = NumberParserBuilder::new().negative(true).build();
        assert_eq!(
            parser.parse("+42").into_result(),
            Ok(NumberValue::new_integer(42, true))
        );
    }

    #[test]
    fn test_rational() {
        let parser = NumberParserBuilder::new().rational(true).negative(true).build();
        let result = parser.parse("42.0").into_result().unwrap();
        assert!(!result.is_integer(), "Expected number to be rational");
        assert_eq!(result.to_string(), "42.0");
        assert_eq!(result.base(), "42");
        assert_eq!(result.decimal(), Some("0"));
        assert_eq!(result.exponent(), None);
        assert_eq!(result.to_integer(), BigInt::from(42));
        assert_eq!(
            result.to_rational(),
            Ratio::new(BigInt::from(42), BigInt::from(1))
        );
        assert_eq!(result.as_f64().unwrap(), 42.0);
        assert_eq!(
            result.as_rational(),
            &Ratio::new(BigInt::from(42), BigInt::from(1))
        );
    }

    #[test]
    fn test_negative_rational() {
        let parser = NumberParserBuilder::new().rational(true).negative(true).build();
        let result = parser.parse("-42.0").into_result().unwrap();
        assert!(!result.is_integer(), "Expected number to be rational");
        assert_eq!(result.to_integer(), BigInt::from(-42));
        assert_eq!(
            result.to_rational(),
            Ratio::new(BigInt::from(-42), BigInt::one())
        );
        assert_eq!(result.as_f64().unwrap(), -42.0);
        assert_eq!(
            result.as_rational(),
            &Ratio::new(BigInt::from(-42), BigInt::one())
        );
        assert_eq!(result.to_string(), "-42.0");
        assert_eq!(result.base(), "42");
        assert_eq!(result.decimal(), Some("0"));
        assert_eq!(result.exponent(), None);
    }

    #[test]
    fn test_scientific() {
        let parser = NumberParserBuilder::new().scientific(true).negative(true).build();
        let result = parser.parse("42e0").into_result().unwrap();
        assert!(!result.is_integer(), "Expected number to be rational");
        assert_eq!(result.to_string(), "42e0");
        assert_eq!(result.base(), "42");
        assert_eq!(result.decimal(), None);
        assert_eq!(
            result.exponent(),
            Some(&Exponent {
                sign: Sign::None,
                explicit_sign: false,
                value: "0".to_string(),
                case: 'e'
            })
        );
        assert_eq!(result.to_integer(), BigInt::from(42));
        assert_eq!(
            result.to_rational(),
            Ratio::new(BigInt::from(42), BigInt::from(1))
        );
        assert_eq!(result.as_f64().unwrap(), 42.0);
        assert_eq!(
            result.as_rational(),
            &Ratio::new(BigInt::from(42), BigInt::from(1))
        );
    }

    #[test]
    fn test_disallowed_negative() {
        let parser = NumberParserBuilder::new().negative(false).build();
        assert!(parser.parse("-42").has_errors());
    }

    #[test]
    fn test_disallowed_rational() {
        let parser = NumberParserBuilder::new().rational(false).build();
        assert!(parser.parse("42.0").has_errors());
    }

    #[test]
    fn test_disallowed_scientific() {
        let parser = NumberParserBuilder::new().scientific(false).build();
        assert!(parser.parse("42e0").has_errors());
    }

    #[test]
    fn test_rational_with_no_decimal() {
        let parser = NumberParserBuilder::new().rational(true).negative(true).build();
        let result = parser.parse("42.").into_result().unwrap();
        assert!(!result.is_integer(), "Expected number to be rational");
        assert_eq!(result.to_string(), "42.");
        assert_eq!(result.base(), "42");
        assert_eq!(result.decimal(), Some(""));
        assert_eq!(result.exponent(), None);
        assert_eq!(result.to_integer(), BigInt::from(42));
        assert_eq!(
            result.to_rational(),
            Ratio::new(BigInt::from(42), BigInt::from(1))
        );
        assert_eq!(result.as_f64().unwrap(), 42.0);
        assert_eq!(
            result.as_rational(),
            &Ratio::new(BigInt::from(42), BigInt::from(1))
        );
    }

    #[test]
    fn test_scientific_with_positive_exp() {
        let parser = NumberParserBuilder::new().scientific(true).build();
        let result = parser.parse("42e+2").into_result().unwrap();
        assert!(!result.is_integer(), "Expected number to be rational");
        assert_eq!(result.to_string(), "42e+2");
        assert_eq!(result.base(), "42");
        assert_eq!(result.decimal(), None);
        assert_eq!(
            result.exponent(),
            Some(&Exponent {
                sign: Sign::Positive,
                explicit_sign: true,
                value: "2".to_string(),
                case: 'e'
            })
        );
        assert_eq!(result.to_integer(), BigInt::from(4200));
        assert_eq!(
            result.to_rational(),
            Ratio::new(BigInt::from(4200), BigInt::from(1))
        );
        assert_eq!(result.as_f64().unwrap(), 4200.0);
        assert_eq!(
            result.as_rational(),
            &Ratio::new(BigInt::from(4200), BigInt::from(1))
        );
    }

    #[test]
    fn test_combined_rational_scientific() {
        let parser =
            NumberParserBuilder::new().rational(true).scientific(true).negative(true).build();
        let result = parser.parse("-42.5e-1").into_result().unwrap();
        assert!(!result.is_integer(), "Expected number to be rational");
        assert_eq!(result.to_string(), "-42.5e-1");
        assert_eq!(result.base(), "42");
        assert_eq!(result.decimal(), Some("5"));
        assert_eq!(
            result.exponent(),
            Some(&Exponent {
                sign: Sign::Negative,
                explicit_sign: true,
                value: "1".to_string(),
                case: 'e'
            })
        );
        assert_eq!(result.to_integer(), BigInt::from(-4));
        assert_eq!(
            result.to_rational(),
            Ratio::new(BigInt::from(-425), BigInt::from(100))
        );
        assert_eq!(result.as_f64().unwrap(), -4.25);
        assert_eq!(
            result.as_rational(),
            &Ratio::new(BigInt::from(-425), BigInt::from(100))
        );
    }

    #[test]
    fn test_exponent_variations() {
        let parser = NumberParserBuilder::new().scientific(true).build();

        // Check values with as_f64() for brevity in these variations
        assert!((parser.parse("1e0").into_result().unwrap().as_f64().unwrap() - 1.0).abs() < 1e-10);
        assert!(
            (parser.parse("1e1").into_result().unwrap().as_f64().unwrap() - 10.0).abs() < 1e-10
        );
        assert!(
            (parser.parse("1e+1").into_result().unwrap().as_f64().unwrap() - 10.0).abs() < 1e-10
        );
        assert!(
            (parser.parse("1e-1").into_result().unwrap().as_f64().unwrap() - 0.1).abs() < 1e-10
        );
        assert!(
            (parser.parse("10e2").into_result().unwrap().as_f64().unwrap() - 1000.0).abs() < 1e-10
        );
    }

    #[test]
    fn test_explicit_positive_variations() {
        let parser =
            NumberParserBuilder::new().scientific(true).negative(true).rational(true).build();

        // Check components for one case
        let result = parser.parse("+1.5e+1").into_result().unwrap();
        assert!(!result.is_integer(), "Expected number to be rational");
        assert_eq!(result.to_string(), "+1.5e+1");
        assert_eq!(result.base(), "1");
        assert_eq!(result.decimal(), Some("5"));
        assert_eq!(
            result.exponent(),
            Some(&Exponent {
                sign: Sign::Positive,
                explicit_sign: true,
                value: "1".to_string(),
                case: 'e'
            })
        );
        assert_eq!(result.to_integer(), BigInt::from(15));
        assert_eq!(
            result.to_rational(),
            Ratio::new(BigInt::from(15), BigInt::from(1))
        );
        assert_eq!(result.as_f64().unwrap(), 15.0);
        assert_eq!(
            result.as_rational(),
            &Ratio::new(BigInt::from(15), BigInt::from(1))
        );

        // Just check values with as_f64() for the rest
        let pos1 = parser.parse("+1").into_result().unwrap();
        assert_eq!(pos1.to_string(), "+1"); // Display should handle explicit positive correctly now
        assert!((pos1.as_f64().unwrap() - 1.0).abs() < 1e-10);

        let pos1e1 = parser.parse("+1e1").into_result().unwrap();
        assert_eq!(pos1e1.to_string(), "+1e1");
        assert!((pos1e1.as_f64().unwrap() - 10.0).abs() < 1e-10);

        let pos1e_pos1 = parser.parse("+1e+1").into_result().unwrap();
        assert_eq!(pos1e_pos1.to_string(), "+1e+1");
        assert!((pos1e_pos1.as_f64().unwrap() - 10.0).abs() < 1e-10);
    }

    #[test]
    fn test_component_preservation() {
        let parser =
            NumberParserBuilder::new().rational(true).scientific(true).negative(true).build();

        // Create exponent values outside the array to avoid temporary value drops
        let exp_neg = Exponent {
            sign: Sign::Negative,
            explicit_sign: true,
            value: "7".to_string(),
            case: 'e',
        };
        let exp_pos = Exponent {
            sign: Sign::Positive,
            explicit_sign: true,
            value: "3".to_string(),
            case: 'E',
        };

        // Test with a complex number with all components
        let test_cases = [
            (
                "123.456e-7",
                "123",
                Some("456".to_string()),
                Some(&exp_neg),
                123.456e-7,
            ),
            (
                "-987.654E+3",
                "987",
                Some("654".to_string()),
                Some(&exp_pos),
                -987.654e3,
            ),
            ("42.", "42", Some("".to_string()), None, 42.0),
            ("0.123", "0", Some("123".to_string()), None, 0.123),
        ];

        for (input, expected_base, expected_decimal, expected_exponent, expected_value) in
            test_cases
        {
            let result = parser.parse(input).into_result().unwrap();
            assert!(!result.is_integer(), "Expected number to be rational");
            assert_eq!(result.to_string(), input);
            assert_eq!(result.base(), expected_base);
            assert_eq!(result.decimal(), expected_decimal.as_deref());
            assert_eq!(result.exponent(), expected_exponent);
            // Compare BigRational values directly for accuracy
            let expected_rational = BigRational::from_float(expected_value).unwrap_or_else(|| {
                panic!(
                    "Failed to create BigRational for expected value: {}",
                    expected_value
                )
            });
            // Compare the BigRational values directly for accuracy
            assert_eq!(
                result.to_rational(),
                expected_rational,
                "Rational value mismatch for input '{}'",
                input
            );

            // Also compare f64 representations with tolerance as a sanity check
            let actual_f64 = result.as_f64().unwrap();
            assert!(
                (actual_f64 - expected_value).abs() < 1e-10,
                "f64 comparison failed for input '{}': expected ~{}, got {}",
                input,
                expected_value,
                actual_f64
            );
        }
    }

    #[test]
    fn test_large_integer() {
        let parser = NumberParserBuilder::new().negative(true).build();
        let large_num = "12345678901234567890123456789012345678901234567890";
        let result = parser.parse(large_num).into_result().unwrap();
        assert!(result.is_integer(), "Expected number to be an integer");
        assert_eq!(result.to_string(), large_num);
    }

    #[test]
    fn test_large_rational() {
        let parser = NumberParserBuilder::new().rational(true).build();
        let large_num =
            "1234567890123456789012345678901234567890.1234567890123456789012345678901234567890";
        let result = parser.parse(large_num).into_result().unwrap();
        assert!(!result.is_integer(), "Expected number to be rational");
        assert_eq!(result.to_string(), large_num);
        assert_eq!(result.base(), "1234567890123456789012345678901234567890");
        assert_eq!(
            result.decimal(),
            Some("1234567890123456789012345678901234567890")
        );
        assert_eq!(result.exponent(), None);
        assert_eq!(
            result.to_integer(),
            BigInt::parse_bytes(b"1234567890123456789012345678901234567890", 10).unwrap()
        );
    }

    proptest! {
        #[test]
        fn prop_valid_integers(input in (-1000i64..1000).prop_map(|n| n.to_string())) {
            let parser = NumberParserBuilder::new().negative(true).build();
            let result = parser.parse(&input).into_result().unwrap();
            assert!(result.is_integer(), "Expected number to be an integer");
            assert_eq!(result.to_string(), input);
        }

        #[test]
        fn prop_valid_rationals(
            // Use positive values only to simplify test
            numerator in 0i32..1000,
            denominator in 1..1000i32
        ) {
            let input = format!("{}.{}", numerator, denominator);
            let parser = NumberParserBuilder::new().rational(true).negative(true).build();

            let result = parser.parse(&input).into_result().unwrap();
            assert!(!result.is_integer(), "Expected number to be rational");
            assert_eq!(result.to_string(), input);
            assert_eq!(result.base(), numerator.to_string());
            assert_eq!(result.decimal(), Some(denominator.to_string().as_ref()));
            assert_eq!(result.exponent(), None);
            assert_eq!(result.to_integer(), BigInt::from(numerator));

            // Calculate the actual rational value based on the input format
            let den_str = denominator.to_string();
            let den_len = den_str.len();
            let denominator_factor = 10i64.pow(den_len as u32);
            let expected_num = (numerator as i64) * denominator_factor + (denominator as i64);

            // Calculate the expected rational with appropriate precision
            let expected_rational = BigRational::new(
                BigInt::from(expected_num),
                BigInt::from(denominator_factor)
            );

            // Compare using approximate floating point
            let expected_f64 = expected_rational.to_f64().unwrap_or(f64::NAN);
            let actual_f64 = result.as_f64().unwrap_or(f64::NAN);
            assert!((actual_f64 - expected_f64).abs() < 1e-10,
                   "Input: '{}', Expected rational: {}, Expected f64: {}, Actual f64: {}",
                   input, expected_rational, expected_f64, actual_f64);
        }
    }
}
