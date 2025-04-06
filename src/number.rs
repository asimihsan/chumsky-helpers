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
//! assert_eq!(
//!     parser.parse("42").into_result(),
//!     Ok(NumberValue::Integer(BigInt::from(42)))
//! );
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
//! match result {
//!     NumberValue::Rational { value, base, decimal, exponent } => {
//!         // -123.456e+7 = -1234560000
//!         let expected_value = BigRational::from_str("-1234560000").unwrap();
//!         assert_eq!(value, expected_value);
//!         assert_eq!(base, "123");
//!         assert_eq!(decimal, Some("456".to_string()));
//!         assert_eq!(exponent, Some((Sign::Positive, "7".to_string())));
//!     },
//!     _ => panic!("Expected Rational variant"),
//! }
//! ```

use chumsky::{error::Rich, prelude::*};
use num::One;
use num_bigint::BigInt;
use num_rational::BigRational;
use std::str::FromStr;

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
    /// An integer with its string representation.
    Integer(String),

    /// A decimal number with preserved components.
    Decimal {
        /// The base component (digits before the decimal point).
        base: String,

        /// The decimal component (digits after the decimal point).
        decimal: Option<String>,

        /// The exponent component, if any.
        exponent: Option<Exponent>,
    },

    /// A computed value with no original formatting.
    /// This is used for results of operations that don't have a specific
    /// display format from the source.
    Computed,
}

impl std::fmt::Display for NumberValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.format {
            NumberFormat::Integer(s) => {
                write!(f, "{}", s)
            }
            NumberFormat::Decimal { base, decimal, exponent } => {
                // Write the base part
                write!(f, "{}", base)?;

                // Write decimal part if it exists
                if let Some(dec) = decimal {
                    write!(f, ".{}", dec)?;
                }

                // Write exponent part if it exists
                if let Some(exp) = exponent {
                    // Write the exponent marker with correct case
                    write!(f, "{}", exp.case)?;

                    // Write the sign if any
                    match exp.sign {
                        Sign::Positive => write!(f, "+")?,
                        Sign::Negative => write!(f, "-")?,
                        Sign::None => {}
                    }

                    // Write the exponent value
                    write!(f, "{}", exp.value)?;
                }

                Ok(())
            }
            NumberFormat::Computed => {
                // For computed values, use the mathematical format (n/d)
                if self.value.denom() == &BigInt::one() {
                    write!(f, "{}", self.value.numer())
                } else {
                    write!(f, "{}", self.value)
                }
            }
        }
    }
}

impl NumberValue {
    /// Creates a new integer value.
    pub fn new_integer<T: Into<BigInt>>(value: T) -> Self {
        let int_value = value.into();
        let str_value = int_value.to_string();
        NumberValue {
            value: BigRational::from_integer(int_value),
            format: NumberFormat::Integer(str_value),
        }
    }

    /// Creates a new rational value from components.
    pub fn new_rational(
        value: BigRational,
        base: String,
        decimal: Option<String>,
        exponent: Option<Exponent>,
    ) -> Self {
        NumberValue { value, format: NumberFormat::Decimal { base, decimal, exponent } }
    }

    /// Creates a computed value from an operation result.
    pub fn new_computed(value: BigRational) -> Self {
        // Normalize to Integer format if result is an integer
        if value.denom() == &BigInt::one() {
            NumberValue {
                value: value.clone(),
                format: NumberFormat::Integer(value.numer().to_string()),
            }
        } else {
            NumberValue { value, format: NumberFormat::Computed }
        }
    }

    /// Checks if the value was parsed as an integer.
    pub fn is_integer(&self) -> bool {
        matches!(self.format, NumberFormat::Integer(_))
    }

    /// Checks if the value was parsed as a rational.
    pub fn is_rational(&self) -> bool {
        matches!(
            self.format,
            NumberFormat::Decimal { .. } | NumberFormat::Computed
        )
    }

    /// Converts the number to an f64 value.
    ///
    /// Note that this may lose precision for very large numbers or
    /// numbers with many decimal places.
    pub fn as_f64(&self) -> f64 {
        let num = self.value.numer().to_string().parse::<f64>().unwrap_or(0.0);
        let denom = self.value.denom().to_string().parse::<f64>().unwrap_or(1.0);
        num / denom
    }

    /// Returns the base component of the number (digits before the decimal point).
    pub fn base(&self) -> &str {
        match &self.format {
            NumberFormat::Integer(s) => s,
            NumberFormat::Decimal { base, .. } => base,
            NumberFormat::Computed => "",
        }
    }

    /// Returns the decimal component of the number (digits after the decimal point), if any.
    pub fn decimal(&self) -> Option<&str> {
        match &self.format {
            NumberFormat::Integer(_) => None,
            NumberFormat::Decimal { decimal, .. } => decimal.as_deref(),
            NumberFormat::Computed => None,
        }
    }

    /// Returns the exponent component of the number, if any.
    pub fn exponent(&self) -> Option<&Exponent> {
        match &self.format {
            NumberFormat::Integer(_) => None,
            NumberFormat::Decimal { exponent, .. } => exponent.as_ref(),
            NumberFormat::Computed => None,
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

    /// Parses a string into a NumberValue.
    ///
    /// This function can handle integers, decimal numbers, and scientific notation.
    /// It returns None if parsing fails.
    ///
    /// Note: This method doesn't implement FromStr trait to avoid confusion with the standard
    /// trait method. Use this method directly instead.
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(s: &str) -> Option<Self> {
        // First try to parse as a simple integer
        if let Ok(i) = BigInt::from_str(s) {
            return Some(NumberValue::new_integer(i));
        }

        // Parse as a rational number (may include decimal point and/or scientific notation)
        let mut parts = s.split(&['e', 'E'][..]);
        let base_part = parts.next()?;
        let exp_part = parts.next();

        let (sign, mantissa) = if let Some(stripped) = base_part.strip_prefix('-') {
            (Sign::Negative, stripped)
        } else if let Some(stripped) = base_part.strip_prefix('+') {
            (Sign::Positive, stripped)
        } else {
            (Sign::None, base_part)
        };

        let mantissa_parts: Vec<&str> = mantissa.split('.').collect();
        let base = mantissa_parts.first()?.to_string();
        let decimal = mantissa_parts.get(1).map(|s| s.to_string());

        // Parse exponent if present
        let exponent = if let Some(exp) = exp_part {
            // Determine the exponent marker case ('e' or 'E') from the original string
            let exp_case = if s.contains('E') { 'E' } else { 'e' };

            let (exp_sign, exp_val) = if let Some(stripped) = exp.strip_prefix('-') {
                (Sign::Negative, stripped.to_string())
            } else if let Some(stripped) = exp.strip_prefix('+') {
                (Sign::Positive, stripped.to_string())
            } else {
                (Sign::None, exp.to_string())
            };

            Some(Exponent { sign: exp_sign, value: exp_val, case: exp_case })
        } else {
            None
        };

        // Construct the rational value
        let sign_for_display = sign; // Save sign for display purposes
        let mut rational_str = if sign == Sign::Negative { "-" } else { "" }.to_string();
        rational_str.push_str(&base);

        if let Some(dec) = &decimal {
            if !dec.is_empty() {
                let numerator = format!("{}{}", base, dec);
                let denominator = format!("1{}", "0".repeat(dec.len()));

                let num = BigInt::from_str(&numerator).ok()?;
                let denom = BigInt::from_str(&denominator).ok()?;
                let mut value = BigRational::new(num, denom);

                if sign == Sign::Negative {
                    value = -value;
                }

                // Apply exponent if present
                if let Some(exp) = &exponent {
                    if let Ok(exp_num) = u32::from_str(&exp.value) {
                        let factor = BigInt::from(10).pow(exp_num);
                        match exp.sign {
                            Sign::Negative => value /= BigRational::from_integer(factor),
                            _ => value *= BigRational::from_integer(factor),
                        }
                    }
                }

                return Some(NumberValue::new_rational(
                    value,
                    if sign_for_display == Sign::Positive {
                        format!("+{}", base)
                    } else if sign_for_display == Sign::Negative {
                        // Use original base without sign for internal format
                        // The negative sign is already in the value
                        base.clone()
                    } else {
                        base.clone()
                    },
                    decimal.clone(),
                    exponent,
                ));
            }
        }

        // No decimal part, but might have exponent
        let mut value = BigRational::from_integer(BigInt::from_str(&rational_str).ok()?);

        // Apply exponent if present
        if let Some(exp) = &exponent {
            // Parse the exponent value, ignoring any e/E marker
            if let Ok(exp_num) = u32::from_str(&exp.value) {
                let factor = BigInt::from(10).pow(exp_num);
                match exp.sign {
                    Sign::Negative => value /= BigRational::from_integer(factor),
                    _ => value *= BigRational::from_integer(factor),
                }
            }
        }

        Some(NumberValue::new_rational(
            value,
            if sign_for_display == Sign::Positive {
                format!("+{}", base)
            } else {
                base.clone()
            },
            decimal,
            exponent,
        ))
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

    /// The sign of the exponent (+, -, or none)
    pub sign: Sign,

    /// The numeric value of the exponent as a string
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
        let digits = text::int(10);
        let decimal = just('.')
            .ignore_then(text::digits(10).to_slice().or_not().map(|opt| opt.unwrap_or("")))
            .map(Some)
            .or_not();
        let exponent = choice((just('e').to('e'), just('E').to('E')))
            .then(Self::sign_parser())
            .then(text::int(10).to_slice())
            .map(|((case, sign), value)| Some(Exponent { case, sign, value: value.to_string() }))
            .or_not();

        let allow_negative = self.allow_negative;
        let allow_rational = self.allow_rational;
        let allow_scientific = self.allow_scientific;

        Self::sign_parser().then(digits.to_slice()).then(decimal).then(exponent).try_map(
            move |(((sign, int_str), dec), exp), span| {
                if matches!(sign, Sign::Negative) && !allow_negative {
                    return Err(Rich::<char, _>::custom(
                        span,
                        "Negative numbers not allowed",
                    ));
                }

                // Start building the full number string
                let mut num_str = String::new();
                if sign == Sign::Negative {
                    num_str.push('-');
                } else if sign == Sign::Positive {
                    num_str.push('+');
                }
                num_str.push_str(int_str);

                // Check for decimal part
                let has_decimal = if let Some(Some(dec_str)) = dec {
                    if !allow_rational {
                        return Err(Rich::<char, _>::custom(
                            span,
                            "Rational numbers not allowed",
                        ));
                    }
                    num_str.push('.');
                    num_str.push_str(dec_str);
                    true
                } else {
                    false
                };

                // Check for exponent part
                let has_exponent = if let Some(Some(exp)) = exp {
                    if !allow_scientific {
                        return Err(Rich::<char, _>::custom(
                            span,
                            "Scientific notation not allowed",
                        ));
                    }
                    num_str.push(exp.case);
                    match exp.sign {
                        Sign::Negative => num_str.push('-'),
                        Sign::Positive => num_str.push('+'),
                        _ => (),
                    }
                    num_str.push_str(&exp.value);
                    true
                } else {
                    false
                };

                // If it's a simple integer (no decimal, no exponent), use the Integer format
                if !has_decimal && !has_exponent {
                    let sign_prefix = if sign == Sign::Negative { "-" } else { "" };
                    let full_int_str = format!("{}{}", sign_prefix, int_str);
                    match BigInt::from_str(&full_int_str) {
                        Ok(value) => Ok(NumberValue::new_integer(value)),
                        Err(_) => Err(Rich::<char, _>::custom(span, "Failed to parse integer")),
                    }
                } else {
                    // For more complex numbers, use the from_str method we implemented
                    match NumberValue::from_str(&num_str) {
                        Some(value) => Ok(value),
                        None => Err(Rich::<char, _>::custom(span, "Failed to parse number")),
                    }
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

    #[test]
    fn test_display_implementation() {
        // Test integer display
        let int_val = NumberValue::new_integer(42);
        assert_eq!(int_val.to_string(), "42");

        // Test rational display with original components
        let rational_with_components = NumberValue::new_rational(
            BigRational::new(BigInt::from(1234), BigInt::from(10)),
            "123".to_string(),
            Some("4".to_string()),
            None,
        );
        assert_eq!(rational_with_components.to_string(), "123.4");

        // Test with exponent
        let rational_with_exponent = NumberValue::new_rational(
            BigRational::new(BigInt::from(1234560000), BigInt::from(1)),
            "123".to_string(),
            Some("456".to_string()),
            Some(Exponent { sign: Sign::Positive, value: "7".to_string(), case: 'e' }),
        );
        assert_eq!(rational_with_exponent.to_string(), "123.456e+7");

        // Test negative exponent
        let rational_with_neg_exponent = NumberValue::new_rational(
            BigRational::new(BigInt::from(1234), BigInt::from(100000)),
            "123".to_string(),
            Some("4".to_string()),
            Some(Exponent { sign: Sign::Negative, value: "5".to_string(), case: 'e' }),
        );
        assert_eq!(rational_with_neg_exponent.to_string(), "123.4e-5");

        // Test with operation result (no original components)
        let operation_result =
            NumberValue::new_computed(BigRational::new(BigInt::from(22), BigInt::from(7)));
        assert_eq!(operation_result.to_string(), "22/7");
    }

    #[test]
    fn test_basic_integer() {
        let parser = NumberParserBuilder::new().negative(true).build();
        assert_eq!(
            parser.parse("42").into_result(),
            Ok(NumberValue::new_integer(42))
        );
    }

    #[test]
    fn test_negative_integer() {
        let parser = NumberParserBuilder::new().negative(true).build();
        assert_eq!(
            parser.parse("-42").into_result(),
            Ok(NumberValue::new_integer(-42))
        );
    }

    #[test]
    fn test_positive_integer() {
        let parser = NumberParserBuilder::new().negative(true).build();
        assert_eq!(
            parser.parse("+42").into_result(),
            Ok(NumberValue::new_integer(-42))
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
        assert_eq!(result.as_f64(), 42.0);
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
        assert_eq!(result.as_f64(), -42.0);
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
            Some(&Exponent { sign: Sign::None, value: "0".to_string(), case: 'e' })
        );
        assert_eq!(result.to_integer(), BigInt::from(42));
        assert_eq!(
            result.to_rational(),
            Ratio::new(BigInt::from(42), BigInt::from(1))
        );
        assert_eq!(result.as_f64(), 42.0);
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
        assert_eq!(result.as_f64(), 42.0);
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
            Some(&Exponent { sign: Sign::Positive, value: "2".to_string(), case: 'e' })
        );
        assert_eq!(result.to_integer(), BigInt::from(4200));
        assert_eq!(
            result.to_rational(),
            Ratio::new(BigInt::from(4200), BigInt::from(1))
        );
        assert_eq!(result.as_f64(), 4200.0);
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
            Some(&Exponent { sign: Sign::Negative, value: "1".to_string(), case: 'e' })
        );
        assert_eq!(result.to_integer(), BigInt::from(-4));
        assert_eq!(
            result.to_rational(),
            Ratio::new(BigInt::from(-425), BigInt::from(100))
        );
        assert_eq!(result.as_f64(), -4.25);
        assert_eq!(
            result.as_rational(),
            &Ratio::new(BigInt::from(-425), BigInt::from(100))
        );
    }

    #[test]
    fn test_exponent_variations() {
        let parser = NumberParserBuilder::new().scientific(true).build();

        // Check values with as_f64() for brevity in these variations
        assert!((parser.parse("1e0").into_result().unwrap().as_f64() - 1.0).abs() < 1e-10);
        assert!((parser.parse("1e1").into_result().unwrap().as_f64() - 10.0).abs() < 1e-10);
        assert!((parser.parse("1e+1").into_result().unwrap().as_f64() - 10.0).abs() < 1e-10);
        assert!((parser.parse("1e-1").into_result().unwrap().as_f64() - 0.1).abs() < 1e-10);
        assert!((parser.parse("10e2").into_result().unwrap().as_f64() - 1000.0).abs() < 1e-10);
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
            Some(&Exponent { sign: Sign::Positive, value: "1".to_string(), case: 'e' })
        );
        assert_eq!(result.to_integer(), BigInt::from(15));
        assert_eq!(
            result.to_rational(),
            Ratio::new(BigInt::from(15), BigInt::from(1))
        );
        assert_eq!(result.as_f64(), 15.0);
        assert_eq!(
            result.as_rational(),
            &Ratio::new(BigInt::from(15), BigInt::from(1))
        );

        // Just check values with as_f64() for the rest
        let pos1 = parser.parse("+1").into_result().unwrap();
        assert_eq!(pos1.to_string(), "+1");
        assert!((pos1.as_f64() - 1.0).abs() < 1e-10);

        let pos1e1 = parser.parse("+1e1").into_result().unwrap();
        assert_eq!(pos1e1.to_string(), "+1e1");
        assert!((pos1e1.as_f64() - 10.0).abs() < 1e-10);

        let pos1e_pos1 = parser.parse("+1e+1").into_result().unwrap();
        assert_eq!(pos1e_pos1.to_string(), "+1e+1");
        assert!((pos1e_pos1.as_f64() - 10.0).abs() < 1e-10);
    }

    #[test]
    fn test_component_preservation() {
        let parser =
            NumberParserBuilder::new().rational(true).scientific(true).negative(true).build();

        // Create exponent values outside the array to avoid temporary value drops
        let exp_neg = Exponent { sign: Sign::Negative, value: "7".to_string(), case: 'e' };
        let exp_pos = Exponent { sign: Sign::Positive, value: "3".to_string(), case: 'E' };

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
            assert_eq!(result.to_integer(), BigInt::from(expected_value as i64));

            // Just check that we're close to the expected value using as_f64()
            assert!(
                (result.as_f64() - expected_value).abs() < 1e-10,
                "Expected value close to {}, got {}",
                expected_value,
                result.as_f64()
            );

            // Since we're using arbitrary precision, we can't easily construct the exact expected ratio
            // So we'll compare string representations of f64 values instead
            let expected_f64 = expected_value;
            let actual_f64 = result.as_f64();
            assert!(
                (actual_f64 - expected_f64).abs() < 1e-10,
                "Expected f64 value close to {}, got {}",
                expected_f64,
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

            // Compare using approximate floating point to avoid precision issues
            let expected_f64 = expected_rational.to_f64().unwrap_or(0.0);
            let actual_f64 = result.as_f64();
            assert!((actual_f64 - expected_f64).abs() < 1e-10,
                   "Expected value around {}, got {}", expected_f64, actual_f64);
        }
    }
}
