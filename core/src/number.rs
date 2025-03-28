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
//!
//! let parser = NumberParserBuilder::new()
//!     .negative(true)
//!     .build();
//!
//! assert_eq!(
//!     parser.parse("42").into_result(),
//!     Ok(NumberValue::Integer(42))
//! );
//! ```
//!
//! Parsing floating point numbers with component preservation:
//!
//! ```
//! use chumsky_helpers::number::{NumberParserBuilder, NumberValue, Sign};
//! use chumsky::prelude::*;
//!
//! let parser = NumberParserBuilder::new()
//!     .negative(true)
//!     .float(true)
//!     .scientific(true)
//!     .build();
//!
//! let result = parser.parse("-123.456e+7").into_result().unwrap();
//! match result {
//!     NumberValue::Float { value, base, decimal, exponent } => {
//!         assert_eq!(value, -123.456e+7);
//!         assert_eq!(base, "123");
//!         assert_eq!(decimal, Some("456".to_string()));
//!         assert_eq!(exponent, Some((Sign::Positive, "7".to_string())));
//!     },
//!     _ => panic!("Expected Float variant"),
//! }
//! ```

use chumsky::{error::Rich, prelude::*};

/// Represents a parsed numeric value, either as an integer or a floating point number.
///
/// The `Float` variant preserves the original components of the parsed number,
/// allowing for high-precision arithmetic operations that might be lost in floating-point
/// representation.
#[derive(Debug, Clone, PartialEq)]
pub enum NumberValue {
    /// An integer value.
    Integer(i64),
    
    /// A floating point value with preserved components.
    Float { 
        /// The calculated floating point value.
        value: f64, 
        
        /// The base component (digits before the decimal point).
        base: String, 
        
        /// The decimal component (digits after the decimal point), if any.
        decimal: Option<String>, 
        
        /// The exponent component with sign, if any.
        exponent: Option<(Sign, String)> 
    },
}

impl NumberValue {
    /// Converts the number value to an f64, regardless of whether it's an integer or float.
    pub fn as_f64(&self) -> f64 {
        match self {
            NumberValue::Integer(i) => *i as f64,
            NumberValue::Float { value, .. } => *value,
        }
    }

    /// Returns the base component of the number (digits before the decimal point).
    /// For integers, returns an empty string.
    pub fn base(&self) -> &str {
        match self {
            NumberValue::Integer(_) => "", // Integer doesn't have separate base
            NumberValue::Float { base, .. } => base,
        }
    }

    /// Returns the decimal component of the number (digits after the decimal point), if any.
    /// For integers, returns `None`.
    pub fn decimal(&self) -> Option<&str> {
        match self {
            NumberValue::Integer(_) => None,
            NumberValue::Float { decimal, .. } => decimal.as_deref(),
        }
    }

    /// Returns the exponent component of the number with its sign, if any.
    /// For integers, returns `None`.
    pub fn exponent(&self) -> Option<(Sign, &str)> {
        match self {
            NumberValue::Integer(_) => None,
            NumberValue::Float { exponent, .. } => {
                exponent.as_ref().map(|(sign, exp)| (*sign, exp.as_str()))
            }
        }
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

/// Builder for configuring and creating a number parser.
///
/// This builder allows you to customize which numeric formats are allowed
/// in the parser, such as negative numbers, floating point numbers, and
/// scientific notation.
#[derive(Debug, Default)]
pub struct NumberParserBuilder {
    allow_negative: bool,
    allow_float: bool,
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

    /// Configure whether floating point numbers are allowed.
    pub fn float(mut self, allow: bool) -> Self {
        self.allow_float = allow;
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
    /// parse numeric literals into the `NumberValue` type.
    pub fn build<'a>(self) -> impl Parser<'a, &'a str, NumberValue, extra::Err<Rich<'a, char>>> {
        let digits = text::int(10);
        let integer = digits.map(|s: &str| s.parse::<i64>().unwrap());
        let decimal = just('.')
            .ignore_then(text::digits(10).to_slice().or_not().map(|opt| opt.unwrap_or("")))
            .map(Some)
            .or_not();
        let exponent = choice((just('e'), just('E')))
            .ignore_then(Self::sign_parser().then(text::int(10)))
            .map(Some)
            .or_not();

        let allow_negative = self.allow_negative;
        let allow_float = self.allow_float;
        let allow_scientific = self.allow_scientific;

        Self::sign_parser().then(integer).then(decimal).then(exponent).try_map(
            move |(((sign, int), dec), exp), span| {
                if matches!(sign, Sign::Negative) && !allow_negative {
                    return Err(Rich::<char, _>::custom(
                        span,
                        "Negative numbers not allowed",
                    ));
                }

                let mut num_str = String::new();
                if sign == Sign::Negative {
                    num_str.push('-')
                }
                num_str.push_str(&int.to_string());

                let has_decimal = if let Some(dec_str) = dec.as_ref().and_then(|d| d.as_ref()) {
                    if !allow_float {
                        return Err(Rich::<char, _>::custom(span, "Float numbers not allowed"));
                    }
                    num_str.push('.');
                    num_str.push_str(dec_str);
                    true
                } else {
                    false
                };

                let has_exponent =
                    if let Some((exp_sign, exp_str)) = exp.as_ref().and_then(|e| e.as_ref()) {
                        if !allow_scientific {
                            return Err(Rich::<char, _>::custom(
                                span,
                                "Scientific notation not allowed",
                            ));
                        }
                        num_str.push('e');
                        match exp_sign {
                            Sign::Negative => num_str.push('-'),
                            Sign::Positive => num_str.push('+'),
                            _ => (),
                        }
                        num_str.push_str(exp_str);
                        true
                    } else {
                        false
                    };

                if !has_decimal && !has_exponent {
                    Ok(NumberValue::Integer(if matches!(sign, Sign::Negative) {
                        -int
                    } else {
                        int
                    }))
                } else {
                    let base_str = int.to_string();
                    let decimal_str = dec.as_ref().and_then(|d| d.as_ref()).map(|s| s.to_string());
                    let exponent_data = exp
                        .as_ref()
                        .and_then(|e| e.as_ref())
                        .map(|(exp_sign, exp_str)| (*exp_sign, exp_str.to_string()));

                    Ok(NumberValue::Float {
                        value: num_str.parse::<f64>().unwrap(),
                        base: base_str,
                        decimal: decimal_str,
                        exponent: exponent_data,
                    })
                }
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn test_basic_integer() {
        let parser = NumberParserBuilder::new().negative(true).build();
        assert_eq!(
            parser.parse("42").into_result(),
            Ok(NumberValue::Integer(42))
        );
    }

    #[test]
    fn test_negative_integer() {
        let parser = NumberParserBuilder::new().negative(true).build();
        assert_eq!(
            parser.parse("-42").into_result(),
            Ok(NumberValue::Integer(-42))
        );
    }

    #[test]
    fn test_float() {
        let parser = NumberParserBuilder::new().float(true).negative(true).build();
        let result = parser.parse("42.0").into_result().unwrap();
        match result {
            NumberValue::Float { value, base, decimal, exponent } => {
                assert_eq!(value, 42.0);
                assert_eq!(base, "42");
                assert_eq!(decimal, Some("0".to_string()));
                assert_eq!(exponent, None);
            }
            _ => panic!("Expected Float variant"),
        }
    }

    #[test]
    fn test_scientific() {
        let parser = NumberParserBuilder::new().scientific(true).negative(true).build();
        let result = parser.parse("42e0").into_result().unwrap();
        match result {
            NumberValue::Float { value, base, decimal, exponent } => {
                assert_eq!(value, 42.0);
                assert_eq!(base, "42");
                assert_eq!(decimal, None);
                assert_eq!(exponent, Some((Sign::None, "0".to_string())));
            }
            _ => panic!("Expected Float variant"),
        }
    }

    #[test]
    fn test_disallowed_negative() {
        let parser = NumberParserBuilder::new().negative(false).build();
        assert!(parser.parse("-42").has_errors());
    }

    #[test]
    fn test_disallowed_float() {
        let parser = NumberParserBuilder::new().float(false).build();
        assert!(parser.parse("42.0").has_errors());
    }

    #[test]
    fn test_disallowed_scientific() {
        let parser = NumberParserBuilder::new().scientific(false).build();
        assert!(parser.parse("42e0").has_errors());
    }

    #[test]
    fn test_float_with_no_decimal() {
        let parser = NumberParserBuilder::new().float(true).negative(true).build();
        let result = parser.parse("42.").into_result().unwrap();
        match result {
            NumberValue::Float { value, base, decimal, exponent } => {
                assert_eq!(value, 42.0);
                assert_eq!(base, "42");
                assert_eq!(decimal, Some("".to_string()));
                assert_eq!(exponent, None);
            }
            _ => panic!("Expected Float variant"),
        }
    }

    #[test]
    fn test_scientific_with_positive_exp() {
        let parser = NumberParserBuilder::new().scientific(true).build();
        let result = parser.parse("42e+2").into_result().unwrap();
        match result {
            NumberValue::Float { value, base, decimal, exponent } => {
                assert_eq!(value, 4200.0);
                assert_eq!(base, "42");
                assert_eq!(decimal, None);
                assert_eq!(exponent, Some((Sign::Positive, "2".to_string())));
            }
            _ => panic!("Expected Float variant"),
        }
    }

    #[test]
    fn test_combined_float_scientific() {
        let parser = NumberParserBuilder::new().float(true).scientific(true).negative(true).build();
        let result = parser.parse("-42.5e-1").into_result().unwrap();
        match result {
            NumberValue::Float { value, base, decimal, exponent } => {
                assert_eq!(value, -4.25);
                assert_eq!(base, "42");
                assert_eq!(decimal, Some("5".to_string()));
                assert_eq!(exponent, Some((Sign::Negative, "1".to_string())));
            }
            _ => panic!("Expected Float variant"),
        }
    }

    #[test]
    fn test_exponent_variations() {
        let parser = NumberParserBuilder::new().scientific(true).build();

        // Just check values with as_f64() for brevity in these variations
        assert_eq!(
            parser.parse("1e0").into_result().map(|n| n.as_f64()),
            Ok(1.0)
        );
        assert_eq!(
            parser.parse("1e1").into_result().map(|n| n.as_f64()),
            Ok(10.0)
        );
        assert_eq!(
            parser.parse("1e+1").into_result().map(|n| n.as_f64()),
            Ok(10.0)
        );
        assert_eq!(
            parser.parse("1e-1").into_result().map(|n| n.as_f64()),
            Ok(0.1)
        );
        assert_eq!(
            parser.parse("10e2").into_result().map(|n| n.as_f64()),
            Ok(1000.0)
        );
    }

    #[test]
    fn test_explicit_positive_variations() {
        let parser = NumberParserBuilder::new().scientific(true).negative(true).float(true).build();

        // Check components for one case
        let result = parser.parse("+1.5e+1").into_result().unwrap();
        match result {
            NumberValue::Float { value, base, decimal, exponent } => {
                assert_eq!(value, 15.0);
                assert_eq!(base, "1");
                assert_eq!(decimal, Some("5".to_string()));
                assert_eq!(exponent, Some((Sign::Positive, "1".to_string())));
            }
            _ => panic!("Expected Float variant"),
        }

        // Just check values with as_f64() for the rest
        assert_eq!(
            parser.parse("+1").into_result().map(|n| n.as_f64()),
            Ok(1.0)
        );
        assert_eq!(
            parser.parse("+1e1").into_result().map(|n| n.as_f64()),
            Ok(10.0)
        );
        assert_eq!(
            parser.parse("+1e+1").into_result().map(|n| n.as_f64()),
            Ok(10.0)
        );
    }

    #[test]
    fn test_component_preservation() {
        let parser = NumberParserBuilder::new().float(true).scientific(true).negative(true).build();

        // Test with a complex number with all components
        let test_cases = [
            (
                "123.456e-7",
                "123",
                Some("456".to_string()),
                Some((Sign::Negative, "7".to_string())),
                123.456e-7,
            ),
            (
                "-987.654E+3",
                "987",
                Some("654".to_string()),
                Some((Sign::Positive, "3".to_string())),
                -987.654e3,
            ),
            ("42.", "42", Some("".to_string()), None, 42.0),
            ("0.123", "0", Some("123".to_string()), None, 0.123),
        ];

        for (input, expected_base, expected_decimal, expected_exponent, expected_value) in
            test_cases
        {
            let result = parser.parse(input).into_result().unwrap();
            match result {
                NumberValue::Float { value, base, decimal, exponent } => {
                    assert!(
                        (value - expected_value).abs() < 1e-10,
                        "For input {}, expected value {} but got {}",
                        input,
                        expected_value,
                        value
                    );
                    assert_eq!(
                        base, expected_base,
                        "For input {}, expected base {} but got {}",
                        input, expected_base, base
                    );
                    assert_eq!(
                        decimal, expected_decimal,
                        "For input {}, expected decimal {:?} but got {:?}",
                        input, expected_decimal, decimal
                    );
                    assert_eq!(
                        exponent, expected_exponent,
                        "For input {}, expected exponent {:?} but got {:?}",
                        input, expected_exponent, exponent
                    );
                }
                _ => panic!("Expected Float variant for input {}", input),
            }
        }
    }

    proptest! {
        #[test]
        fn prop_valid_integers(input in (-1000i64..1000).prop_map(|n| n.to_string())) {
            let parser = NumberParserBuilder::new().negative(true).build();
            let expected = input.parse::<i64>().unwrap();
            let result = parser.parse(&input).into_result().unwrap();
            prop_assert_eq!(result, NumberValue::Integer(expected));
        }

        #[test]
        fn prop_valid_floats(input in (-1000.0f64..1000.0).prop_map(|n| n.to_string())) {
            let parser = NumberParserBuilder::new().float(true).negative(true).build();
            let expected = input.parse::<f64>().unwrap();
            let parsed = parser.parse(&input).into_result().unwrap().as_f64();
            let rel_error = if expected != 0.0 { (parsed - expected).abs() / expected.abs() } else { (parsed - expected).abs() };

            // Also verify components are correctly stored
            match parser.parse(&input).into_result().unwrap() {
                NumberValue::Float { value, .. } => {
                    // Just check the value is approximately correct
                    let value_error = if expected != 0.0 { (value - expected).abs() / expected.abs() } else { (value - expected).abs() };
                    prop_assert!(value_error < 1e-10);
                },
                _ => prop_assert!(false, "Expected Float variant"),
            }

            prop_assert!(rel_error < 1e-10, "Parsed: {}, Expected: {}, Relative Error: {}", parsed, expected, rel_error);
        }

        // #[test]
        // fn prop_scientific_notation(
        //     base in (-100i64..100).prop_map(|n| n.to_string()),
        //     exp in (-5i32..5).prop_map(|n| n.to_string()))
        // {
        //     let parser = NumberParserBuilder::new().scientific(true).negative(true).build();
        //     let input = format!("{}e{}", base, exp);
        //     let expected = base.parse::<i64>().unwrap() as f64 * 10f64.powi(exp.parse::<i32>().unwrap());
        //     let parsed = parser.parse(&input).into_result().unwrap().as_f64();
        //     prop_assert!((parsed - expected).abs() < 0.000001);
        // }
    }
}