// Copyright 2025 Asim Ihsan
//
// This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
// If a copy of the MPL was not distributed with this file, You can obtain one at https://mozilla.org/MPL/2.0/.
//
// SPDX-License-Identifier: MPL-2.0

use chumsky::prelude::*;
use std::ops::Range;

#[derive(Debug, Clone, PartialEq)]
pub enum NumberValue {
    Integer(i64),
    Float(f64),
}

impl NumberValue {
    pub fn as_f64(&self) -> f64 {
        match self {
            NumberValue::Integer(i) => *i as f64,
            NumberValue::Float(f) => *f,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum Sign {
    Positive,
    Negative,
    None,
}

#[derive(Debug, Default)]
pub struct NumberParserBuilder {
    allow_negative: bool,
    allow_float: bool,
    allow_scientific: bool,
}

impl NumberParserBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn negative(mut self, allow: bool) -> Self {
        self.allow_negative = allow;
        self
    }

    pub fn float(mut self, allow: bool) -> Self {
        self.allow_float = allow;
        self
    }

    pub fn scientific(mut self, allow: bool) -> Self {
        self.allow_scientific = allow;
        self
    }

    fn sign_parser() -> impl Parser<char, Sign, Error = Simple<char>> {
        choice((just('+').to(Sign::Positive), just('-').to(Sign::Negative)))
            .or_not()
            .map(|s| s.unwrap_or(Sign::None))
    }

    pub fn build(self) -> impl Parser<char, NumberValue, Error = Simple<char>> {
        let digits = text::int(10);
        let integer = digits.map(|s: String| s.parse::<i64>().unwrap());
        let decimal = just('.').ignore_then(text::digits(10)).map(Some).or_not();
        let exponent = choice((just('e'), just('E')))
            .ignore_then(Self::sign_parser().then(text::int(10)))
            .map(Some)
            .or_not();

        let allow_negative = self.allow_negative;
        let allow_float = self.allow_float;
        let allow_scientific = self.allow_scientific;

        Self::sign_parser().then(integer).then(decimal).then(exponent).try_map(
            move |(((sign, int), dec), exp), span: Range<usize>| {
                if matches!(sign, Sign::Negative) && !allow_negative {
                    return Err(Simple::custom(span, "Negative numbers not allowed"));
                }

                let mut num_str = String::new();
                if sign == Sign::Negative {
                    num_str.push('-')
                }
                num_str.push_str(&int.to_string());

                let has_decimal = if let Some(dec_str) = dec.as_ref().and_then(|d| d.as_ref()) {
                    if !allow_float {
                        return Err(Simple::custom(span, "Float numbers not allowed"));
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
                            return Err(Simple::custom(span, "Scientific notation not allowed"));
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
                    Ok(NumberValue::Float(num_str.parse::<f64>().unwrap()))
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
        assert_eq!(parser.parse("42"), Ok(NumberValue::Integer(42)));
    }

    #[test]
    fn test_negative_integer() {
        let parser = NumberParserBuilder::new().negative(true).build();
        assert_eq!(parser.parse("-42"), Ok(NumberValue::Integer(-42)));
    }

    #[test]
    fn test_float() {
        let parser = NumberParserBuilder::new().float(true).negative(true).build();
        assert_eq!(parser.parse("42.0"), Ok(NumberValue::Float(42.0)));
    }

    #[test]
    fn test_scientific() {
        let parser = NumberParserBuilder::new().scientific(true).negative(true).build();
        assert_eq!(parser.parse("42e0").map(|n| n.as_f64()), Ok(42.0));
    }

    #[test]
    fn test_disallowed_negative() {
        let parser = NumberParserBuilder::new().negative(false).build();
        assert!(parser.parse("-42").is_err());
    }

    #[test]
    fn test_disallowed_float() {
        let parser = NumberParserBuilder::new().float(false).build();
        assert!(parser.parse("42.0").is_err());
    }

    #[test]
    fn test_disallowed_scientific() {
        let parser = NumberParserBuilder::new().scientific(false).build();
        assert!(parser.parse("42e0").is_err());
    }

    #[test]
    fn test_float_with_no_decimal() {
        let parser = NumberParserBuilder::new().float(true).negative(true).build();
        assert_eq!(parser.parse("42.").map(|n| n.as_f64()), Ok(42.0));
    }

    #[test]
    fn test_scientific_with_positive_exp() {
        let parser = NumberParserBuilder::new().scientific(true).build();
        assert_eq!(parser.parse("42e+2").map(|n| n.as_f64()), Ok(4200.0));
    }

    #[test]
    fn test_combined_float_scientific() {
        let parser = NumberParserBuilder::new().float(true).scientific(true).negative(true).build();
        assert_eq!(parser.parse("-42.5e-1").map(|n| n.as_f64()), Ok(-4.25));
    }

    #[test]
    fn test_exponent_variations() {
        let parser = NumberParserBuilder::new().scientific(true).build();
        assert_eq!(parser.parse("1e0").map(|n| n.as_f64()), Ok(1.0));
        assert_eq!(parser.parse("1e1").map(|n| n.as_f64()), Ok(10.0));
        assert_eq!(parser.parse("1e+1").map(|n| n.as_f64()), Ok(10.0));
        assert_eq!(parser.parse("1e-1").map(|n| n.as_f64()), Ok(0.1));
        assert_eq!(parser.parse("10e2").map(|n| n.as_f64()), Ok(1000.0));
    }

    #[test]
    fn test_explicit_positive_variations() {
        let parser = NumberParserBuilder::new().scientific(true).negative(true).float(true).build();
        assert_eq!(parser.parse("+1").map(|n| n.as_f64()), Ok(1.0));
        assert_eq!(parser.parse("+1e1").map(|n| n.as_f64()), Ok(10.0));
        assert_eq!(parser.parse("+1e+1").map(|n| n.as_f64()), Ok(10.0));
        assert_eq!(parser.parse("+1.5e+1").map(|n| n.as_f64()), Ok(15.0));
    }

    proptest! {
        #[test]
        fn prop_valid_integers(n in -1000i64..1000) {
            let parser = NumberParserBuilder::new().negative(true).build();
            let input = n.to_string();
            prop_assert_eq!(parser.parse(&*input), Ok(NumberValue::Integer(n)));
        }

        #[test]
        fn prop_valid_floats(n in -1000.0f64..1000.0) {
            let parser = NumberParserBuilder::new().float(true).negative(true).build();
            let input = format!("{}", n);
            let parsed = parser.parse(&*input).unwrap().as_f64();
            let rel_error = if n != 0.0 { (parsed - n).abs() / n.abs() } else { (parsed - n).abs() };
            prop_assert!(rel_error < 1e-10, "Parsed: {}, Expected: {}, Relative Error: {}", parsed, n, rel_error);
        }

        #[test]
        fn prop_scientific_notation(base in -100i64..100, exp in -5i32..5) {
            let parser = NumberParserBuilder::new().scientific(true).negative(true).build();
            let input = format!("{}e{}", base, exp);
            let expected = (base as f64) * 10f64.powi(exp);
            let parsed = parser.parse(&*input).unwrap().as_f64();
            prop_assert!((parsed - expected).abs() < 0.000001);
        }
    }
}
