// Copyright 2025 Asim Ihsan
//
// This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
// If a copy of the MPL was not distributed with this file, You can obtain one at https://mozilla.org/MPL/2.0/.
//
// SPDX-License-Identifier: MPL-2.0

use crate::expr::{Error, Expr};
use crate::number::{ExplicitSign, NumberValue};
use num::{One, Signed, ToPrimitive, Zero};
use num_bigint::BigInt;
use num_rational::BigRational;
use std::ops::{Add, Div, Mul, Neg, Sub};

/// Extension trait that adds evaluation capabilities to expressions
pub trait Evaluate {
    /// Evaluates the expression to a numeric value with arbitrary precision.
    fn evaluate(&self) -> Result<NumberValue, Error>;
}

impl Evaluate for Expr {
    /// Evaluates the expression to a numeric value with arbitrary precision.
    ///
    /// This method recursively evaluates the expression tree, performing the arithmetic
    /// operations with arbitrary precision using the BigInt and BigRational types.
    fn evaluate(&self) -> Result<NumberValue, Error> {
        match self {
            Expr::Number(num) => Ok(num.clone()),

            Expr::Add(left, right) => {
                let left_val = left.evaluate()?;
                let right_val = right.evaluate()?;

                // We can directly access the rational values
                let result = left_val.as_rational().add(right_val.as_rational());

                // Create a computed value that will automatically handle integer normalization
                Ok(NumberValue::new_computed(result))
            }

            Expr::Sub(left, right) => {
                let left_val = left.evaluate()?;
                let right_val = right.evaluate()?;

                let result = left_val.as_rational().sub(right_val.as_rational());

                Ok(NumberValue::new_computed(result))
            }

            Expr::Mul(left, right) => {
                let left_val = left.evaluate()?;
                let right_val = right.evaluate()?;

                let result = left_val.as_rational().mul(right_val.as_rational());

                Ok(NumberValue::new_computed(result))
            }

            Expr::Div(left, right) => {
                let left_val = left.evaluate()?;
                let right_val = right.evaluate()?;

                // Check for division by zero
                if right_val.as_rational().is_zero() {
                    return Err(Error::EvaluationError("Division by zero".to_string()));
                }

                let result = left_val.as_rational().div(right_val.as_rational());

                Ok(NumberValue::new_computed(result))
            }

            Expr::Pow(left, right) => {
                let left_val = left.evaluate()?;
                let right_val = right.evaluate()?;

                // Power operation has some limitations:
                // - Right side must be an integer
                // - For negative exponents, left side must be a non-zero rational

                // Check if the right value is an integer
                if !right_val.is_integer() {
                    return Err(Error::EvaluationError(
                        "Exponent must be an integer".to_string(),
                    ));
                }

                let exponent = right_val.to_integer();
                let left_rational = left_val.as_rational();

                if exponent.is_zero() {
                    // Anything^0 = 1 (except 0^0 which is undefined)
                    if left_rational.is_zero() {
                        return Err(Error::EvaluationError("0^0 is undefined".to_string()));
                    }
                    return Ok(NumberValue::new_integer(BigInt::one(), ExplicitSign::None));
                }

                let exponent_is_negative = exponent < BigInt::from(0);

                if exponent_is_negative && left_rational.is_zero() {
                    return Err(Error::EvaluationError(
                        "Division by zero in negative exponent".to_string(),
                    ));
                }

                // Handle both positive and negative exponents
                let abs_exp = exponent
                    .abs()
                    .to_i32()
                    .ok_or_else(|| Error::EvaluationError("Exponent too large".to_string()))?;

                if exponent_is_negative {
                    // For negative exponents, compute 1 / (base^|exponent|)
                    let base_pow = left_rational.pow(abs_exp);
                    let one = BigRational::from_integer(BigInt::one());
                    let result = one.div(base_pow);

                    Ok(NumberValue::new_computed(result))
                } else {
                    // For positive exponents, directly compute base^exponent
                    let result = left_rational.pow(abs_exp);

                    Ok(NumberValue::new_computed(result))
                }
            }

            Expr::Neg(expr) => {
                let value = expr.evaluate()?;

                // Create a negated value
                let result = value.as_rational().neg();

                Ok(NumberValue::new_computed(result))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::parse;
    use crate::number::NumberValue;
    use num_bigint::BigInt;
    use num_rational::BigRational;
    use std::str::FromStr;

    // Helper function to create expressions for testing with arbitrary precision integers
    #[allow(unused)]
    fn make_int_expr(op: fn(Box<Expr>, Box<Expr>) -> Expr, left: &str, right: &str) -> Expr {
        op(
            Box::new(Expr::Number(NumberValue::new_integer(
                BigInt::from_str(left).unwrap(),
                ExplicitSign::None,
            ))),
            Box::new(Expr::Number(NumberValue::new_integer(
                BigInt::from_str(right).unwrap(),
                ExplicitSign::None,
            ))),
        )
    }

    // Helper function to create expressions for testing with arbitrary precision rationals
    #[allow(unused)]
    fn make_rational_expr(
        op: fn(Box<Expr>, Box<Expr>) -> Expr,
        left: (BigInt, BigInt),
        right: (BigInt, BigInt),
    ) -> Expr {
        op(
            Box::new(Expr::Number(NumberValue::new_computed(BigRational::new(
                left.0, left.1,
            )))),
            Box::new(Expr::Number(NumberValue::new_computed(BigRational::new(
                right.0, right.1,
            )))),
        )
    }

    #[allow(unused)]
    fn make_neg_expr(value: &str) -> Expr {
        Expr::Neg(Box::new(Expr::Number(NumberValue::new_integer(
            BigInt::from_str(value).unwrap(),
            ExplicitSign::None,
        ))))
    }

    #[test]
    fn test_evaluate_basic() {
        // Test the evaluate method for some basic expressions
        let test_cases = [
            ("1+2", "3"),
            ("3-4", "-1"),
            ("5*6", "30"),
            ("8/4", "2"),
            ("2^10", "1024"),
            ("-5", "-5"),
            ("-(10)", "-10"),
        ];

        for (input, expected) in test_cases {
            let expr = parse(input).unwrap();
            let result = expr.evaluate().unwrap();
            assert!(result.is_integer(), "Expected integer result for {}", input);
            assert_eq!(result.to_string(), expected);
        }
    }

    #[test]
    fn test_evaluate_rational() {
        // Test the evaluate method for expressions with rational results
        let test_cases = [
            ("1.5+2.5", "4"),
            ("3.1-2.1", "1"),
            ("2.5*3", "15/2"),
            ("1/2", "1/2"),
            ("10/3", "10/3"),
            ("1.5^2", "9/4"),
        ];

        for (input, expected) in test_cases {
            let expr = parse(input).unwrap();
            let result = expr.evaluate().unwrap();

            // Use to_string() which will format correctly based on the value
            assert_eq!(result.to_string(), expected);

            // Additional check for integers if necessary
            if expected.contains('/') {
                assert!(!result.is_integer(), "Expected non-integer for {}", input);
            } else {
                assert!(result.is_integer(), "Expected integer for {}", input);
            }
        }
    }

    #[test]
    fn test_evaluate_large_numbers() {
        // Test evaluation with large numbers that would overflow regular integer types
        let large_num1 = "12345678901234567890";
        let large_num2 = "98765432109876543210";

        let expr = parse(&format!("{}+{}", large_num1, large_num2)).unwrap();
        let result = expr.evaluate().unwrap();
        assert!(result.is_integer(), "Expected integer result");
        assert_eq!(result.to_string(), "111111111011111111100");

        let expr = parse(&format!("{}*{}", large_num1, large_num2)).unwrap();
        let result = expr.evaluate().unwrap();
        assert!(result.is_integer(), "Expected integer result");
        assert_eq!(
            result.to_string(),
            "1219326311370217952237463801111263526900"
        );
    }

    #[test]
    fn test_error_cases() {
        // Test cases that should result in evaluation errors
        assert!(parse("1/0").unwrap().evaluate().is_err()); // Division by zero
        assert!(parse("0^0").unwrap().evaluate().is_err()); // 0^0 is undefined
        assert!(parse("0^-1").unwrap().evaluate().is_err()); // Division by zero in negative exponent
    }
}
