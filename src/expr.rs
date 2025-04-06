// Copyright 2025 Asim Ihsan
//
// This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
// If a copy of the MPL was not distributed with this file, You can obtain one at https://mozilla.org/MPL/2.0/.
//
// SPDX-License-Identifier: MPL-2.0

use crate::number::{NumberParserBuilder, NumberValue};
use chumsky::prelude::*;

#[allow(unused)]
#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("Parse error: {0}")]
    ParseError(String),
}

/// An expression type for our calculator
#[allow(unused)]
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// A numeric literal value
    Number(NumberValue),

    /// Addition operation (a + b)
    Add(Box<Expr>, Box<Expr>),

    /// Subtraction operation (a - b)
    Sub(Box<Expr>, Box<Expr>),

    /// Multiplication operation (a * b)
    Mul(Box<Expr>, Box<Expr>),

    /// Division operation (a / b)
    Div(Box<Expr>, Box<Expr>),

    /// Power operation (a ^ b)
    Pow(Box<Expr>, Box<Expr>),

    /// Unary negation (-a)
    Neg(Box<Expr>),
}

/// Parse an input string into an expression AST
#[allow(unused)]
pub fn parse(input: &str) -> Result<Expr, Error> {
    // Build the parser
    let expr_parser = parser();

    // Parse the input and convert errors to our Error type
    match expr_parser.parse(input).into_result() {
        Ok(expr) => Ok(expr),
        Err(errs) => {
            let msg = errs.into_iter().map(|e| e.to_string()).collect::<Vec<_>>().join(", ");
            Err(Error::ParseError(msg))
        }
    }
}

/// Create the parser for our expression language
fn parser<'a>() -> impl Parser<'a, &'a str, Expr, extra::Err<Rich<'a, char>>> {
    // Use recursive parsing to handle nested expressions
    recursive(|expr| {
        // Number parser that supports integers, floats, and scientific notation
        let make_number = NumberParserBuilder::new()
            .negative(true)
            .float(true)
            .scientific(true)
            .build()
            .map(Expr::Number)
            .boxed();

        let atom = make_number.or(expr.delimited_by(just('('), just(')'))).padded();

        let op = |c| just(c).padded();

        let unary = op('-').repeated().foldr(atom, |_op, rhs| Expr::Neg(Box::new(rhs)));

        let product = unary.clone().foldl(
            choice((
                op('*').to(Expr::Mul as fn(_, _) -> _),
                op('/').to(Expr::Div as fn(_, _) -> _),
            ))
            .then(unary)
            .repeated(),
            |lhs, (op, rhs)| op(Box::new(lhs), Box::new(rhs)),
        );

        product.clone().foldl(
            choice((
                op('+').to(Expr::Add as fn(_, _) -> _),
                op('-').to(Expr::Sub as fn(_, _) -> _),
            ))
            .then(product)
            .repeated(),
            |lhs, (op, rhs)| op(Box::new(lhs), Box::new(rhs)),
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::number::NumberValue;

    // Helper function to create expressions for testing
    fn make_expr(op: fn(Box<Expr>, Box<Expr>) -> Expr, left: i64, right: i64) -> Expr {
        op(
            Box::new(Expr::Number(NumberValue::Integer(left))),
            Box::new(Expr::Number(NumberValue::Integer(right))),
        )
    }

    fn make_float_expr(op: fn(Box<Expr>, Box<Expr>) -> Expr, left: f64, right: f64) -> Expr {
        op(
            Box::new(Expr::Number(NumberValue::Float {
                value: left,
                base: left.to_string().split('.').next().unwrap().to_string(),
                decimal: left.to_string().split('.').nth(1).map(|s| s.to_string()),
                exponent: None,
            })),
            Box::new(Expr::Number(NumberValue::Float {
                value: right,
                base: right.to_string().split('.').next().unwrap().to_string(),
                decimal: right.to_string().split('.').nth(1).map(|s| s.to_string()),
                exponent: None,
            })),
        )
    }

    #[allow(unused)]
    fn make_mixed_expr(op: fn(Box<Expr>, Box<Expr>) -> Expr, left: i64, right: f64) -> Expr {
        op(
            Box::new(Expr::Number(NumberValue::Integer(left))),
            Box::new(Expr::Number(NumberValue::Float {
                value: right,
                base: right.to_string().split('.').next().unwrap().to_string(),
                decimal: right.to_string().split('.').nth(1).map(|s| s.to_string()),
                exponent: None,
            })),
        )
    }

    fn make_neg_expr(value: i64) -> Expr {
        Expr::Neg(Box::new(Expr::Number(NumberValue::Integer(value))))
    }

    #[allow(unused)]
    fn make_neg_float_expr(value: f64) -> Expr {
        Expr::Neg(Box::new(Expr::Number(NumberValue::Float {
            value,
            base: value.to_string().split('.').next().unwrap().to_string(),
            decimal: value.to_string().split('.').nth(1).map(|s| s.to_string()),
            exponent: None,
        })))
    }

    #[test]
    fn test_parse_integers() {
        let expr = parse("1+2").unwrap();
        match expr {
            Expr::Add(left, right) => {
                assert_eq!(*left, make_expr(Expr::Add, 1, 2));
                assert_eq!(*right, make_expr(Expr::Add, 1, 2));
            }
            _ => panic!("Expected Add node at root"),
        }

        let expr = parse("3-4").unwrap();
        match expr {
            Expr::Sub(left, right) => {
                assert_eq!(*left, make_expr(Expr::Sub, 3, 4));
                assert_eq!(*right, make_expr(Expr::Sub, 3, 4));
            }
            _ => panic!("Expected Sub node at root"),
        }

        let expr = parse("5*6").unwrap();
        match expr {
            Expr::Mul(left, right) => {
                assert_eq!(*left, make_expr(Expr::Mul, 5, 6));
                assert_eq!(*right, make_expr(Expr::Mul, 5, 6));
            }
            _ => panic!("Expected Mul node at root"),
        }

        let expr = parse("7/8").unwrap();
        match expr {
            Expr::Div(left, right) => {
                assert_eq!(*left, make_expr(Expr::Div, 7, 8));
                assert_eq!(*right, make_expr(Expr::Div, 7, 8));
            }
            _ => panic!("Expected Div node at root"),
        }

        let expr = parse("9^10").unwrap();
        match expr {
            Expr::Pow(left, right) => {
                assert_eq!(*left, make_expr(Expr::Pow, 9, 10));
                assert_eq!(*right, make_expr(Expr::Pow, 9, 10));
            }
            _ => panic!("Expected Pow node at root"),
        }

        let expr = parse("-11").unwrap();
        match expr {
            Expr::Neg(inner) => {
                assert_eq!(*inner, make_neg_expr(11));
            }
            _ => panic!("Expected Neg node at root"),
        }

        let expr = parse("-(12)").unwrap();
        match expr {
            Expr::Neg(inner) => {
                assert_eq!(*inner, make_neg_expr(12));
            }
            _ => panic!("Expected Neg node at root"),
        }
    }

    #[test]
    fn test_parse_floats() {
        let expr = parse("1.5+2.5").unwrap();
        match expr {
            Expr::Add(left, right) => {
                assert_eq!(*left, make_float_expr(Expr::Add, 1.5, 2.5));
                assert_eq!(*right, make_float_expr(Expr::Add, 1.5, 2.5));
            }
            _ => panic!("Expected Add node at root"),
        }
    }

    #[test]
    fn test_parse_with_scientific() {
        let expr = parse("1.5e2+2.5e3").unwrap();
        match expr {
            Expr::Add(left, right) => {
                assert_eq!(*left, make_float_expr(Expr::Add, 1.5e2, 2.5e3));
                assert_eq!(*right, make_float_expr(Expr::Add, 1.5e2, 2.5e3));
            }
            _ => panic!("Expected Add node at root"),
        }
    }

    #[test]
    fn test_parse_invalid() {
        assert!(parse("1+").is_err());
        assert!(parse("+").is_err());
        assert!(parse("()").is_err());
    }

    #[test]
    fn test_parse_ast() {
        // Test that we get a proper AST from parsing
        let expr = parse("1+2").unwrap();
        match expr {
            Expr::Add(left, right) => {
                match *left {
                    Expr::Number(n) => {
                        if let NumberValue::Integer(i) = n {
                            assert_eq!(i, 1);
                        } else {
                            panic!("Expected Integer variant");
                        }
                    }
                    _ => panic!("Expected Number node for left child"),
                }
                match *right {
                    Expr::Number(n) => {
                        if let NumberValue::Integer(i) = n {
                            assert_eq!(i, 2);
                        } else {
                            panic!("Expected Integer variant");
                        }
                    }
                    _ => panic!("Expected Number node for right child"),
                }
            }
            _ => panic!("Expected Add node at root"),
        }
    }
}
