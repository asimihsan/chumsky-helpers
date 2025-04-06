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

    #[error("Evaluation error: {0}")]
    EvaluationError(String),
}

/// An expression type for our calculator with arbitrary precision arithmetic
#[allow(unused)]
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    /// A numeric literal value with arbitrary precision
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
        // Number parser that supports integers, rationals, and scientific notation
        let make_number = NumberParserBuilder::new()
            .negative(true)
            .rational(true)
            .scientific(true)
            .build()
            .map(Expr::Number)
            .boxed();

        let atom = make_number.or(expr.delimited_by(just('('), just(')'))).padded();

        let op = |c| just(c).padded();

        // Unary negation has highest precedence
        let unary = op('-').repeated().foldr(atom, |_op, rhs| Expr::Neg(Box::new(rhs)));

        // Power has next highest precedence
        let power = unary.clone().foldl(
            op('^').to(Expr::Pow as fn(_, _) -> _).then(unary).repeated(),
            |lhs, (op, rhs)| op(Box::new(lhs), Box::new(rhs)),
        );

        // Product has middle precedence
        let product = power.clone().foldl(
            choice((
                op('*').to(Expr::Mul as fn(_, _) -> _),
                op('/').to(Expr::Div as fn(_, _) -> _),
            ))
            .then(power)
            .repeated(),
            |lhs, (op, rhs)| op(Box::new(lhs), Box::new(rhs)),
        );

        // Sum has lowest precedence
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
    use crate::number::Sign;
    use num_bigint::BigInt;
    use num_rational::BigRational;

    #[test]
    fn test_parse_integers() {
        let expr = parse("1+2").unwrap();
        match expr {
            Expr::Add(left, right) => {
                // Check left operand
                match &*left {
                    Expr::Number(num) => {
                        assert!(num.is_integer(), "Left operand should be an integer");
                        assert_eq!(num.to_integer(), BigInt::from(1));
                    }
                    _ => panic!("Expected Number node for left child"),
                }

                // Check right operand
                match &*right {
                    Expr::Number(num) => {
                        assert!(num.is_integer(), "Right operand should be an integer");
                        assert_eq!(num.to_integer(), BigInt::from(2));
                    }
                    _ => panic!("Expected Number node for right child"),
                }
            }
            _ => panic!("Expected Add node at root"),
        }

        let expr = parse("3-4").unwrap();
        match expr {
            Expr::Sub(left, right) => {
                // Check left operand
                match &*left {
                    Expr::Number(num) => {
                        assert!(num.is_integer(), "Left operand should be an integer");
                        assert_eq!(num.to_integer(), BigInt::from(3));
                    }
                    _ => panic!("Expected Number node for left child"),
                }

                // Check right operand
                match &*right {
                    Expr::Number(num) => {
                        assert!(num.is_integer(), "Right operand should be an integer");
                        assert_eq!(num.to_integer(), BigInt::from(4));
                    }
                    _ => panic!("Expected Number node for right child"),
                }
            }
            _ => panic!("Expected Sub node at root"),
        }

        let expr = parse("5*6").unwrap();
        match expr {
            Expr::Mul(left, right) => {
                // Check left operand
                match &*left {
                    Expr::Number(num) => {
                        assert!(num.is_integer(), "Left operand should be an integer");
                        assert_eq!(num.to_integer(), BigInt::from(5));
                    }
                    _ => panic!("Expected Number node for left child"),
                }

                // Check right operand
                match &*right {
                    Expr::Number(num) => {
                        assert!(num.is_integer(), "Right operand should be an integer");
                        assert_eq!(num.to_integer(), BigInt::from(6));
                    }
                    _ => panic!("Expected Number node for right child"),
                }
            }
            _ => panic!("Expected Mul node at root"),
        }

        let expr = parse("7/8").unwrap();
        match expr {
            Expr::Div(left, right) => {
                // Check left operand
                match &*left {
                    Expr::Number(num) => {
                        assert!(num.is_integer(), "Left operand should be an integer");
                        assert_eq!(num.to_integer(), BigInt::from(7));
                    }
                    _ => panic!("Expected Number node for left child"),
                }

                // Check right operand
                match &*right {
                    Expr::Number(num) => {
                        assert!(num.is_integer(), "Right operand should be an integer");
                        assert_eq!(num.to_integer(), BigInt::from(8));
                    }
                    _ => panic!("Expected Number node for right child"),
                }
            }
            _ => panic!("Expected Div node at root"),
        }

        let expr = parse("9^10").unwrap();
        match expr {
            Expr::Pow(left, right) => {
                // Check left operand
                match &*left {
                    Expr::Number(num) => {
                        assert!(num.is_integer(), "Left operand should be an integer");
                        assert_eq!(num.to_integer(), BigInt::from(9));
                    }
                    _ => panic!("Expected Number node for left child"),
                }

                // Check right operand
                match &*right {
                    Expr::Number(num) => {
                        assert!(num.is_integer(), "Right operand should be an integer");
                        assert_eq!(num.to_integer(), BigInt::from(10));
                    }
                    _ => panic!("Expected Number node for right child"),
                }
            }
            _ => panic!("Expected Pow node at root"),
        }

        let expr = parse("-11").unwrap();
        match expr {
            Expr::Neg(inner) => match *inner {
                Expr::Number(num) => {
                    assert!(num.is_integer(), "Operand should be an integer");
                    assert_eq!(num.to_integer(), BigInt::from(11));
                }
                _ => panic!("Expected Number node for inner expression"),
            },
            _ => panic!("Expected Neg node at root"),
        }

        let expr = parse("-(12)").unwrap();
        match expr {
            Expr::Neg(inner) => match *inner {
                Expr::Number(num) => {
                    assert!(num.is_integer(), "Operand should be an integer");
                    assert_eq!(num.to_integer(), BigInt::from(12));
                }
                _ => panic!("Expected Number node for inner expression"),
            },
            _ => panic!("Expected Neg node at root"),
        }
    }

    #[test]
    fn test_parse_rationals() {
        let expr = parse("1.5+2.5").unwrap();
        match expr {
            Expr::Add(left, right) => {
                // Check left operand
                match &*left {
                    Expr::Number(num) => {
                        let expected_left = BigRational::new(BigInt::from(15), BigInt::from(10));
                        assert_eq!(num.as_rational(), &expected_left);
                    }
                    _ => panic!("Expected Number node for left child"),
                }

                // Check right operand
                match &*right {
                    Expr::Number(num) => {
                        let expected_right = BigRational::new(BigInt::from(25), BigInt::from(10));
                        assert_eq!(num.as_rational(), &expected_right);
                    }
                    _ => panic!("Expected Number node for right child"),
                }
            }
            _ => panic!("Expected Add node at root"),
        }
    }

    #[test]
    fn test_parse_with_scientific() {
        let expr = parse("1.5e2+2.5e3").unwrap();
        match expr {
            Expr::Add(left, right) => {
                // Check left operand
                match &*left {
                    Expr::Number(num) => {
                        // 1.5e2 = 150
                        let expected_left = BigRational::new(BigInt::from(150), BigInt::from(1));
                        assert_eq!(num.as_rational(), &expected_left);

                        // Also verify exponent component
                        let exp = num.exponent().unwrap();
                        assert_eq!(exp.sign, Sign::None);
                        assert_eq!(exp.value, "2");
                        assert_eq!(exp.case, 'e');
                    }
                    _ => panic!("Expected Number node for left child"),
                }

                // Check right operand
                match &*right {
                    Expr::Number(num) => {
                        // 2.5e3 = 2500
                        let expected_right = BigRational::new(BigInt::from(2500), BigInt::from(1));
                        assert_eq!(num.as_rational(), &expected_right);

                        // Also verify exponent component
                        let exp = num.exponent().unwrap();
                        assert_eq!(exp.case, 'e');
                        assert_eq!(exp.sign, Sign::None);
                        assert_eq!(exp.value, "3");
                    }
                    _ => panic!("Expected Number node for right child"),
                }
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
                        assert!(n.is_integer(), "Left operand should be an integer");
                        assert_eq!(n.to_integer(), BigInt::from(1));
                    }
                    _ => panic!("Expected Number node for left child"),
                }
                match *right {
                    Expr::Number(n) => {
                        assert!(n.is_integer(), "Right operand should be an integer");
                        assert_eq!(n.to_integer(), BigInt::from(2));
                    }
                    _ => panic!("Expected Number node for right child"),
                }
            }
            _ => panic!("Expected Add node at root"),
        }
    }
}
