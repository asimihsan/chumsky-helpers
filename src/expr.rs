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
#[derive(Debug, Clone)]
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

/// Result of an expression evaluation
#[allow(unused)]
#[derive(Debug, Clone, PartialEq)]
pub enum EvalResult {
    /// Integer result
    Integer(i64),
    /// Floating point result
    Float(f64),
}

impl std::fmt::Display for EvalResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EvalResult::Integer(i) => write!(f, "{}", i),
            EvalResult::Float(fl) => {
                // Check if it's whole number and display without decimal if so
                if fl.fract() == 0.0 && fl.abs() < 1e15 {
                    write!(f, "{}", fl.trunc() as i64)
                } else {
                    write!(f, "{}", fl)
                }
            }
        }
    }
}

#[allow(unused)]
impl EvalResult {
    /// Convert to f64 regardless of the type
    pub fn as_f64(&self) -> f64 {
        match self {
            EvalResult::Integer(i) => *i as f64,
            EvalResult::Float(f) => *f,
        }
    }

    /// Convert to i64 if possible, or returns None if it would truncate
    pub fn as_i64(&self) -> Option<i64> {
        match self {
            EvalResult::Integer(i) => Some(*i),
            EvalResult::Float(f) => {
                if f.fract() == 0.0 && *f <= i64::MAX as f64 && *f >= i64::MIN as f64 {
                    Some(*f as i64)
                } else {
                    None
                }
            }
        }
    }
}

/// Evaluate an expression to compute its result
#[allow(unused)]
pub fn evaluate(expr: &Expr) -> Result<EvalResult, Error> {
    match expr {
        Expr::Number(n) => match n {
            NumberValue::Integer(i) => Ok(EvalResult::Integer(*i)),
            NumberValue::Float { value, .. } => Ok(EvalResult::Float(*value)),
        },
        Expr::Add(left, right) => {
            apply_binary_op(left, right, |l, r| l.checked_add(r), |l, r| Ok(l + r))
        }
        Expr::Sub(left, right) => {
            apply_binary_op(left, right, |l, r| l.checked_sub(r), |l, r| Ok(l - r))
        }
        Expr::Mul(left, right) => {
            apply_binary_op(left, right, |l, r| l.checked_mul(r), |l, r| Ok(l * r))
        }
        Expr::Div(left, right) => apply_binary_op(
            left,
            right,
            |l, r| {
                if r == 0 {
                    None // Will be converted to error in float operation
                } else {
                    l.checked_div(r)
                }
            },
            |l, r| {
                if r == 0.0 {
                    return Err(Error::ParseError("Division by zero".to_string()));
                }
                Ok(l / r)
            },
        ),
        Expr::Pow(left, right) => apply_binary_op(
            left,
            right,
            |l, r| {
                if r < 0 {
                    return None; // Negative exponent for integers handled as float
                }
                l.checked_pow(r as u32)
            },
            |l, r| {
                // Check for negative base with non-integer exponent (would give complex result)
                if l < 0.0 && r.fract() != 0.0 {
                    return Err(Error::ParseError(
                        "Cannot raise negative number to non-integer power (result would be complex)".to_string()
                    ));
                }
                Ok(l.powf(r))
            },
        ),
        Expr::Neg(expr) => {
            let result = evaluate(expr)?;
            match result {
                EvalResult::Integer(i) => Ok(EvalResult::Integer(-i)),
                EvalResult::Float(f) => Ok(EvalResult::Float(-f)),
            }
        }
    }
}

// Helper function to handle binary operations with the same pattern
#[inline]
fn apply_binary_op(
    left: &Expr,
    right: &Expr,
    int_op: impl Fn(i64, i64) -> Option<i64>,
    float_op: impl Fn(f64, f64) -> Result<f64, Error>,
) -> Result<EvalResult, Error> {
    let left_result = evaluate(left)?;
    let right_result = evaluate(right)?;

    match (&left_result, &right_result) {
        (EvalResult::Integer(l), EvalResult::Integer(r)) => {
            match int_op(*l, *r) {
                Some(result) => Ok(EvalResult::Integer(result)),
                None => {
                    // Integer operation failed (e.g., overflow), use float operation
                    let result = float_op(*l as f64, *r as f64)?;
                    Ok(EvalResult::Float(result))
                }
            }
        }
        _ => {
            // At least one operand is float, use float operation
            let left_float = left_result.as_f64();
            let right_float = right_result.as_f64();
            let result = float_op(left_float, right_float)?;
            Ok(EvalResult::Float(result))
        }
    }
}

/// Parse and evaluate an input string in one step
#[allow(unused)]
pub fn parse_and_evaluate(input: &str) -> Result<EvalResult, Error> {
    let expr = parse(input)?;
    evaluate(&expr)
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

    fn make_neg_float_expr(value: f64) -> Expr {
        Expr::Neg(Box::new(Expr::Number(NumberValue::Float {
            value,
            base: value.to_string().split('.').next().unwrap().to_string(),
            decimal: value.to_string().split('.').nth(1).map(|s| s.to_string()),
            exponent: None,
        })))
    }

    #[test]
    fn test_parse_and_evaluate_integers() {
        assert_eq!(parse_and_evaluate("1+2+3").unwrap(), EvalResult::Integer(6));
        assert_eq!(
            parse_and_evaluate("10+20+30").unwrap(),
            EvalResult::Integer(60)
        );
        assert_eq!(
            parse_and_evaluate("100+200+300").unwrap(),
            EvalResult::Integer(600)
        );
        assert_eq!(
            parse_and_evaluate("(1+2)+3").unwrap(),
            EvalResult::Integer(6)
        );
        assert_eq!(
            parse_and_evaluate("1+(2+3)").unwrap(),
            EvalResult::Integer(6)
        );
    }

    #[test]
    fn test_parse_with_floats() {
        assert_eq!(
            parse_and_evaluate("1.5+2.5").unwrap(),
            EvalResult::Float(4.0)
        );

        // Mixing integers and floats should produce a float
        assert_eq!(parse_and_evaluate("1+2.5").unwrap(), EvalResult::Float(3.5));

        // Floating point precision issue
        let result = parse_and_evaluate("0.1+0.2").unwrap();
        match result {
            EvalResult::Float(f) => {
                assert!((f - 0.3).abs() < 1e-14, "Expected approximately 0.3");
            }
            _ => panic!("Expected Float result"),
        }
    }

    #[test]
    fn test_parse_with_scientific() {
        assert_eq!(
            parse_and_evaluate("1e2+2e2").unwrap(),
            EvalResult::Float(300.0)
        );
        assert_eq!(
            parse_and_evaluate("1.5e1+2.5e0").unwrap(),
            EvalResult::Float(17.5)
        );
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

    #[test]
    fn test_eval_result_display() {
        // Test integer display
        assert_eq!(EvalResult::Integer(42).to_string(), "42");

        // Test float display with no fractional part
        assert_eq!(EvalResult::Float(42.0).to_string(), "42");

        // Test float display with fractional part
        assert_eq!(EvalResult::Float(42.5).to_string(), "42.5");
    }

    // New tests for subtraction
    #[test]
    fn test_evaluate_subtraction_integers() {
        let expr = make_expr(Expr::Sub, 10, 4);
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Integer(6));

        // Test negative result
        let expr = make_expr(Expr::Sub, 5, 10);
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Integer(-5));
    }

    #[test]
    fn test_evaluate_subtraction_floats() {
        let expr = make_float_expr(Expr::Sub, 10.5, 3.5);
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Float(7.0));

        let expr = make_float_expr(Expr::Sub, 0.3, 0.1);
        let result = evaluate(&expr).unwrap();
        match result {
            EvalResult::Float(f) => {
                // Floating point math needs approximate comparison
                assert!(
                    (f - 0.2).abs() < 1e-14,
                    "Expected approximately 0.2, got {}",
                    f
                );
            }
            _ => panic!("Expected Float result"),
        }
    }

    #[test]
    fn test_evaluate_subtraction_mixed() {
        let expr = make_mixed_expr(Expr::Sub, 10, 3.5);
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Float(6.5));

        let expr = make_expr(Expr::Sub, 5, 2);
        let expr = Expr::Sub(
            Box::new(expr),
            Box::new(Expr::Number(NumberValue::Float {
                value: 1.5,
                base: "1".to_string(),
                decimal: Some("5".to_string()),
                exponent: None,
            })),
        );
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Float(1.5));
    }

    // Tests for multiplication
    #[test]
    fn test_evaluate_multiplication_integers() {
        let expr = make_expr(Expr::Mul, 6, 7);
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Integer(42));

        // Test zero multiplication
        let expr = make_expr(Expr::Mul, 123, 0);
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Integer(0));

        // Test negative multiplication
        let expr = make_expr(Expr::Mul, -5, 4);
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Integer(-20));

        let expr = make_expr(Expr::Mul, -5, -4);
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Integer(20));
    }

    #[test]
    fn test_evaluate_multiplication_floats() {
        let expr = make_float_expr(Expr::Mul, 2.5, 4.0);
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Float(10.0));

        // Test with irrational result
        let expr = make_float_expr(Expr::Mul, 1.1, 1.1);
        let result = evaluate(&expr).unwrap();
        match result {
            EvalResult::Float(f) => {
                assert!(
                    (f - 1.21).abs() < 1e-14,
                    "Expected approximately 1.21, got {}",
                    f
                );
            }
            _ => panic!("Expected Float result"),
        }
    }

    #[test]
    fn test_evaluate_multiplication_overflow() {
        // Test integer overflow
        let expr = make_expr(Expr::Mul, i64::MAX, 2);
        let result = evaluate(&expr).unwrap();
        match result {
            EvalResult::Float(f) => {
                // Should convert to float to handle overflow
                assert!(f > i64::MAX as f64);
            }
            _ => panic!("Expected Float result for overflow case"),
        }
    }

    // Tests for division
    #[test]
    fn test_evaluate_division_integers() {
        let expr = make_expr(Expr::Div, 10, 2);
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Integer(5));

        // Test integer division that produces a float
        let expr = make_expr(Expr::Div, 10, 3);
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Integer(3));

        // Test negative division
        let expr = make_expr(Expr::Div, -10, 2);
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Integer(-5));

        let expr = make_expr(Expr::Div, 10, -2);
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Integer(-5));

        let expr = make_expr(Expr::Div, -10, -2);
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Integer(5));
    }

    #[test]
    fn test_evaluate_division_by_zero() {
        // Division by zero should return an error
        let expr = make_expr(Expr::Div, 42, 0);
        assert!(evaluate(&expr).is_err());

        // Test with a tiny float divisor
        let expr = make_float_expr(Expr::Div, 1.0, 1e-300);
        // Should evaluate to a very large number, not error
        assert!(evaluate(&expr).is_ok());
    }

    #[test]
    fn test_evaluate_division_floats() {
        let expr = make_float_expr(Expr::Div, 7.5, 2.5);
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Float(3.0));
    }

    // Tests for power operation
    #[test]
    fn test_evaluate_power_integers() {
        let expr = make_expr(Expr::Pow, 2, 3);
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Integer(8));

        // Test power of 0
        let expr = make_expr(Expr::Pow, 5, 0);
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Integer(1));

        // Test negative base
        let expr = make_expr(Expr::Pow, -2, 2);
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Integer(4));

        let expr = make_expr(Expr::Pow, -2, 3);
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Integer(-8));
    }

    #[test]
    fn test_evaluate_power_non_integer_exponents() {
        // Fractional powers will return floats
        let expr = make_mixed_expr(Expr::Pow, 4, 0.5);
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Float(2.0));

        // Negative bases with fractional exponents are complex numbers
        // This should error as our calculator doesn't support complex numbers
        let expr = make_mixed_expr(Expr::Pow, -4, 0.5);
        assert!(evaluate(&expr).is_err());
    }

    #[test]
    fn test_evaluate_power_large_exponents() {
        // Large powers might overflow integers
        let expr = make_expr(Expr::Pow, 2, 63);
        let result = evaluate(&expr).unwrap();
        match result {
            EvalResult::Float(f) => {
                // Should be around 2^63
                assert!((f - 9.223372036854776e18).abs() < 1e5);
            }
            _ => panic!("Expected Float result for large power"),
        }
    }

    // Tests for negation
    #[test]
    fn test_evaluate_negation_integers() {
        let expr = make_neg_expr(42);
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Integer(-42));

        // Double negation
        let expr = Expr::Neg(Box::new(make_neg_expr(42)));
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Integer(42));

        // Negating zero
        let expr = make_neg_expr(0);
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Integer(0));
    }

    #[test]
    fn test_evaluate_negation_floats() {
        let expr = make_neg_float_expr(2.5);
        assert_eq!(evaluate(&expr).unwrap(), EvalResult::Float(-2.5));

        // Negating a number close to zero
        let expr = make_neg_float_expr(1e-100);
        let result = evaluate(&expr).unwrap();
        match result {
            EvalResult::Float(f) => {
                assert!(f < 0.0 && f > -1e-99);
            }
            _ => panic!("Expected Float result"),
        }
    }

    // Tests for complex expressions with operator precedence
    #[test]
    fn test_evaluate_complex_expressions() {
        // Test a complex expression: 2 * (3 + 4) - 5 = 9
        let add_expr = make_expr(Expr::Add, 3, 4);
        let mul_expr = Expr::Mul(
            Box::new(Expr::Number(NumberValue::Integer(2))),
            Box::new(add_expr),
        );
        let sub_expr = Expr::Sub(
            Box::new(mul_expr),
            Box::new(Expr::Number(NumberValue::Integer(5))),
        );

        assert_eq!(evaluate(&sub_expr).unwrap(), EvalResult::Integer(9));

        // Test a complex expression with mixed types: 2.5 * (3 - 1) + 0.5 = 5.5
        let sub_expr = make_expr(Expr::Sub, 3, 1);
        let mul_expr = Expr::Mul(
            Box::new(Expr::Number(NumberValue::Float {
                value: 2.5,
                base: "2".to_string(),
                decimal: Some("5".to_string()),
                exponent: None,
            })),
            Box::new(sub_expr),
        );
        let add_expr = Expr::Add(
            Box::new(mul_expr),
            Box::new(Expr::Number(NumberValue::Float {
                value: 0.5,
                base: "0".to_string(),
                decimal: Some("5".to_string()),
                exponent: None,
            })),
        );

        assert_eq!(evaluate(&add_expr).unwrap(), EvalResult::Float(5.5));
    }

    #[test]
    fn test_evaluate_numerical_stability() {
        // Test floating point stability with small numbers
        let expr = make_float_expr(Expr::Add, 1e-16, 1.0);
        let result = evaluate(&expr).unwrap();
        match result {
            EvalResult::Float(f) => {
                // Should be very close to 1.0 due to precision limits
                assert!((f - 1.0).abs() < 1e-15);
            }
            _ => panic!("Expected Float result"),
        }

        // Test with very large numbers
        let expr = make_float_expr(Expr::Add, 1e200, 1e-200);
        let result = evaluate(&expr).unwrap();
        match result {
            EvalResult::Float(f) => {
                // Should essentially be equal to the larger number
                assert!((f - 1e200).abs() / 1e200 < 1e-15);
            }
            _ => panic!("Expected Float result"),
        }
    }
}
