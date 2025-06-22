use bon::Builder;
use chumsky::Parser;
use chumsky_helpers::number::{ExplicitSign, NumberParserBuilder, NumberValue};
use rstest::rstest;
use std::str::FromStr;
mod common;
use common::assert_display_sign;

#[derive(Debug, Builder)]
struct DecimalCase {
    input: &'static str,
    sign: ExplicitSign,
    base: &'static str,
    decimal: Option<&'static str>,
    exponent: Option<&'static str>,
}

#[rstest]
#[case(DecimalCase::builder().input("0.0").sign(ExplicitSign::None).base("0").decimal("0").build())]
#[case(DecimalCase::builder().input("1.5").sign(ExplicitSign::None).base("1").decimal("5").build())]
#[case(DecimalCase::builder().input("-0.25").sign(ExplicitSign::Negative).base("0").decimal("25").build())]
#[case(DecimalCase::builder().input("+100.001").sign(ExplicitSign::Positive).base("100").decimal("001").build())]
#[case(DecimalCase::builder().input("42.").sign(ExplicitSign::None).base("42").decimal("").build())]
#[case(DecimalCase::builder().input(".5").sign(ExplicitSign::None).base("0").decimal("5").build())]
#[case(DecimalCase::builder().input("-.12").sign(ExplicitSign::Negative).base("0").decimal("12").build())]
fn parses_decimals(#[case] c: DecimalCase) {
    let parser = NumberParserBuilder::new().negative(true).rational(true).build();

    let parsed = parser.parse(c.input).into_result().expect("parse failure");

    // Base, decimal, exponent components
    assert_eq!(parsed.base(), c.base);
    assert_eq!(parsed.decimal(), c.decimal);
    assert_eq!(parsed.exponent().map(|e| e.value.as_str()), c.exponent);

    // Sign via Display prefix
    assert_display_sign(&parsed.to_string(), c.sign);

    // Rational round-trip matches
    let expected = NumberValue::from_str(c.input).unwrap().to_rational();
    assert_eq!(parsed.to_rational(), expected);
}
