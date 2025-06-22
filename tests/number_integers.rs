use bon::Builder;
use chumsky::Parser;
use chumsky_helpers::number::{ExplicitSign, NumberParserBuilder};
use num_bigint::BigInt;
use rstest::rstest;
mod common;
use common::assert_display_sign;

#[derive(Debug, Builder)]
struct IntegerCase {
    input: &'static str,
    expected: i64,
    sign: ExplicitSign,
}

#[rstest]
#[case(IntegerCase::builder().input("0").expected(0).sign(ExplicitSign::None).build())]
#[case(IntegerCase::builder().input("42").expected(42).sign(ExplicitSign::None).build())]
#[case(IntegerCase::builder().input("+123").expected(123).sign(ExplicitSign::Positive).build())]
#[case(IntegerCase::builder().input("-5").expected(-5).sign(ExplicitSign::Negative).build())]
#[case(IntegerCase::builder().input("-0").expected(0).sign(ExplicitSign::Negative).build())]
fn parses_integers(#[case] c: IntegerCase) {
    let parser = NumberParserBuilder::new().negative(true).build();
    let parsed = parser.parse(c.input).into_result().expect("parse failure");

    // Then
    assert_eq!(parsed.to_integer(), BigInt::from(c.expected));
    assert_eq!(parsed.to_string(), c.input);
    assert_display_sign(&parsed.to_string(), c.sign);
}
