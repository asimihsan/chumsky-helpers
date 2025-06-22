use chumsky::Parser;
use chumsky_helpers::number::{ExplicitSign, NumberParserBuilder};
use num_bigint::BigInt;
use rstest::rstest;
mod common;
use common::assert_display_sign;

#[rstest]
#[case("0", 0, ExplicitSign::None)]
#[case("42", 42, ExplicitSign::None)]
#[case("+123", 123, ExplicitSign::Positive)]
#[case("-5", -5, ExplicitSign::Negative)]
#[case("-0", 0, ExplicitSign::Negative)]
fn parses_integers(#[case] input: &str, #[case] expected: i64, #[case] sign: ExplicitSign) {
    let parser = NumberParserBuilder::new().negative(true).build();
    let parsed = parser.parse(input).into_result().expect("parse failure");

    // Then
    assert_eq!(parsed.to_integer(), BigInt::from(expected));
    assert_eq!(parsed.to_string(), input);
    assert_display_sign(&parsed.to_string(), sign);
}
