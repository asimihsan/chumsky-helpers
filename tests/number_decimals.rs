use chumsky::Parser;
use chumsky_helpers::number::{ExplicitSign, NumberParserBuilder, NumberValue};
use rstest::rstest;
use std::str::FromStr;
mod common;
use common::assert_display_sign;

#[rstest]
#[case("0.0", ExplicitSign::None, "0", Some("0"), None)]
#[case("1.5", ExplicitSign::None, "1", Some("5"), None)]
#[case("-0.25", ExplicitSign::Negative, "0", Some("25"), None)]
#[case("+100.001", ExplicitSign::Positive, "100", Some("001"), None)]
#[case("42.", ExplicitSign::None, "42", Some(""), None)]
#[case(".5", ExplicitSign::None, "0", Some("5"), None)]
#[case("-.12", ExplicitSign::Negative, "0", Some("12"), None)]
fn parses_decimals(
    #[case] input: &str,
    #[case] sign: ExplicitSign,
    #[case] base: &str,
    #[case] decimal: Option<&str>,
    #[case] exponent: Option<&str>,
) {
    let parser = NumberParserBuilder::new().negative(true).rational(true).build();

    let parsed = parser.parse(input).into_result().expect("parse failure");

    // Base, decimal, exponent components
    assert_eq!(parsed.base(), base);
    assert_eq!(parsed.decimal(), decimal);
    assert_eq!(parsed.exponent().map(|e| e.value.as_str()), exponent);

    // Sign via Display prefix
    assert_display_sign(&parsed.to_string(), sign);

    // Rational round-trip matches
    let expected = NumberValue::from_str(input).unwrap().to_rational();
    assert_eq!(parsed.to_rational(), expected);
}
