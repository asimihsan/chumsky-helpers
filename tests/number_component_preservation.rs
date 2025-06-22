use chumsky::Parser;
use chumsky_helpers::number::{Exponent, NumberParserBuilder, Sign};
use rstest::rstest;

#[rstest]
#[case("123.456e-7", "123", Some("456"), Some(Exponent{case:'e', sign:Sign::Negative, explicit_sign:true, value:"7".to_string()}))]
#[case("-987.654E+3", "987", Some("654"), Some(Exponent{case:'E', sign:Sign::Positive, explicit_sign:true, value:"3".to_string()}))]
#[case("42.", "42", Some(""), None)]
#[case("0.123", "0", Some("123"), None)]
fn preserves_components(
    #[case] input: &str,
    #[case] expected_base: &str,
    #[case] expected_decimal: Option<&str>,
    #[case] expected_exponent: Option<Exponent>,
) {
    let parser = NumberParserBuilder::new()
        .negative(true)
        .rational(true)
        .scientific(true)
        .build();

    let parsed = parser.parse(input).into_result().expect("parse failure");

    assert_eq!(parsed.base(), expected_base);
    assert_eq!(parsed.decimal(), expected_decimal);
    match (parsed.exponent(), &expected_exponent) {
        (None, None) => {}
        (Some(actual), Some(expected)) => assert_eq!(actual, expected),
        _ => panic!("exponent mismatch"),
    }

    assert_eq!(parsed.to_string(), input);
}
