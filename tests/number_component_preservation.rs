use bon::Builder;
use chumsky::Parser;
use chumsky_helpers::number::{Exponent, NumberParserBuilder, Sign};
use rstest::rstest;

#[derive(Debug, Builder)]
struct ComponentCase {
    input: &'static str,
    expected_base: &'static str,
    expected_decimal: Option<&'static str>,
    expected_exponent: Option<Exponent>,
}

#[rstest]
#[case(ComponentCase::builder()
    .input("123.456e-7")
    .expected_base("123")
    .expected_decimal("456")
    .expected_exponent(Exponent{case:'e', sign:Sign::Negative, explicit_sign:true, value:"7".to_string()})
    .build())]
#[case(ComponentCase::builder()
    .input("-987.654E+3")
    .expected_base("987")
    .expected_decimal("654")
    .expected_exponent(Exponent{case:'E', sign:Sign::Positive, explicit_sign:true, value:"3".to_string()})
    .build())]
#[case(ComponentCase::builder().input("42.").expected_base("42").expected_decimal("").build())]
#[case(ComponentCase::builder().input("0.123").expected_base("0").expected_decimal("123").build())]
fn preserves_components(#[case] c: ComponentCase) {
    let parser = NumberParserBuilder::new()
        .negative(true)
        .rational(true)
        .scientific(true)
        .build();

    let parsed = parser.parse(c.input).into_result().expect("parse failure");

    assert_eq!(parsed.base(), c.expected_base);
    assert_eq!(parsed.decimal(), c.expected_decimal);
    match (parsed.exponent(), &c.expected_exponent) {
        (None, None) => {}
        (Some(actual), Some(expected)) => assert_eq!(actual, expected),
        _ => panic!("exponent mismatch"),
    }

    assert_eq!(parsed.to_string(), c.input);
}
