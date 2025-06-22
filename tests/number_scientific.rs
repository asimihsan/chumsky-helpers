use chumsky::Parser;
use chumsky_helpers::number::{ExplicitSign, NumberParserBuilder};
use rstest::rstest;
mod common;
use common::assert_display_sign;

#[rstest]
#[case("1e3", ExplicitSign::None, "1", None, "3", false)]
#[case("-2E+4", ExplicitSign::Negative, "2", None, "4", true)]
#[case("+5e-2", ExplicitSign::Positive, "5", None, "2", true)]
#[case("10e0", ExplicitSign::None, "10", None, "0", false)]
#[case("1.23e2", ExplicitSign::None, "1", Some("23"), "2", false)]
#[case("-0.5E-1", ExplicitSign::Negative, "0", Some("5"), "1", true)]
#[case("+42.e+3", ExplicitSign::Positive, "42", Some(""), "3", true)]
#[case(".5e1", ExplicitSign::None, "0", Some("5"), "1", false)]
fn parses_scientific(
    #[case] input: &str,
    #[case] sign: ExplicitSign,
    #[case] base: &str,
    #[case] decimal: Option<&str>,
    #[case] exponent_value: &str,
    #[case] exponent_explicit_sign: bool,
) {
    let parser = NumberParserBuilder::new()
        .negative(true)
        .rational(true)
        .scientific(true)
        .build();

    let parsed = parser.parse(input).into_result().expect("parse failure");

    assert_eq!(parsed.base(), base);
    assert_eq!(parsed.decimal(), decimal);
    let exp = parsed.exponent().expect("expected exponent");
    assert_eq!(exp.value, exponent_value);
    assert_eq!(exp.explicit_sign, exponent_explicit_sign);

    assert_display_sign(&parsed.to_string(), sign);
}
