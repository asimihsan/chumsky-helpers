use bon::Builder;
use chumsky::Parser;
use chumsky_helpers::number::{ExplicitSign, NumberParserBuilder};
use rstest::rstest;
mod common;
use common::assert_display_sign;

#[derive(Debug, Builder)]
struct ScientificCase {
    input: &'static str,
    sign: ExplicitSign,
    base: &'static str,
    decimal: Option<&'static str>,
    exponent_value: &'static str,
    exponent_explicit_sign: bool,
}

#[rstest]
#[case(ScientificCase::builder().input("1e3").sign(ExplicitSign::None).base("1").exponent_value("3").exponent_explicit_sign(false).build())]
#[case(ScientificCase::builder().input("-2E+4").sign(ExplicitSign::Negative).base("2").exponent_value("4").exponent_explicit_sign(true).build())]
#[case(ScientificCase::builder().input("+5e-2").sign(ExplicitSign::Positive).base("5").exponent_value("2").exponent_explicit_sign(true).build())]
#[case(ScientificCase::builder().input("10e0").sign(ExplicitSign::None).base("10").exponent_value("0").exponent_explicit_sign(false).build())]
#[case(ScientificCase::builder().input("1.23e2").sign(ExplicitSign::None).base("1").decimal("23").exponent_value("2").exponent_explicit_sign(false).build())]
#[case(ScientificCase::builder().input("-0.5E-1").sign(ExplicitSign::Negative).base("0").decimal("5").exponent_value("1").exponent_explicit_sign(true).build())]
#[case(ScientificCase::builder().input("+42.e+3").sign(ExplicitSign::Positive).base("42").decimal("").exponent_value("3").exponent_explicit_sign(true).build())]
#[case(ScientificCase::builder().input(".5e1").sign(ExplicitSign::None).base("0").decimal("5").exponent_value("1").exponent_explicit_sign(false).build())]
fn parses_scientific(#[case] c: ScientificCase) {
    let parser = NumberParserBuilder::new()
        .negative(true)
        .rational(true)
        .scientific(true)
        .build();

    let parsed = parser.parse(c.input).into_result().expect("parse failure");

    assert_eq!(parsed.base(), c.base);
    assert_eq!(parsed.decimal(), c.decimal);
    let exp = parsed.exponent().expect("expected exponent");
    assert_eq!(exp.value, c.exponent_value);
    assert_eq!(exp.explicit_sign, c.exponent_explicit_sign);

    assert_display_sign(&parsed.to_string(), c.sign);
}
