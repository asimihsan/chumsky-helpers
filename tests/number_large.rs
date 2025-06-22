use chumsky::Parser;
use chumsky_helpers::number::NumberParserBuilder;
use rstest::rstest;

#[rstest]
#[case("12345678901234567890123456789012345678901234567890")]
#[case("123456789012345678901234567890")]
#[case("-987654321098765432109876543210")]
#[case("1234567890.0987654321")]
#[case("1.23456789e+30")]
#[case("-9.8765e-25")]
fn parses_large_numbers(#[case] input: &str) {
    let parser = NumberParserBuilder::new()
        .negative(true)
        .rational(true)
        .scientific(true)
        .build();

    assert!(parser.parse(input).into_result().is_ok(), "failed to parse {}", input);
}
