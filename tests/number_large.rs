use bon::Builder;
use chumsky::Parser;
use chumsky_helpers::number::NumberParserBuilder;
use rstest::rstest;

#[derive(Debug, Builder)]
struct LargeCase {
    input: &'static str,
}

#[rstest]
#[case(LargeCase::builder().input("12345678901234567890123456789012345678901234567890").build())]
#[case(LargeCase::builder().input("123456789012345678901234567890").build())]
#[case(LargeCase::builder().input("-987654321098765432109876543210").build())]
#[case(LargeCase::builder().input("1234567890.0987654321").build())]
#[case(LargeCase::builder().input("1.23456789e+30").build())]
#[case(LargeCase::builder().input("-9.8765e-25").build())]
fn parses_large_numbers(#[case] c: LargeCase) {
    let parser = NumberParserBuilder::new()
        .negative(true)
        .rational(true)
        .scientific(true)
        .build();

    assert!(
        parser.parse(c.input).into_result().is_ok(),
        "failed to parse {}",
        c.input
    );
}
