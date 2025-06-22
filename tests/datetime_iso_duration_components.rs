use bon::Builder;
use chumsky_helpers::datetime::parse_iso_duration;
use rstest::rstest;

#[derive(Debug, Builder)]
struct IsoCase {
    input: &'static str,
    years: Option<i32>,
    months: Option<i32>,
    days: Option<i32>,
    hours: Option<i32>,
    minutes: Option<i32>,
    seconds: Option<f64>,
}

#[rstest]
#[case(IsoCase::builder().input("P1Y").years(1).build())]
#[case(IsoCase::builder().input("P1M").months(1).build())]
#[case(IsoCase::builder().input("P1D").days(1).build())]
#[case(IsoCase::builder().input("PT1H").hours(1).build())]
#[case(IsoCase::builder().input("PT1M").minutes(1).build())]
#[case(IsoCase::builder().input("PT1S").seconds(1.0).build())]
fn iso_duration_single_component(#[case] c: IsoCase) {
    let parsed = parse_iso_duration(c.input).unwrap();
    assert_eq!(parsed.years, c.years);
    assert_eq!(parsed.months, c.months);
    assert_eq!(parsed.days, c.days);
    assert_eq!(parsed.hours, c.hours);
    assert_eq!(parsed.minutes, c.minutes);
    assert_eq!(parsed.seconds, c.seconds);
}
