use chumsky_helpers::datetime::parse_iso_duration;
use rstest::rstest;

#[derive(Debug)]
struct IsoCase {
    input: &'static str,
    years: Option<i32>,
    months: Option<i32>,
    days: Option<i32>,
    hours: Option<i32>,
    minutes: Option<i32>,
    seconds: Option<f64>,
}

impl IsoCase {
    const fn y(input: &'static str, y: i32) -> Self {
        Self {
            input,
            years: Some(y),
            months: None,
            days: None,
            hours: None,
            minutes: None,
            seconds: None,
        }
    }
    const fn m(input: &'static str, m: i32) -> Self {
        Self {
            input,
            years: None,
            months: Some(m),
            days: None,
            hours: None,
            minutes: None,
            seconds: None,
        }
    }
    const fn d(input: &'static str, d: i32) -> Self {
        Self {
            input,
            years: None,
            months: None,
            days: Some(d),
            hours: None,
            minutes: None,
            seconds: None,
        }
    }
    const fn h(input: &'static str, h: i32) -> Self {
        Self {
            input,
            years: None,
            months: None,
            days: None,
            hours: Some(h),
            minutes: None,
            seconds: None,
        }
    }
    const fn min(input: &'static str, m: i32) -> Self {
        Self {
            input,
            years: None,
            months: None,
            days: None,
            hours: None,
            minutes: Some(m),
            seconds: None,
        }
    }
    const fn s(input: &'static str, s: f64) -> Self {
        Self {
            input,
            years: None,
            months: None,
            days: None,
            hours: None,
            minutes: None,
            seconds: Some(s),
        }
    }
}

#[rstest]
#[case(IsoCase::y("P1Y", 1))]
#[case(IsoCase::m("P1M", 1))]
#[case(IsoCase::d("P1D", 1))]
#[case(IsoCase::h("PT1H", 1))]
#[case(IsoCase::min("PT1M", 1))]
#[case(IsoCase::s("PT1S", 1.0))]
fn iso_duration_single_component(#[case] c: IsoCase) {
    let parsed = parse_iso_duration(c.input).unwrap();
    assert_eq!(parsed.years, c.years);
    assert_eq!(parsed.months, c.months);
    assert_eq!(parsed.days, c.days);
    assert_eq!(parsed.hours, c.hours);
    assert_eq!(parsed.minutes, c.minutes);
    assert_eq!(parsed.seconds, c.seconds);
}
