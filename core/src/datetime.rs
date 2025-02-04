// Copyright 2025 Asim Ihsan
//
// This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
// If a copy of the MPL was not distributed with this file, You can obtain one at https://mozilla.org/MPL/2.0/.
//
// SPDX-License-Identifier: MPL-2.0

use chumsky::prelude::*;
use std::convert::TryFrom;
use time::{Date, Month};

// A simple digit parser
fn digit() -> impl Parser<char, char, Error = Simple<char>> {
    filter(|c: &char| c.is_ascii_digit())
}

// Parser for one or more digits
fn number(digits: usize) -> impl Parser<char, String, Error = Simple<char>> {
    digit().repeated().exactly(digits).collect::<String>()
}

fn any_number() -> impl Parser<char, String, Error = Simple<char>> {
    digit().repeated().at_least(1).collect::<String>()
}

// Parser for a decimal number (integer and optional fractional part)
fn decimal_number() -> impl Parser<char, f64, Error = Simple<char>> {
    let int_part = digit().repeated().at_least(1).collect::<String>();
    let frac_part =
        just('.').ignore_then(digit().repeated().at_least(1).collect::<String>()).or_not();
    int_part.then(frac_part).try_map(|(i, frac), span| {
        let num_str = if let Some(frac) = frac {
            format!("{}.{}", i, frac)
        } else {
            i
        };
        num_str.parse::<f64>().map_err(|_| Simple::custom(span, "Invalid number"))
    })
}

pub fn iso_date_parser() -> impl Parser<char, Date, Error = Simple<char>> {
    // Basic: YYYYMMDD
    let basic = number(8).try_map(|s: String, span| {
        let year =
            s[0..4].parse::<i32>().map_err(|_| Simple::custom(span.clone(), "Invalid year"))?;
        let month: u8 =
            s[4..6].parse().map_err(|_| Simple::custom(span.clone(), "Invalid month"))?;
        let day: u8 = s[6..8].parse().map_err(|_| Simple::custom(span.clone(), "Invalid day"))?;
        Ok((year, month, day))
    });

    // Extended: YYYY-MM-DD
    let extended = number(4)
        .then_ignore(just('-'))
        .then(number(2))
        .then_ignore(just('-'))
        .then(number(2))
        .try_map(|((year_str, month_str), day_str), span| {
            let year = year_str
                .parse::<i32>()
                .map_err(|_| Simple::custom(span.clone(), "Invalid year"))?;
            let month: u8 =
                month_str.parse().map_err(|_| Simple::custom(span.clone(), "Invalid month"))?;
            let day: u8 =
                day_str.parse().map_err(|_| Simple::custom(span.clone(), "Invalid day"))?;
            Ok((year, month, day))
        });

    basic.or(extended).map(|(year, month, day)| {
        let m = Month::try_from(month).expect("Invalid month value");
        Date::from_calendar_date(year, m, day).expect("Invalid date")
    })
}

#[derive(Debug, Clone, PartialEq)]
pub struct IsoDuration {
    pub years: Option<i32>,
    pub months: Option<i32>,
    pub days: Option<i32>,
    pub hours: Option<i32>,
    pub minutes: Option<i32>,
    pub seconds: Option<f64>,
}

pub fn iso_duration_parser() -> impl Parser<char, IsoDuration, Error = Simple<char>> {
    // Parser for an integer value
    let int_val = any_number()
        .try_map(|s, span| s.parse::<i32>().map_err(|_| Simple::custom(span, "Invalid integer")))
        .boxed();

    // Define each component
    let year_part = int_val.clone().then_ignore(just('Y')).map(Some);
    let month_part = int_val.clone().then_ignore(just('M')).map(Some);
    let day_part = int_val.clone().then_ignore(just('D')).map(Some);

    let hour_part = int_val.clone().then_ignore(just('H')).map(Some);
    let minute_part = int_val.clone().then_ignore(just('M')).map(Some);
    let second_part = decimal_number().then_ignore(just('S')).map(Some);

    // Date period is zero or more of the date parts
    let date_period = year_part.or_not().then(month_part.or_not()).then(day_part.or_not());

    // Time period is optional and must be preceded by 'T'
    let time_period = just('T')
        .ignore_then(hour_part.or_not().then(minute_part.or_not()).then(second_part.or_not()));

    just('P').ignore_then(date_period.then(time_period.or_not())).map(|(((y, m), d), t_opt)| {
        let (years, months, days) = (y.flatten(), m.flatten(), d.flatten());
        // If a time part was provided, deconstruct it; otherwise all are None
        let (hours, minutes, seconds) = if let Some(((ho, mi), se)) = t_opt {
            (ho.flatten(), mi.flatten(), se.flatten())
        } else {
            (None, None, None)
        };
        IsoDuration { years, months, days, hours, minutes, seconds }
    })
}

#[derive(Debug, Clone, PartialEq)]
pub struct GoDuration {
    pub nanos: i64,
}

pub fn go_duration_parser() -> impl Parser<char, GoDuration, Error = Simple<char>> {
    // Order matters: longer literal units first
    let unit = choice((
        just("ns").to(1),
        just("µs").to(1_000),
        just("ms").to(1_000_000),
        just("s").to(1_000_000_000),
        just("m").to(60_i64 * 1_000_000_000_i64),
        just("h").to(3600_i64 * 1_000_000_000_i64),
    ));

    let component = decimal_number().then(unit).map(|(num, mult)| (num * mult as f64) as i64);

    component.repeated().at_least(1).map(|parts| GoDuration { nanos: parts.into_iter().sum() })
}

pub fn parse_iso_date(input: &str) -> Result<Date, Vec<Simple<char>>> {
    iso_date_parser().parse(input)
}

pub fn parse_iso_duration(input: &str) -> Result<IsoDuration, Vec<Simple<char>>> {
    iso_duration_parser().parse(input)
}

pub fn parse_go_duration(input: &str) -> Result<GoDuration, Vec<Simple<char>>> {
    go_duration_parser().parse(input)
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    use time::Month;

    #[test]
    fn test_iso_date_basic() {
        let input = "20240204";
        let parsed = parse_iso_date(input).unwrap();
        assert_eq!(parsed.year(), 2024);
        assert_eq!(parsed.month(), Month::February);
        assert_eq!(parsed.day(), 4);
    }

    #[test]
    fn test_iso_date_extended() {
        let input = "2024-02-04";
        let parsed = parse_iso_date(input).unwrap();
        assert_eq!(parsed.year(), 2024);
        assert_eq!(parsed.month(), Month::February);
        assert_eq!(parsed.day(), 4);
    }

    #[test]
    fn test_iso_duration() {
        let input = "P1Y2M3DT4H5M6.789S";
        let parsed = parse_iso_duration(input).unwrap();
        assert_eq!(parsed.years, Some(1));
        assert_eq!(parsed.months, Some(2));
        assert_eq!(parsed.days, Some(3));
        assert_eq!(parsed.hours, Some(4));
        assert_eq!(parsed.minutes, Some(5));
        assert_eq!(parsed.seconds, Some(6.789));
    }

    #[test]
    fn test_go_duration() {
        let input = "2h3m4s";
        let parsed = parse_go_duration(input).unwrap();
        let expected = 2 * 3600 * 1_000_000_000 + 3 * 60 * 1_000_000_000 + 4 * 1_000_000_000;
        assert_eq!(parsed.nanos, expected);
    }

    #[test]
    fn test_iso_duration_date_only() {
        let input = "P1Y2M3D";
        let parsed = parse_iso_duration(input).unwrap();
        assert_eq!(parsed.years, Some(1));
        assert_eq!(parsed.months, Some(2));
        assert_eq!(parsed.days, Some(3));
        assert_eq!(parsed.hours, None);
        assert_eq!(parsed.minutes, None);
        assert_eq!(parsed.seconds, None);
    }

    proptest! {
        #[test]
        fn prop_iso_date_basic(year in 1970i32..=2100i32, month in 1u8..=12, day in 1u8..=31) {
            // Only test if the generated values form a valid date.
            if let Ok(date) = time::Date::from_calendar_date(year, time::Month::try_from(month).unwrap(), day) {
                let input = format!("{:04}{:02}{:02}", year, month, day);
                let parsed = parse_iso_date(&input).unwrap();
                prop_assert_eq!(parsed, date);
            }
        }
    }

    proptest! {
        #[test]
        fn prop_iso_date_extended(year in 1970i32..=2100i32, month in 1u8..=12, day in 1u8..=31) {
            if let Ok(date) = time::Date::from_calendar_date(year, time::Month::try_from(month).unwrap(), day) {
                let input = format!("{:04}-{:02}-{:02}", year, month, day);
                let parsed = parse_iso_date(&input).unwrap();
                prop_assert_eq!(parsed, date);
            }
        }
    }

    proptest! {
        #[test]
        fn prop_iso_duration(
            year in 0i32..=20,
            month in 0i32..=20,
            day in 0i32..=31,
            hour in 0i32..=23,
            minute in 0i32..=59,
            second in 0.0f64..60.0
        ) {
            // Build the ISO duration string conditionally.
            let mut input = String::from("P");
            if year != 0 { input.push_str(&format!("{}Y", year)); }
            if month != 0 { input.push_str(&format!("{}M", month)); }
            if day != 0 { input.push_str(&format!("{}D", day)); }
            if hour != 0 || minute != 0 || (second - 0.0).abs() > f64::EPSILON {
                input.push('T');
                if hour != 0 { input.push_str(&format!("{}H", hour)); }
                if minute != 0 { input.push_str(&format!("{}M", minute)); }
                if (second - 0.0).abs() > f64::EPSILON { input.push_str(&format!("{}S", second)); }
            }
            let parsed = parse_iso_duration(&input).unwrap();
            prop_assert_eq!(parsed.years, if year != 0 { Some(year) } else { None });
            prop_assert_eq!(parsed.months, if month != 0 { Some(month) } else { None });
            prop_assert_eq!(parsed.days, if day != 0 { Some(day) } else { None });
            prop_assert_eq!(parsed.hours, if hour != 0 { Some(hour) } else { None });
            prop_assert_eq!(parsed.minutes, if minute != 0 { Some(minute) } else { None });
            if (second - 0.0).abs() > f64::EPSILON {
                prop_assert_eq!(parsed.seconds, Some(second));
            } else {
                prop_assert_eq!(parsed.seconds, None);
            }
        }
    }

    proptest! {
        #[test]
        fn prop_go_duration(
            components in proptest::collection::vec(
                (0.1f64..100.0, prop_oneof!["ns", "µs", "ms", "s", "m", "h"]),
                1..10
            )
        ) {
            let mut input = String::new();
            let mut expected: i64 = 0;
            for (num, unit) in components {
                input.push_str(&format!("{}{}", num, unit));
                let multiplier = match unit.as_str() {
                    "ns" => 1,
                    "µs" => 1_000,
                    "ms" => 1_000_000,
                    "s"  => 1_000_000_000,
                    "m"  => 60 * 1_000_000_000_i64,
                    "h"  => 3600 * 1_000_000_000_i64,
                    _ => unreachable!(),
                };
                expected += (num * multiplier as f64) as i64;
            }
            let parsed = parse_go_duration(&input).unwrap();
            prop_assert_eq!(parsed.nanos, expected);
        }
    }
}
