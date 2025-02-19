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
    filter(|c: &char| c.is_ascii_digit()).labelled("digit")
}

// Parser for one or more digits
fn number(digits: usize) -> impl Parser<char, String, Error = Simple<char>> {
    digit().repeated().exactly(digits).collect::<String>().labelled("digit")
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
        .then_ignore(just('-').labelled("expected '-'"))
        .then(number(2))
        .then_ignore(just('-').labelled("expected '-'"))
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
    let year_part = int_val.clone().then_ignore(just('Y').labelled("expected 'Y'")).map(Some);
    let month_part = int_val.clone().then_ignore(just('M').labelled("expected 'M'")).map(Some);
    let day_part = int_val.clone().then_ignore(just('D').labelled("expected 'D'")).map(Some);

    let hour_part = int_val.clone().then_ignore(just('H').labelled("expected 'H'")).map(Some);
    let minute_part = int_val.clone().then_ignore(just('M').labelled("expected 'M'")).map(Some);
    let second_part = decimal_number().then_ignore(just('S').labelled("expected 'S'")).map(Some);

    // Date period is zero or more of the date parts
    let date_period = year_part.or_not().then(month_part.or_not()).then(day_part.or_not());

    // Time period is optional and must be preceded by 'T'
    let time_period = just('T')
        .ignore_then(hour_part.or_not().then(minute_part.or_not()).then(second_part.or_not()));

    just('P').labelled("expected P").ignore_then(date_period.then(time_period.or_not())).try_map(
        |(((y, m), d), t_opt), span| {
            let years = y.flatten();
            let months = m.flatten();
            let days = d.flatten();
            let (hours, minutes, seconds) = if let Some(((ho, mi), se)) = t_opt {
                (ho.flatten(), mi.flatten(), se.flatten())
            } else {
                (None, None, None)
            };
            if years.is_none()
                && months.is_none()
                && days.is_none()
                && hours.is_none()
                && minutes.is_none()
                && seconds.is_none()
            {
                Err(Simple::custom(
                    span,
                    "Expected at least one duration component after 'P'",
                ))
            } else {
                Ok(IsoDuration { years, months, days, hours, minutes, seconds })
            }
        },
    )
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

    let component = decimal_number()
        .then(unit.labelled("expected time unit"))
        .map(|(num, mult)| (num * mult as f64) as i64);

    component
        .repeated()
        .at_least(1)
        .then_ignore(end())
        .map(|parts| GoDuration { nanos: parts.into_iter().sum() })
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
            if let Ok(date) = Date::from_calendar_date(year, time::Month::try_from(month).unwrap(), day) {
                let input = format!("{:04}{:02}{:02}", year, month, day);
                let parsed = parse_iso_date(&input).unwrap();
                prop_assert_eq!(parsed, date);
            }
        }
    }

    proptest! {
        #[test]
        fn prop_iso_date_extended(year in 1970i32..=2100i32, month in 1u8..=12, day in 1u8..=31) {
            if let Ok(date) = Date::from_calendar_date(year, time::Month::try_from(month).unwrap(), day) {
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

    #[test]
    fn test_iso_date_invalid_length() {
        let input = "2024020"; // 7 digits instead of 8
        let res = parse_iso_date(input);
        assert!(res.is_err());
        let errors = res.unwrap_err();
        assert!(!errors.is_empty());
        // Expect that the parser failed where an 8th digit was missing.
        assert_eq!(errors[0].span().start, input.len());
        let reason_str = format!("{:?}", errors[0].reason());
        assert!(reason_str.contains("expected") || reason_str.contains("digit"));
    }

    #[test]
    #[ignore]
    fn test_iso_date_invalid_format() {
        let input = "2024/02/04"; // wrong delimiter instead of '-' at positions 4 and 7
        let res = parse_iso_date(input);
        assert!(
            res.is_err(),
            "Expected parse_iso_date({:?}) to fail due to invalid format, but got Ok",
            input
        );
        let errors = res.unwrap_err();
        assert!(!errors.is_empty());
        // Expect an error indicating that '-' was expected.
        let reason_str = format!("{:?}", errors[0].reason());
        assert!(
            reason_str.contains("-"),
            "Expected error message to mention '-' as delimiter, but got: {:?}",
            reason_str
        );
        // Check that the error span starts at the first unexpected character (here at index 4)
        assert_eq!(
            errors[0].span().start,
            4,
            "Expected error at position 4 for input {:?}, but found error at {}",
            input,
            errors[0].span().start
        );
    }

    #[test]
    #[ignore]
    fn test_iso_date_invalid_char() {
        let input = "20A40204"; // non-digit character in the date
        let res = parse_iso_date(input);
        assert!(
            res.is_err(),
            "Expected parse_iso_date({:?}) to fail due to an invalid character, but got Ok",
            input
        );
        let errors = res.unwrap_err();
        assert!(!errors.is_empty());
        // Expect an error message mentioning a digit (or "Invalid year"/"Invalid month"/"Invalid day")
        let reason_str = format!("{:?}", errors[0].reason()).to_lowercase();
        assert!(
            reason_str.contains("digit"),
            "Expected error message to mention 'digit', but got: {:?}",
            reason_str
        );
    }

    #[test]
    #[ignore]
    fn test_iso_duration_missing_prefix() {
        let input = "1Y2M3DT4H5M6.789S"; // missing leading 'P'
        let res = parse_iso_duration(input);
        assert!(
            res.is_err(),
            "Expected parse_iso_duration({:?}) to fail due to missing prefix 'P', but got Ok",
            input
        );
        let errors = res.unwrap_err();
        assert!(!errors.is_empty());
        // Expect an error indicating that the literal 'P' was expected at position 0.
        let reason_str = format!("{:?}", errors[0].reason());
        assert!(
            reason_str.contains("P"),
            "Expected error message to mention missing 'P' at the beginning, but got: {:?}",
            reason_str
        );
        assert_eq!(
            errors[0].span().start,
            0,
            "Expected error span to start at 0 for missing 'P', but got {}",
            errors[0].span().start
        );
    }

    #[test]
    #[ignore]
    fn test_iso_duration_invalid_token() {
        let input = "P1X"; // After the digit, the expected token is 'Y' (or one of Y, M, D)
        let res = parse_iso_duration(input);
        assert!(
            res.is_err(),
            "Expected parse_iso_duration({:?}) to fail due to an invalid token, but got Ok",
            input
        );
        let errors = res.unwrap_err();
        assert!(!errors.is_empty());
        // Expect an error mentioning the expected token (e.g. "Y")
        let reason_str = format!("{:?}", errors[0].reason());
        assert!(
            reason_str.contains("Y"),
            "Expected error message to mention 'Y' as the expected token, but got: {:?}",
            reason_str
        );
        // Check that the error span starts at where the unexpected 'X' is found.
        let pos = input.find('X').unwrap();
        assert_eq!(
            errors[0].span().start,
            pos,
            "Expected error span to start at {} for input {:?}, but got {}",
            pos,
            input,
            errors[0].span().start
        );
    }

    #[test]
    #[ignore]
    fn test_iso_duration_missing_end() {
        let input = "P1Y2M3DT4H5M6.789"; // missing trailing 'S' for seconds
        let res = parse_iso_duration(input);
        assert!(
            res.is_err(),
            "Expected parse_iso_duration({:?}) to fail due to missing 'S' at the end, but got Ok",
            input
        );
        let errors = res.unwrap_err();
        assert!(!errors.is_empty());
        // Expect an error mentioning that 'S' is missing.
        let reason_str = format!("{:?}", errors[0].reason());
        assert!(
            reason_str.contains("S"),
            "Expected error message to mention 'S' for seconds, but got: {:?}",
            reason_str
        );
        assert_eq!(
            errors[0].span().start,
            input.len(),
            "Expected error span at end of input ({}), but got {}",
            input.len(),
            errors[0].span().start
        );
    }

    #[test]
    #[ignore]
    fn test_go_duration_invalid_missing_unit() {
        let input = "2h5"; // '2h' is valid, but '5' lacks the trailing valid unit
        let res = parse_go_duration(input);
        assert!(
            res.is_err(),
            "Expected parse_go_duration({:?}) to fail when unit is missing, but got Ok",
            input
        );
        let errors = res.unwrap_err();
        assert!(!errors.is_empty());
        // Expect an error message regarding a missing unit marker.
        let reason_str = format!("{:?}", errors[0].reason());
        assert!(
            reason_str.contains("expected"),
            "Expected error message to contain 'expected', but got: {:?}",
            reason_str
        );
        let pos = input.find('5').unwrap();
        assert_eq!(
            errors[0].span().start,
            pos,
            "Expected error span to start at {} (position of missing unit) but got {}",
            pos,
            errors[0].span().start
        );
    }

    proptest! {
        #[test]
        fn prop_invalid_iso_date(input in "\\PC+") {
            // Exclude valid basic (8 digits) and extended (YYYY-MM-DD) formats.
            prop_assume!(!(input.len() == 8 && input.chars().all(|c| c.is_ascii_digit())));
            prop_assume!(!(input.len() == 10 &&
                input.chars().nth(4) == Some('-') &&
                input.chars().nth(7) == Some('-') &&
                input.chars().enumerate().all(|(i, c)| {
                    if i == 4 || i == 7 { c == '-' } else { c.is_ascii_digit() }
                })));
            let res = parse_iso_date(&input);
            prop_assert!(res.is_err());
        }
    }

    proptest! {
        #[test]
        fn prop_invalid_iso_duration(input in "\\PC+") {
            // A valid iso duration must start with 'P' and contain at least one digit.
            prop_assume!(!(input.starts_with("P") && input.chars().any(|c| c.is_ascii_digit())));
            let res = parse_iso_duration(&input);
            prop_assert!(res.is_err());
            let errors = res.unwrap_err();
            prop_assert!(!errors.is_empty());
        }
    }

    proptest! {
        #[test]
        fn prop_invalid_go_duration(num in 0.1f64..100.0, unit in "[a-zA-Z]{1,3}") {
            let valid_units = ["ns", "µs", "ms", "s", "m", "h"];
            prop_assume!(!valid_units.contains(&unit.as_str()));
            let input = format!("{}{}", num, unit);
            let res = parse_go_duration(&input);
            prop_assert!(res.is_err(), "Expected parse_go_duration({:?}) to fail for invalid unit, but got Ok", input);
            let errors = res.unwrap_err();
            prop_assert!(!errors.is_empty(), "Expected errors to be non-empty for invalid go duration input: {:?}", input);
        }
    }
}
