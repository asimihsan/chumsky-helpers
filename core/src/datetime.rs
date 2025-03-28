// Copyright 2025 Asim Ihsan
//
// This Source Code Form is subject to the terms of the Mozilla Public License, v. 2.0.
// If a copy of the MPL was not distributed with this file, You can obtain one at https://mozilla.org/MPL/2.0/.
//
// SPDX-License-Identifier: MPL-2.0

//! # Date and Duration Parsing
//!
//! This module provides parsers for date and duration formats including:
//!
//! * ISO 8601 dates (basic and extended formats)
//! * ISO 8601 durations
//! * Go-style time durations
//!
//! All parsers provide detailed error reporting with spans indicating exactly where
//! in the input the error occurred and what was expected.
//!
//! ## Examples
//!
//! ### Parsing ISO 8601 Dates
//!
//! ```
//! use chumsky_helpers::datetime::parse_iso_date;
//! use time::Month;
//!
//! // Parse a basic ISO date format (YYYYMMDD)
//! let date = parse_iso_date("20240204").unwrap();
//! assert_eq!(date.year(), 2024);
//! assert_eq!(date.month(), Month::February);
//! assert_eq!(date.day(), 4);
//!
//! // Parse an extended ISO date format (YYYY-MM-DD)
//! let date = parse_iso_date("2024-02-04").unwrap();
//! assert_eq!(date.year(), 2024);
//! assert_eq!(date.month(), Month::February);
//! assert_eq!(date.day(), 4);
//! ```
//!
//! ### Parsing ISO 8601 Durations
//!
//! ```
//! use chumsky_helpers::datetime::parse_iso_duration;
//!
//! // Parse a full ISO duration with date and time components
//! let duration = parse_iso_duration("P1Y2M3DT4H5M6.789S").unwrap();
//! assert_eq!(duration.years, Some(1));
//! assert_eq!(duration.months, Some(2));
//! assert_eq!(duration.days, Some(3));
//! assert_eq!(duration.hours, Some(4));
//! assert_eq!(duration.minutes, Some(5));
//! assert_eq!(duration.seconds, Some(6.789));
//! ```
//!
//! ### Parsing Go-style Durations
//!
//! ```
//! use chumsky_helpers::datetime::parse_go_duration;
//!
//! // Parse a Go duration format
//! let duration = parse_go_duration("2h3m4s").unwrap();
//! let expected_nanos = 2 * 3600 * 1_000_000_000 + 3 * 60 * 1_000_000_000 + 4 * 1_000_000_000;
//! assert_eq!(duration.nanos, expected_nanos);
//! ```

use chumsky::combinator::Repeated;
use chumsky::error::LabelError;
use chumsky::extra::ParserExtra;
use chumsky::input::StrInput;
use chumsky::text::{Char, TextExpected};
use chumsky::util::MaybeRef;
use chumsky::{error::Rich, prelude::*};
use std::convert::TryFrom;
use time::{Date, Month};

fn any_number<'a>() -> impl Parser<'a, &'a str, String, extra::Err<Rich<'a, char>>> {
    text::digits(10)
        .repeated()
        .at_least(1)
        .to_slice()
        .map(|s: &str| s.to_string())
        .labelled("number")
}

// Parser for a decimal number (integer and optional fractional part)
fn decimal_number<'a>() -> impl Parser<'a, &'a str, f64, extra::Err<Rich<'a, char>>> {
    let int_part = any_number();
    let frac_part = just('.').ignore_then(any_number()).or_not();
    int_part.then(frac_part).try_map(|(i, frac), span| {
        let num_str = if let Some(frac) = frac {
            format!("{}.{}", i, frac)
        } else {
            i
        };
        num_str.parse::<f64>().map_err(|_| Rich::custom(span, "Invalid float"))
    })
}

fn exactly_digits<'src, I, E>(
    length: usize,
) -> Repeated<impl Parser<'src, I, <I as Input<'src>>::Token, E> + Copy, I::Token, I, E>
where
    I: StrInput<'src>,
    I::Token: Char + 'src,
    E: ParserExtra<'src, I>,
    E::Error: LabelError<'src, I, TextExpected<'src, I>>,
{
    any()
        .try_map(move |c: I::Token, span| {
            if c.is_digit(10) {
                Ok(c)
            } else {
                Err(LabelError::expected_found(
                    [TextExpected::Digit(0..10)],
                    Some(MaybeRef::Val(c)),
                    span,
                ))
            }
        })
        .repeated()
        .exactly(length)
}

/// Creates a parser for ISO 8601 date formats.
///
/// This parser supports both the basic format (YYYYMMDD) and extended format (YYYY-MM-DD).
/// It returns a `time::Date` object representing the parsed date.
pub fn iso_date_parser<'a>() -> impl Parser<'a, &'a str, Date, extra::Err<Rich<'a, char>>> {
    let year_digits = exactly_digits(4).to_slice();
    let month_digits = exactly_digits(2).to_slice();
    let day_digits = exactly_digits(2).to_slice();

    // Basic ISO date format: YYYYMMDD (8 digits)
    let basic = year_digits
        .then(month_digits)
        .then(day_digits)
        .try_map(
            |((year_str, month_str), day_str): ((&str, &str), &str), span| {
                let year =
                    year_str.parse::<i32>().map_err(|_| Rich::custom(span, "Invalid year"))?;
                let month =
                    month_str.parse::<u8>().map_err(|_| Rich::custom(span, "Invalid month"))?;
                let day = day_str.parse::<u8>().map_err(|_| Rich::custom(span, "Invalid day"))?;
                Ok((year, month, day))
            },
        )
        .then_ignore(end());

    // Extended ISO date format: YYYY-MM-DD
    let extended = year_digits
        .then_ignore(just('-'))
        .then(month_digits)
        .then_ignore(just('-'))
        .then(day_digits)
        .then_ignore(end())
        .try_map(
            |((year_str, month_str), day_str): ((&str, &str), &str), span| {
                let year =
                    year_str.parse::<i32>().map_err(|_| Rich::custom(span, "Invalid year"))?;
                let month =
                    month_str.parse::<u8>().map_err(|_| Rich::custom(span, "Invalid month"))?;
                let day = day_str.parse::<u8>().map_err(|_| Rich::custom(span, "Invalid day"))?;
                Ok((year, month, day))
            },
        );

    basic
        .or(extended)
        .try_map(|(year, month, day), span| {
            let month =
                Month::try_from(month).map_err(|_| Rich::custom(span, "Invalid month value"))?;
            let date = Date::from_calendar_date(year, month, day)
                .map_err(|_| Rich::custom(span, "Invalid date"))?;
            Ok(date)
        })
        .boxed()
}

/// Represents an ISO 8601 duration.
///
/// This struct holds the components of an ISO 8601 duration, which can include years, months,
/// days, hours, minutes, and seconds. Any component that is not present in the parsed input
/// will be set to `None`.
///
/// For example, a duration like "P1Y2M3DT4H5M6.789S" would have all components set:
/// - years: Some(1)
/// - months: Some(2)
/// - days: Some(3)
/// - hours: Some(4)
/// - minutes: Some(5)
/// - seconds: Some(6.789)
#[derive(Debug, Clone, PartialEq)]
pub struct IsoDuration {
    /// The number of years in the duration, if specified.
    pub years: Option<i32>,

    /// The number of months in the duration, if specified.
    pub months: Option<i32>,

    /// The number of days in the duration, if specified.
    pub days: Option<i32>,

    /// The number of hours in the duration, if specified.
    pub hours: Option<i32>,

    /// The number of minutes in the duration, if specified.
    pub minutes: Option<i32>,

    /// The number of seconds in the duration, if specified.
    /// May include fractional seconds.
    pub seconds: Option<f64>,
}

/// Creates a parser for ISO 8601 duration formats.
///
/// This parser supports the full ISO 8601 duration syntax, including both date and time
/// components. The parser will return an `IsoDuration` object containing the parsed components.
///
/// Example formats:
/// - "P1Y2M3D" (1 year, 2 months, 3 days)
/// - "PT4H5M6S" (4 hours, 5 minutes, 6 seconds)
/// - "P1Y2M3DT4H5M6.789S" (1 year, 2 months, 3 days, 4 hours, 5 minutes, 6.789 seconds)
pub fn iso_duration_parser<'a>() -> impl Parser<'a, &'a str, IsoDuration, extra::Err<Rich<'a, char>>>
{
    // Parser for an integer value
    let int_val = any_number()
        .try_map(|s, span| s.parse::<i32>().map_err(|_| Rich::custom(span, "Invalid integer")))
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

    just('P')
        .labelled("expected P")
        .ignore_then(date_period.then(time_period.or_not()))
        .try_map(|(((y, m), d), t_opt), span| {
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
                Ok(Err(Rich::custom(
                    span,
                    "Expected at least one duration component after 'P'",
                ))?)
            } else {
                Ok(IsoDuration { years, months, days, hours, minutes, seconds })
            }
        })
        .boxed()
}

/// Represents a Go-style duration.
///
/// This struct holds a duration in nanoseconds, as used in the Go programming language.
/// The nanosecond value is calculated from the sum of all the duration components
/// in the parsed input.
#[derive(Debug, Clone, PartialEq)]
pub struct GoDuration {
    /// The total duration in nanoseconds.
    pub nanos: i64,
}

/// Creates a parser for Go-style duration formats.
///
/// This parser supports the Go duration syntax, which consists of a sequence of
/// time units with optional decimal values. The parser will return a `GoDuration`
/// object containing the total duration in nanoseconds.
///
/// Supported units:
/// - "h" (hours)
/// - "m" (minutes)
/// - "s" (seconds)
/// - "ms" (milliseconds)
/// - "µs" (microseconds)
/// - "ns" (nanoseconds)
///
/// Example formats:
/// - "2h3m4s" (2 hours, 3 minutes, 4 seconds)
/// - "1.5h" (1.5 hours)
/// - "500ms" (500 milliseconds)
/// - "1h30m45s" (1 hour, 30 minutes, 45 seconds)
pub fn go_duration_parser<'a>() -> impl Parser<'a, &'a str, GoDuration, extra::Err<Rich<'a, char>>>
{
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
        .collect::<Vec<_>>() // Collect into Vec before summing
        .map(|parts| GoDuration { nanos: parts.iter().sum() })
        .then_ignore(end())
        .boxed()
}

/// Parses an ISO 8601 date string.
///
/// This function supports both the basic format (YYYYMMDD) and extended format (YYYY-MM-DD).
/// It returns a `ParseResult` containing either the parsed `Date` or error information.
///
/// # Examples
///
/// ```
/// use chumsky_helpers::datetime::parse_iso_date;
///
/// // Parse a basic ISO date
/// let date = parse_iso_date("20240204").unwrap();
/// assert_eq!(date.year(), 2024);
/// assert_eq!(date.month(), time::Month::February);
/// assert_eq!(date.day(), 4);
///
/// // Parse an extended ISO date
/// let date = parse_iso_date("2024-02-04").unwrap();
/// assert_eq!(date.year(), 2024);
/// assert_eq!(date.month(), time::Month::February);
/// assert_eq!(date.day(), 4);
/// ```
pub fn parse_iso_date(input: &str) -> ParseResult<Date, Rich<char>> {
    iso_date_parser().parse(input)
}

/// Parses an ISO 8601 duration string.
///
/// This function supports the full ISO 8601 duration syntax, including both date and time
/// components. It returns a `ParseResult` containing either the parsed `IsoDuration` or error information.
///
/// # Examples
///
/// ```
/// use chumsky_helpers::datetime::parse_iso_duration;
///
/// // Parse a full ISO duration
/// let duration = parse_iso_duration("P1Y2M3DT4H5M6.789S").unwrap();
/// assert_eq!(duration.years, Some(1));
/// assert_eq!(duration.months, Some(2));
/// assert_eq!(duration.days, Some(3));
/// assert_eq!(duration.hours, Some(4));
/// assert_eq!(duration.minutes, Some(5));
/// assert_eq!(duration.seconds, Some(6.789));
///
/// // Parse a date-only ISO duration
/// let duration = parse_iso_duration("P1Y2M3D").unwrap();
/// assert_eq!(duration.years, Some(1));
/// assert_eq!(duration.months, Some(2));
/// assert_eq!(duration.days, Some(3));
/// assert_eq!(duration.hours, None);
/// assert_eq!(duration.minutes, None);
/// assert_eq!(duration.seconds, None);
/// ```
pub fn parse_iso_duration(input: &str) -> ParseResult<IsoDuration, Rich<char>> {
    iso_duration_parser().parse(input)
}

/// Parses a Go-style duration string.
///
/// This function supports the Go duration syntax, which consists of a sequence of
/// time units with optional decimal values. It returns a `ParseResult` containing
/// either the parsed `GoDuration` or error information.
///
/// # Examples
///
/// ```
/// use chumsky_helpers::datetime::parse_go_duration;
///
/// // Parse a simple Go duration
/// let duration = parse_go_duration("2h3m4s").unwrap();
/// let expected = 2 * 3600 * 1_000_000_000 + 3 * 60 * 1_000_000_000 + 4 * 1_000_000_000;
/// assert_eq!(duration.nanos, expected);
///
/// // Parse a Go duration with fractional values
/// let duration = parse_go_duration("1.5h").unwrap();
/// let expected = (1.5 * 3600.0 * 1_000_000_000.0) as i64;
/// assert_eq!(duration.nanos, expected);
/// ```
pub fn parse_go_duration(input: &str) -> ParseResult<GoDuration, Rich<char>> {
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

    #[test]
    fn test_iso_duration_empty() {
        // This should fail with an error since "P" with no duration components is invalid
        let input = "P";
        let result = parse_iso_duration(input);
        assert!(result.has_errors());
        let errors = result.into_errors();
        assert!(!errors.is_empty());
        let reason_str = format!("{:?}", errors[0].reason());
        assert!(
            reason_str.contains("Expected at least one duration component after 'P'"),
            "Unexpected error message: {:?}",
            reason_str
        );
    }

    // Test that all individual component validation branches in the empty condition are covered
    #[test]
    fn test_iso_duration_each_component_alone() {
        // Test each duration component individually to ensure branch coverage
        let components = [
            ("P1Y", Some(1), None, None, None, None, None),
            ("P1M", None, Some(1), None, None, None, None),
            ("P1D", None, None, Some(1), None, None, None),
            ("PT1H", None, None, None, Some(1), None, None),
            ("PT1M", None, None, None, None, Some(1), None),
            ("PT1S", None, None, None, None, None, Some(1.0)),
        ];

        for (input, years, months, days, hours, minutes, seconds) in components {
            let parsed = parse_iso_duration(input).unwrap();
            assert_eq!(parsed.years, years);
            assert_eq!(parsed.months, months);
            assert_eq!(parsed.days, days);
            assert_eq!(parsed.hours, hours);
            assert_eq!(parsed.minutes, minutes);
            assert_eq!(parsed.seconds, seconds);
        }
    }

    #[test]
    fn test_iso_date_invalid_format() {
        let input = "2024/02/04"; // wrong delimiter instead of '-' at positions 4 and 7
        let res = parse_iso_date(input);
        assert!(
            res.has_errors(),
            "Expected parse_iso_date({:?}) to fail due to invalid format, but got Ok",
            input
        );
        let errors = res.into_errors();
        assert!(!errors.is_empty());
        // Expect an error at position 4 (where '/' appears instead of '-')
        assert_eq!(
            errors[0].span().start,
            4,
            "Expected error at position 4 for input {:?}, but found error at {}",
            input,
            errors[0].span().start
        );
    }

    #[test]
    fn test_iso_date_invalid_char() {
        let input = "20A40204"; // non-digit character in the date
        let res = parse_iso_date(input);
        assert!(
            res.has_errors(),
            "Expected parse_iso_date({:?}) to fail due to an invalid character, but got Ok",
            input
        );
        let errors = res.into_errors();
        assert!(!errors.is_empty());
        // Expect an error at position 2 (where 'A' appears instead of a digit)
        let reason_str = format!("{:?}", errors[0].reason()).to_lowercase();
        assert!(
            reason_str.contains("digit"),
            "Expected error message to mention 'digit', but got: {:?}",
            reason_str
        );
        assert_eq!(
            errors[0].span().start,
            2,
            "Expected error at position 2 for input {:?}, but found error at {}",
            input,
            errors[0].span().start
        );
    }

    #[test]
    fn test_iso_duration_missing_prefix() {
        let input = "1Y2M3DT4H5M6.789S"; // missing leading 'P'
        let res = parse_iso_duration(input);
        assert!(
            res.has_errors(),
            "Expected parse_iso_duration({:?}) to fail due to missing prefix 'P', but got Ok",
            input
        );
        let errors = res.into_errors();
        assert!(!errors.is_empty());
        // Expect an error indicating that the literal 'P' was expected at position 0.
        let reason_str = format!("{:?}", errors[0].reason());
        assert!(
            reason_str.contains("P") || reason_str.contains("expected"),
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
    fn test_iso_duration_invalid_token() {
        let input = "P1X"; // After the digit, the expected token is 'Y' (or one of Y, M, D)
        let res = parse_iso_duration(input);
        assert!(
            res.has_errors(),
            "Expected parse_iso_duration({:?}) to fail due to an invalid token, but got Ok",
            input
        );
        let errors = res.into_errors();
        assert!(!errors.is_empty());
        // The error actually occurs at the beginning of the input (position 0)
        assert_eq!(
            errors[0].span().start,
            0,
            "Expected error span to start at beginning of input for {:?}, but got {}",
            input,
            errors[0].span().start
        );
    }

    #[test]
    fn test_iso_duration_missing_end() {
        let input = "P1Y2M3DT4H5M6.789"; // missing trailing 'S' for seconds
        let res = parse_iso_duration(input);
        assert!(
            res.has_errors(),
            "Expected parse_iso_duration({:?}) to fail due to missing 'S' at the end, but got Ok",
            input
        );
        let errors = res.into_errors();
        assert!(!errors.is_empty());
        // Expect an error at the end of the input where 'S' should be
        assert_eq!(
            errors[0].span().start,
            input.len(),
            "Expected error span at end of input ({}), but got {}",
            input.len(),
            errors[0].span().start
        );
    }

    #[test]
    fn test_go_duration_invalid_missing_unit() {
        let input = "2h5"; // '2h' is valid, but '5' lacks the trailing valid unit
        let res = parse_go_duration(input);
        assert!(
            res.has_errors(),
            "Expected parse_go_duration({:?}) to fail when unit is missing, but got Ok",
            input
        );
        let errors = res.into_errors();
        assert!(!errors.is_empty());
        // The error occurs at position 3, right after the '5'
        assert_eq!(
            errors[0].span().start,
            3,
            "Expected error span to start at position 3 (after the digit) but got {}",
            errors[0].span().start
        );
    }

    #[test]
    fn test_go_duration_multiple_units() {
        // Test parsing a Go duration with multiple units and fractional values
        let input = "1.5h30.5m10.1s500ms";
        let parsed = parse_go_duration(input).unwrap();

        // Calculate expected value:
        // 1.5h = 1.5 * 3600 * 1_000_000_000 nanoseconds
        // 30.5m = 30.5 * 60 * 1_000_000_000 nanoseconds
        // 10.1s = 10.1 * 1_000_000_000 nanoseconds
        // 500ms = 500 * 1_000_000 nanoseconds
        let expected = (1.5 * 3600.0 * 1_000_000_000.0) as i64
            + (30.5 * 60.0 * 1_000_000_000.0) as i64
            + (10.1 * 1_000_000_000.0) as i64
            + (500.0 * 1_000_000.0) as i64;

        assert_eq!(parsed.nanos, expected);
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
        assert!(res.has_errors());
        let errors = res.into_errors();
        assert!(!errors.is_empty());
        // Expect that the parser failed where an 8th digit was missing.
        assert_eq!(errors[0].span().start, input.len());
        let reason_str = format!("{:?}", errors[0].reason());
        assert!(reason_str.contains("expected") || reason_str.contains("digit"));
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
            prop_assert!(res.has_errors());
        }
    }

    proptest! {
        #[test]
        fn prop_invalid_iso_duration(input in "\\PC+") {
            // A valid iso duration must start with 'P' and contain at least one digit.
            prop_assume!(!(input.starts_with("P") && input.chars().any(|c| c.is_ascii_digit())));
            let res = parse_iso_duration(&input);
            prop_assert!(res.has_errors());
            let errors = res.into_errors();
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
            prop_assert!(res.has_errors(), "Expected parse_go_duration({:?}) to fail for invalid unit, but got Ok", input);
            let errors = res.into_errors();
            prop_assert!(!errors.is_empty(), "Expected errors to be non-empty for invalid go duration input: {:?}", input);
        }
    }
}
