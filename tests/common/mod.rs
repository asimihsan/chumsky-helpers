use chumsky_helpers::number::ExplicitSign;

/// Assert that the `display` string begins with the correct sign corresponding
/// to `expected_sign`.
#[allow(dead_code)]
pub fn assert_display_sign(display: &str, expected_sign: ExplicitSign) {
    match expected_sign {
        ExplicitSign::Positive => assert!(display.starts_with('+')),
        ExplicitSign::Negative => assert!(display.starts_with('-')),
        ExplicitSign::None => assert!(!display.starts_with('+') && !display.starts_with('-')),
    }
}

// -------------------------------------------------------------------------------------------------
// Macro helpers used by many test modules so we keep them in a common place.
// -------------------------------------------------------------------------------------------------

/// Assert that a parser successfully parses `src` and yields `want`.
///
/// Example:
/// ```
/// assert_parses_to!(raw_single_line(), "\"abc\"", "abc");
/// ```
#[macro_export]
macro_rules! assert_parses_to {
    ($parser:expr, $src:expr, $want:expr $(,)?) => {{
        let got = $parser.parse($src).into_result().expect("parse error");
        use std::borrow::Borrow;
        let got_str: &str = got.borrow();
        assert_eq!(got_str, $want, "on input {:?}", $src);
    }};
}

/// Assert that parsing `src` produces at least one error.
#[macro_export]
macro_rules! assert_fails {
    ($parser:expr, $src:expr $(,)?) => {{
        assert!($parser.parse($src).has_errors(), "expected errors on input {:?}", $src);
    }};
}
