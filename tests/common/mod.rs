use chumsky_helpers::number::ExplicitSign;

/// Assert that the `display` string begins with the correct sign corresponding
/// to `expected_sign`.
pub fn assert_display_sign(display: &str, expected_sign: ExplicitSign) {
    match expected_sign {
        ExplicitSign::Positive => assert!(display.starts_with('+')),
        ExplicitSign::Negative => assert!(display.starts_with('-')),
        ExplicitSign::None => assert!(!display.starts_with('+') && !display.starts_with('-')),
    }
}
