use chumsky::Parser;

mod common;

use chumsky_helpers::stateful_strings::StringParserConfig;

/// Parse each fixture under `tests/fixtures/stateful_strings/cooked_multi/*.txt`
/// and snapshot the *inner* string.
///
/// We rely on Insta's built-in `glob!` macro which automatically sets a unique
/// snapshot suffix derived from the fixture file stem, greatly simplifying the
/// boilerplate compared to manual directory walking
/// ([docs](https://insta.rs/docs/advanced/#globbing)).
#[test]
fn cooked_multi_line_fixtures() {
    let cfg = StringParserConfig::default();

    insta::glob!("fixtures/stateful_strings/cooked_multi/*.txt", |path| {
        let src = std::fs::read_to_string(path).expect("failed to read fixture file");

        let parsed = cfg.cooked_multi_line().parse(&src);

        // Snapshot the *inner* string.  The snapshot filename will be
        // suffixed with the fixture's stem (e.g. `01_basic`).
        insta::assert_debug_snapshot!(parsed);
    });
}
