# Chumsky Helpers Development Guide

## Build & Test Commands
- Build: `cargo build`
- Check: `just check` (runs fmt, clippy, audit)
- Run all tests: `cargo nextest run` or `just test`
- Run single test: `cargo nextest run [test_name]` (e.g. `cargo nextest run test_iso_date_basic`)
- Run test with pattern: `cargo nextest run [module]::[test_pattern]` (e.g. `cargo nextest run datetime::test_iso_date`)
- Coverage: `just cov` or `just cov-local-web` (opens in browser)
- Watch mode: `just watch` (runs check and test on file changes)

## Code Style Guidelines
- Formatting: 100 character line limit, 4 spaces for indentation (enforced by rustfmt)
- Imports: Group and alphabetically order all imports
- Use full module paths for imports (e.g. `use chumsky::prelude::*`)
- Error handling: Use `try_map` for error conversion, return detailed errors with spans
- Naming: Use descriptive, snake_case for functions and variables
- Tests: Write comprehensive unit tests and property tests with proptest
- Documentation: Document public functions with examples
- Use type aliases for common patterns (e.g. `Spanned<T>`)
- Follow the existing parser combinator pattern with labeled components