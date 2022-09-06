# Testing

## Unit tests
In ZoKrates, unit tests comprise of
- internal tests for all zokrates crates
- compilation tests for all examples in `zokrates_cli/examples`. These tests only ensure that the examples compile.
- compilation + witness-computation tests. These tests compile the test cases, compute a witness and compare the result with a pre-defined expected result.
Such test cases exist for
    - The zokrates_core crate in `zokrates_core_test/tests`
    - The zokrates_stdlib crate in `zokrates_stdlib/tests`

Unit tests can be executed with the following command:

```
cargo test --release
```

## Integration tests

Integration tests are excluded from `cargo test` by default.
They are defined in the `zokrates_cli` crate in `integration.rs` and use the test cases specified in `zokrates_cli/tests/code`.

Integration tests can then be run with the following command:

```
cargo test --release -- --ignored
```
If you want to run unit and integrations tests together, run the following command:
```
cargo test --release & cargo test --release -- --ignored
```
