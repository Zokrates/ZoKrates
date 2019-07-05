# Testing

## Unit tests
Unit tests can be executed with the following command:

```
cargo test --release
```

## Integration tests

Integration tests are excluded from `cargo test` by default.
Before running integration tests 
    1. Make sure your `$ZOKRATES_HOME` is set correctly 
    2. You have [solcjs](https://github.com/ethereum/solc-js) installed and in your `$PATH`.
    This can conventiely done through `npm` by running 
    ```
    npm install -g solc
    ```
Integration tests can then be included in a test run with the following command:

```
cargo test --release -- --ignored
```
If you want to run unit and integrations tests together, run the following command:
```
cargo test --release & cargo test --release -- --ignored
```