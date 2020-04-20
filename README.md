# Unoptimized Branch
This branch is used solely for benchmarking purposes.
For that purpose, it should always be built with `cargo build --release`.

It turns off the following optimizations:
- IR Optimizations
- Constant Propagation in Static Analysis
- Constant Propagation after Flattening
- Memoization (TODO after it is released)

**Warning**
This breaks the packing dsl programs, since they require constant propagation.
Otherwise, the exponentiation performed has non-constant exponent.
