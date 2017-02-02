# VerifiableStatementCompiler

## Using VerifiableStatementCompiler

Set include the libsnark library path in `LD_LIBRARY_PATH`
```
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib
```

Command
```
./code_to_r1cs program [inputs]
```
- `program`: Path to the program that you want to be compiled.
- `inputs` (optional): String of variable assignments of the inputs of a program split with whitespaces.<br>

### Example

To execute the program
```
def add(a, b, c):
  return a + b + c
```
with `add(1, 2, 3)`, call
```
./code_to_r1cs program "1 2 3"
```

## Building

Currently needs to be build with nightly Rust.

### With libsnark

Install [libsnark](https://github.com/scipr-lab/libsnark) to `/usr/local` with
```
make install lib PREFIX=/usr/local NO_PROCPS=1 NO_GTEST=1 NO_DOCS=1 CURVE=ALT_BN128 FEATUREFLAGS="-DBINARY_OUTPUT=1 -DMONTGOMERY_OUTPUT=1 -DNO_PT_COMPRESSION=1"
```
and build with
```
cargo build
```

### Without libsnark
Build with the feature `nolibsnark`
```
cargo build --features nolibsnark
```
