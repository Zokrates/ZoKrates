# ZoKrates

## Using ZoKrates

Set the libsnark library path in `LD_LIBRARY_PATH`
```
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib
```
### CLI


### Example

To execute the program
```
def add(a, b, c):
  return a + b + c
```
with `add(1, 2, 3)`, call
```
./ZoKrates compile -i add.code_path
./ZoKrates shortcut -a "1 2 3"
```

## Building

Currently needs to be build with nightly Rust.

### Docker

Example usage:
```
docker build -t zokrates .
docker run -ti zokrates /bin/bash
cd ZoKrates
./target/debug/ZoKrates compile -i examples/add.code
```

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

## Testing

Run normal tests with
```
cargo test
```
and run long and expensive tests with
```
cargo test -- --ignored
```
