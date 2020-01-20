# This script takes care of testing your crate

set -ex

# This is the test phase. We will only build as tests happened before.
main() {
	cargo build --bin zokrates --target $TARGET --release && echo "Building with libsnark not supported for $TARGET" && cross build --bin zokrates --no-default-features --target $TARGET --release
}

main
