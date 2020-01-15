# This script takes care of testing your crate

set -ex

# This is the test phase. We will only build as tests happened before.
main() {
    cargo build --target $TARGET
    cargo build --target $TARGET --release
}

main
