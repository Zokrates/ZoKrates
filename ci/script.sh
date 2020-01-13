# This script takes care of testing your crate

set -ex

# This is the test phase. We will only build as tests happened before.
main() {
	./scripts/install_libsnark_prerequisites.sh
    cross build --target $TARGET
    cross build --target $TARGET --release
}

main
