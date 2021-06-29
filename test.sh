#!/bin/bash

# Exit if any subcommand fails
set -e

if [ -n "$WITH_LIBSNARK" ]; then
	# run specifically the libsnark tests inside zokrates_core
	cargo test --release --package zokrates_core --features="libsnark" libsnark
fi

# run all tests without libsnark on
cargo test --release
