#!/bin/bash

# Exit if any subcommand fails
set -e

if [ -n "$WITH_LIBSNARK" ]; then
	cargo -Z package-features test --release --package zokrates_cli --features="libsnark" -- --test-threads=1
else
	cargo test --release -- --test-threads=1
fi
