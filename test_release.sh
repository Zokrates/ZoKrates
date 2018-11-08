#!/bin/bash

# Exit if any subcommand fails
set -e

if [ -n "$WITH_LIBSNARK" ]; then
	cargo test --release
else
	cargo -Z package-features test --release --no-default-features
fi