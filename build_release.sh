#!/bin/bash

# Exit if any subcommand fails
set -e

if [ -n "$WITH_LIBSNARK" ]; then
	cargo build --release
else
	cargo -Z package-features build --release --no-default-features
fi
