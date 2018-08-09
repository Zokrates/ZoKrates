#!/bin/bash

# Exit if any subcommand fails
set -e

if [ -n "$WITH_LIBSNARK" ]; then
	cargo test -- --ignored
else
	cargo -Z package-features test --no-default-features -- --ignored
fi