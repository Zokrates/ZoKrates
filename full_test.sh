#!/bin/bash

# Exit if any subcommand fails
set -e

cd zokrates_cli
if [ -n "$WITH_LIBSNARK" ]; then
	cargo test --features libsnark -- --ignored
else
	cargo test -- --ignored
fi

cd ..