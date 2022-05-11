#!/bin/bash

# Exit if any subcommand fails
set -e

if [ -n "$WITH_LIBSNARK" ]; then
	cargo test -j 4 --release --package zokrates_cli --features="libsnark" -- --ignored
else
	cargo test -j 4 --release --package zokrates_cli                       -- --ignored
fi