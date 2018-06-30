#!/bin/bash

# Exit if any subcommand fails
set -e

cd zokrates-cli
if [ $WITH_LIBSNARK ]; then
	cargo build --features libsnark
else
	cargo build
fi

cd ..
