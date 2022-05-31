#!/bin/bash

# Exit if any subcommand fails
set -e
export RUSTFLAGS="--remap-path-prefix=$PWD="

cargo build --release --package zokrates_cli
