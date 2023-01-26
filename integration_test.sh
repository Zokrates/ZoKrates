#!/bin/bash

# Exit if any subcommand fails
set -e
./scripts/install_foundry.sh
cargo test -j 4 --release --package zokrates_cli                       -- --ignored