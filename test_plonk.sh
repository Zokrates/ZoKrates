#!/bin/bash

# Exit if any subcommand fails
set -e

cargo test -j 4 --release --package zokrates_bellman_plonk