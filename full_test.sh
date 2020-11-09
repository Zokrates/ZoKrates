#!/bin/bash

# Exit if any subcommand fails
set -e

cargo test --release -- --ignored --test-threads=1
