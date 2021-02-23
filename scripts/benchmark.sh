#!/bin/bash

# Usage: benchmark.sh <command>
# For MacOS: install gtime with homebrew `brew install gnu-time`

cmd=$*
format="mem=%KK rss=%MK elapsed=%E cpu=%P cpu.sys=%S inputs=%I outputs=%O"

if command -v gtime; then
  gtime -f "$format" $cmd
else
  /usr/bin/time -f "$format" $cmd
fi
