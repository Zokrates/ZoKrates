#!/bin/bash
set -e

if [ $# -gt 0 ]; then
    echo "Your command line contains $# arguments"
else
    echo "Your command line contains no arguments"
fi

fileName=$1
shift

zokrates compile -i $fileName
zokrates setup
zokrates compute-witness -a "$@"
zokrates generate-proof
zokrates export-verifier