#!/bin/bash
set -e

bin=$1; stdlib=$2

function zokrates() {
  ZOKRATES_STDLIB=$stdlib $bin "$@"
}

zokrates compile -i hashexample.zok
zokrates compute-witness -a 0 0 0 5 --verbose

cp -f hashexample_updated.zok hashexample.zok

zokrates compile -i hashexample.zok
zokrates setup
zokrates export-verifier
zokrates compute-witness -a 0 0 0 5
zokrates generate-proof