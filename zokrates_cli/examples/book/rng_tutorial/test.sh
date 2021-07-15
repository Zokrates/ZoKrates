#!/bin/bash
set -e

bin=$1; stdlib=$2

function zokrates() {
  ZOKRATES_STDLIB=$stdlib $bin $*
}

zokrates compile -i get_hash.zok -o get_hash --ztf
zokrates compute-witness --verbose -i get_hash -a 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15

mkdir alice bob

cp reveal_bit.zok bob/reveal_bit.zok
cp reveal_bit.zok alice/reveal_bit.zok

cd bob

zokrates compile -i reveal_bit.zok -o reveal_bit
zokrates setup -i reveal_bit

cd ..
cp bob/proving.key alice/proving.key

cd alice
zokrates compile -i reveal_bit.zok -o reveal_bit
zokrates compute-witness --verbose -i reveal_bit -a 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 510
zokrates generate-proof -i reveal_bit

cd ..
cp alice/proof.json bob/proof.json

cd bob
zokrates verify
zokrates export-verifier