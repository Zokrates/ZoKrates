#!/bin/bash
set -e

bin=$1; stdlib=$2

function zokrates() {
  ZOKRATES_STDLIB=$stdlib $bin "$@"
}

# compile the program
zokrates compile -i program.zok -o circuit

# initialize the ceremony
# this step requires phase1 files eg. phase1radix2m2 for circuits of 2^2 constraints
zokrates mpc init -i circuit -o mpc.params -r ./phase1radix2m2

# first contribution
zokrates mpc contribute -i mpc.params -o alice.params -e "alice 1"

# second contribution
zokrates mpc contribute -i alice.params -o bob.params -e "bob 2"

# third contribution
zokrates mpc contribute -i bob.params -o charlie.params -e "charlie 3"

# apply a random beacon
zokrates mpc beacon -i charlie.params -o final.params -h b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9 -n 10

# verify contributions
zokrates mpc verify -i final.params -c circuit -r ./phase1radix2m2

# export keys from final parameters (proving and verification key)
zokrates mpc export -i final.params

# use the keys to generate proofs and verify
zokrates compute-witness -i circuit -a 123456789 987654321 --verbose
zokrates generate-proof -i circuit -b bellman
zokrates verify -b bellman