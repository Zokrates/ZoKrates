#!/bin/bash

# Exit if any subcommand fails
set -e

# cargo test --release -- --ignored

# if [ -n "$WITH_LIBSNARK" ]; then
	# cargo -Z package-features test --release --package zokrates_cli --features="libsnark" -- --ignored
	ls
	cd target/debug/

	#Generate proof file used for testing
	printf '%s\n' \
		'def main(private field a, field b) -> (field):' \
		'    field result = if a * a == b then 1 else 0 fi' \
		'    return result' > root.code

	# Compile test file:
	./zokrates compile -i root.code

	#PGHR13:
	./zokrates setup --proving-scheme pghr13
	./zokrates compute-witness -a 337 113569

	./zokrates generate-proof --proving-scheme pghr13 -j pghr13-proof.json
	./zokrates export-verifier --proving-scheme pghr13 -o pghr13-v1-verifier.sol
	./zokrates export-verifier --proving-scheme pghr13 -o pghr13-v2-verifier.sol --abiv2

	#GM17:
	./zokrates setup --proving-scheme gm17
	./zokrates compute-witness -a 337 113569

	./zokrates generate-proof --proving-scheme gm17 -j gm17-proof.json
	./zokrates export-verifier --proving-scheme gm17 -o gm17-v1-verifier.sol
	./zokrates export-verifier --proving-scheme gm17 -o gm17-v2-verifier.sol --abiv2

	#G16:
	./zokrates setup --proving-scheme g16
	./zokrates compute-witness -a 337 113569

	./zokrates generate-proof --proving-scheme g16 -j g16-proof.json
	./zokrates export-verifier --proving-scheme g16 -o g16-v1-verifier.sol
	./zokrates export-verifier --proving-scheme g16 -o g16-v2-verifier.sol --abiv2

	#Install dependencies
	ls
	cd ../../zokrates_core/tests/integration
	ls
	npm install
	cd ../../../

	#Compile, Deploy and Call contracts
	node zokrates_core/tests/integration/test.js g16 v1
	node zokrates_core/tests/integration/test.js g16 v2
	node zokrates_core/tests/integration/test.js pghr13 v1
	node zokrates_core/tests/integration/test.js pghr13 v2
	node zokrates_core/tests/integration/test.js gm17 v1
	node zokrates_core/tests/integration/test.js gm17 v2
# fi
