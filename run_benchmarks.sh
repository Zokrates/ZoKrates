#!/bin/bash

for (( i = 0; i < 100; i++ )); do
	./target/release/zokrates compile -i $1 >> $3_compile.out
done
echo "Compile finished."
for (( i = 0; i < 100; i++ )); do
	./target/release/zokrates compute-witness -a $2 >> $3_witness.out
done
echo "Witness finished."
for (( i = 0; i < 100; i++ )); do
	./target/release/zokrates setup >> $3_setup.out
done
echo "Setup finished."
for (( i = 0; i < 100; i++ )); do
	./target/release/zokrates generate-proof >> $3_proof.out
done
echo "Proof finished."
for (( i = 0; i < 100; i++ )); do
	./target/release/zokrates export-verifier >> $3_verifier.out
done
echo "Verifier finished."
echo "All finished."