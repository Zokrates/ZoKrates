# Test Setup

Reproducable test setup for ZoKrates:
- In main.rs, every `println!` is commented out which is not related to error output or benchmark output
- Make the run_benchmarks.sh script executable by running
```
	chmod +x run_benchmarks.sh
```
- The script takes three parameters and executes each ZoKrates step 100 times in a row. The parameters are:
	- Path to the code to be compiled
	- Witness as it would be passed to the `compute-witness` phase
	- Outfile name prefix. I.e., the program output is appended into files named `prefix_[compile/witness/setup/proof/verifier].out`

Example:
```
	./run_benchmarks.sh "examples/sudokuchecker.code" "3 3 2 4 2 4 2 1 4 4 1 3 1 2 1 3" "sudoku"
```
