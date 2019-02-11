# Getting Started

## Installation

### Docker

Using Docker is currently the recommended way to get started with ZoKrates.

```bash
docker run -ti zokrates/zokrates /bin/bash
```

From there on, you can use the `zokrates` CLI.

### From source

You can build the container yourself from [source](https://github.com/JacobEberhardt/ZoKrates/) with the following commands:

```bash
git clone https://github.com/JacobEberhardt/ZoKrates
cd ZoKrates
docker build -t zokrates .
docker run -ti zokrates /bin/bash
cd ZoKrates/target/release
```

## Hello ZoKrates!

First, create the text-file `root.code` and implement your program. In this example, we will prove knowledge of the square root `a` of a number `b`:

```zokrates
{{#include ../../zokrates_cli/examples/book/factorize.code}}
```

Some observations:
- The keyword `field` is the basic type we use, which is an element of a given prime field.
- The keyword `private` signals that we do not want to reveal this input, but still prove that we know its value.

Then run the different phases of the protocol:

```bash
# compile
./zokrates compile -i root.code
# perform the setup phase
./zokrates setup
# execute the program
./zokrates compute-witness -a 337 113569
# generate a proof of computation
./zokrates generate-proof
# export a solidity verifier
./zokrates export-verifier
```

The CLI commands are explained in more detail in the [CLI reference](reference/cli.html).
