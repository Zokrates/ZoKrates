# Getting Started

## Installation

### Remix online IDE

To write your first SNARK program, check out the ZoKrates plugin in the [Remix online IDE](https://remix.ethereum.org)!

### Docker

ZoKrates is available on Dockerhub.

```bash
docker run -ti zokrates/zokrates zokrates
```

### From source

You can build ZoKrates from [source](https://github.com/ZoKrates/ZoKrates/) with the following commands:

```bash
git clone https://github.com/ZoKrates/ZoKrates
cd ZoKrates
cargo +nightly build --release
cd target/release
```

## Hello ZoKrates!

First, create the text-file `root.zok` and implement your program. In this example, we will prove knowledge of the square root `a` of a number `b`:

```zokrates
{{#include ../../zokrates_cli/examples/book/factorize.zok}}
```

Some observations:
- The keyword `field` is the basic type we use, which is an element of a given prime field.
- The keyword `private` signals that we do not want to reveal this input, but still prove that we know its value.

To make it easier to use `zokrates` inside docker, create this file (call it `z`):
```bash
#! /bin/bash

cd /files
zokrates $*
```

Then run the different phases of the protocol. This is how you do it when you use zokrates in docker.

```bash
# compile
docker run -ti -v `pwd`:/files zokrates/zokrates /files/z compile -i root.zok
# perform the setup phase
docker run -ti -v `pwd`:/files zokrates/zokrates /files/z setup -b libsnark -s gm17
# execute the program
docker run -ti -v `pwd`:/files zokrates/zokrates /files/z compute-witness -a 337 113569
# generate a proof of computation
docker run -ti -v `pwd`:/files zokrates/zokrates /files/z generate-proof -b libsnark -s gm17
# export a solidity verifier
zokrates export-verifier -b libsnark -s gm17
```

The CLI commands are explained in more detail in the [CLI reference](reference/cli.md).
