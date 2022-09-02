# Getting Started

## Installation

### Online IDEs

To get a feel of the language, try the [ZoKrates playgound](https://play.zokrat.es).

To experiment with creating SNARKs and verifying them in the EVM, check out the ZoKrates plugin in the [Remix online IDE](https://remix.ethereum.org).


### One-line installation

We provide one-line installation for Linux, MacOS and FreeBSD:

```bash
curl -LSfs get.zokrat.es | sh
```

### From source

You can build ZoKrates from [source](https://github.com/ZoKrates/ZoKrates/) with the following commands:

```bash
git clone https://github.com/ZoKrates/ZoKrates
cd ZoKrates
export ZOKRATES_STDLIB=$PWD/zokrates_stdlib/stdlib
cargo +nightly build -p zokrates_cli --release
cd target/release
```

### Docker

ZoKrates is available on Dockerhub.

```bash
docker run -ti zokrates/zokrates /bin/bash
```

From there on, you can use the `zokrates` CLI.

## Hello ZoKrates!

First, create the text-file `root.zok` and implement your program. In this example, we will prove knowledge of the square root `a` of a number `b`:

```zokrates
{{#include ../../zokrates_cli/examples/book/factorize.zok}}
```

Some observations:
- The keyword `field` is the basic type we use, which is an element of a given prime field.
- The keyword `private` signals that we do not want to reveal this input, but still prove that we know its value.

Then run the different phases of the protocol:

```bash
# compile
zokrates compile -i root.zok
# perform the setup phase
zokrates setup
# execute the program
zokrates compute-witness -a 337 113569
# generate a proof of computation
zokrates generate-proof
# export a solidity verifier
zokrates export-verifier
# or verify natively
zokrates verify
```

The CLI commands are explained in more detail in the [CLI reference](toolbox/cli.md).
