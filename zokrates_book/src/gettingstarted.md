# Getting Started

## Installation

### One-line install

We provide a one-line install for Linux, MacOS and FreeBSD:

```bash
curl -LSfs get.zokrat.es | sh
```

### Docker

ZoKrates is available on Dockerhub.

```bash
docker run -ti zokrates/zokrates /bin/bash
```

From there on, you can use the `zokrates` CLI.

### From source

You can build the container yourself from [source](https://github.com/ZoKrates/ZoKrates/) with the following commands:

```bash
git clone https://github.com/ZoKrates/ZoKrates
cd ZoKrates
cargo +nightly build --release
cd target/release
```

If you want to enable the libsnark backend in ZoKrates, you need to install some prerequisites:
- boost
- cmake
- libssl

#### Libsnark prerequisites - Linux

As an example, this command installs the required dependencies on Ubuntu:

```bash
apt-get update && apt-get install -y --no-install-recommends \
    build-essential \
    cmake \
    libboost-dev \
    libboost-program-options-dev \
    libgmp3-dev \
    libprocps-dev \
    libssl-dev \
    pkg-config \
    python-markdown
```

#### Libsnark prerequisites - MacOS

You can use [brew](https://brew.sh/) to install the required dependencies:

```bash
brew install boost
brew install cmake
brew install openssl
```

Note that you should follow the instructions displayed after installing `openssl` regarding environment variables. If you're not sure if you followed them, use `brew reinstall openssl`.

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
./zokrates compile -i root.zok
# perform the setup phase
./zokrates setup
# execute the program
./zokrates compute-witness -a 337 113569
# generate a proof of computation
./zokrates generate-proof
# export a solidity verifier
./zokrates export-verifier
```

The CLI commands are explained in more detail in the [CLI reference](reference/cli.md).
