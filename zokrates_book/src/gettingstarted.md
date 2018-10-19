# Getting Started

## Installation

Using Docker is currently the recommended way to get started with Zokrates.

```bash
docker run -ti zokrates/zokrates /bin/bash
```

Now you should be dropped into a shell and can find the `zokrates` executable in the following folder `ZoKrates/target/release`.

Alternatively you can build the container yourself with the following commands:

```bash
git clone https://github.com/JacobEberhardt/ZoKrates
cd ZoKrates
docker build -t zokrates .
docker run -ti zokrates /bin/bash
cd ZoKrates/target/release
```

Alternatively, you can build Cargo from [source](https://github.com/JacobEberhardt/ZoKrates/).

## First Steps with ZoKrates

First, create the text-file `add.code` and implement your program:

```zokrates
def main(field a, field b, field c) -> (field):
  return a + b + c
```

The keyword `field` declares the type of the parameters used as elements of the underlying finite field.

Then run the different phases of the protocol:

```bash
./zokrates compile -i 'add.code'
./zokrates setup
./zokrates compute-witness -a 1 2 3
./zokrates generate-proof
./zokrates export-verifier
```

The CLI commands are explained in more detail in this [section
](reference/cli.html) of the doc.