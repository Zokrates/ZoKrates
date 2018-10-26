# Getting Started

## Installation

Using Docker is currently the recommended way to get started with ZoKrates.

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

## Hello ZoKrates!

First, create the text-file `root.code` and implement your program. IN this example, we will prove knowledge of the square root of a number:

```zokrates
def main(private field a, field b) -> (field):
  field result = if a * a == b then 1 else 0
  return result
```

Some observations:
- The keyword `field` is the basic type we use, which is an element of a prime field.
- The keyword `private` signals that we do not want to reveal this input, but still prove that we know its value.

Then run the different phases of the protocol:

```bash
./zokrates compile -i root.code
./zokrates setup
./zokrates compute-witness -a 337 113569
./zokrates generate-proof
./zokrates export-verifier
```

The CLI commands are explained in more detail in this [section
](reference/cli.html) of the documentation.