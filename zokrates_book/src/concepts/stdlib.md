## Standard library

ZoKrates comes with a number of reusable components in the form of a Standard Library. In order to import it as described in the [imports](./imports.html) section, the `$ZOKRATES_HOME` environment variable must be set to the `stdlib` folder.

The full ZoKrates Standard Library can be found [here](https://github.com/Zokrates/ZoKrates/tree/latest/zokrates_stdlib/stdlib).

### Hashes

#### Sha256

The sha526 hash function comes in a variety of flavours. It can be a good choice when pseudo-randomness, or compatibility with off-circuit systems such as the EVM are required, at the cost of a higher number of constraints.

#### Pedersen

Pedersen hashing takes advantage of the BabyJubJub embedded elliptic curve on ALT_BN128 to provide a collision-resistant, cheap hash function. One tradeoff is a relatively high cost when computing it inside the EVM.

#### MiMC

MiMC is an alternative hash function which comes at a reduced cost and is also relatively cheap inside the EVM.

### Elliptic curve cryptography

Thanks to the existence of BabyJubJub, an efficient elliptic curve embedded in ALT_BN128, we provide tools to perform elliptic curve operations such as:

- Point operations
- Proving knowledge of a private EdDSA key
- Proving validity of an EdDSA signature

Check out this [python repository](https://github.com/Zokrates/pycrypto) for tooling, for example to generate EdDSA signatures to then check in a SNARK.

### Utils

#### Packing / Unpacking

As some operations require their input to be provided in the form of bits, we provide tools to convert back and forth between field elements and their bit representations.

#### Casts

Helpers to convert between types representing binary data.

#### Multiplexer

Optimised tools to branch inside circuits.

