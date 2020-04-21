## Standard library

ZoKrates comes with a number of reusable components which are defined at `./stdlib/` in the ZoKrates root repository. In order to import the standard library as described in the [imports](./imports.html) section the `$ZOKRATES_HOME` environment variable needs to be set to the `stdlib` folder.  The standard library is solely based on the ZoKrates DSL and can be easily extended.

The following section highlights a subset of available imports:

### Hashes

#### sha256

```zokrates
import "hashes/sha256/512Padded.zok"
```

A function that takes 2 `field[256]` arrays as inputs and returns their sha256 compression function as an array of 256 field elements.

#### sha256compression

```zokrates
import "hashes/sha256/512bit.zok"
```

A function that takes 2 `field[256]` arrays as inputs and returns their sha256 compression function as an array of 256 field elements.
The difference with `sha256` is that no padding is added at the end of the message, which makes it more efficient but also less compatible with Solidity.

There also is support for 2-round (1024-bit input) and 3-round (1536-bit input) variants, using  `hashes/1024bit.zok` and `hashes/1536bit.zok` respectively.

#### sha256packed

```zokrates
import "hashes/sha256/512bitPacked.zok"
```

A function that takes an array of 4 field elements as inputs, unpacks each of them to 128 bits (big-endian), concatenates them and applies sha256. It then returns an array of 2 field elements, each representing 128 bits of the result.

### Public-key Cryptography

#### Proof of private-key ownership

```zokrates
import "ecc/proofOfOwnership.zok"
```

Verifies match of a given public/private keypair. Checks if the following equation holds for the provided keypair:
`pk = sk*G`
where `G` is the chosen base point of the subgroup and `*` denotes scalar multiplication in the subgroup.

#### Signature verification

```zokrates
import "signatures/verifyEddsa.zok"
```

Verifies an EdDSA Signature. Checks the correctness of a given EdDSA Signature `(R,S)` for the provided public key `A` and message `(M0, M1)`. Check out this [python repository](https://github.com/Zokrates/pycrypto) for tooling to create valid signatures.

### Packing / Unpacking

#### pack128

```zokrates
import "utils/pack/pack128"
```

Packs 128 field elements as one.

#### unpack128

```zokrates
import "utils/pack/unpack128"
```

Unpacks a field element to 128 field elements.

#### pack256

```zokrates
import "utils/pack/pack256"
```

Packs 256 field elements as one. Overflows can occur.

#### nonStrictUnpack256

```zokrates
import "utils/pack/nonStrictUnpack256"
```

Unpacks a field element into 256 field elements. Uniqueness of the output is not guaranteed.

