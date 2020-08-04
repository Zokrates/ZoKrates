## Standard library

ZoKrates comes with a number of reusable components in the form of a Standard Library. In order to import it as described in the [imports](./imports.html) section, the `$ZOKRATES_HOME` environment variable must be set to the `stdlib` folder.

The full ZoKrates Standard Library can be found [here](https://github.com/Zokrates/ZoKrates/tree/latest/zokrates_stdlib/stdlib).

### Hashes

#### SHA256
We provide an implementation of the SHA256 function from the SHA-2 family of secure hash functions [^1]. The hash functions of the SHA-2 family are considered to be pseudorandom.

SHA256 is available in Ethereum as a pre-compiled contract and thus a hash function that is cheap to evaluate in the EVM. However, the implementation inside a circuit is comparatively expensive, as it is defined for binary in- and outputs and heavily relies on bit manipulation.


#### Pedersen Hashes
The pedersen hash function is inspired by a commitment scheme published by Pedersen [^2].
This hash function’s security is based on the discrete logarithm problem. 
Pedersen-hashes cannot be assumed to be pseudorandom and should therefore not be used where a hash function serves as a random oracle.

In the EVM, operations on the BabyJubJub curve are not natively supported. Therefore, Pedersen hashes are expensive to evaluate on-chain and should be avoided.

By definition, the Pedersen hash function has a fixed-length binary input and outputs a group element, i.e., a point on the BabyJubJub elliptic curve in our case.

#### MiMC
The MiMC hash function was designed by using the MiMC-Feistel permutation [^3] over a prime field in a sponge construction [^4] to arrive at a secure and efficiently provable hash function.
The construction is based on established hash function design principles from symmetric cryptography but is still novel and should thus be used cautiously. MiMC hashes are considered to be pseudorandom.

Due to its native use of prime field arithmetics, MiMC hash functions are efficient in circuits. At the same time, they can be evaluated by the EVM with comparatively little overhead.

The MiMC hash function maps from field elements to field elements; applying the function to its output again does not introduce overhead for packing/unpacking.

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

[^1]: P. FIPS. “180-4 FEDERAL INFORMATION PROCESSING STANDARDS PUBLICA- TION”. In: Secure Hash Standard (SHS), National Institute of Standards and Technology (2012).

[^2]: T. P. Pedersen. “Non-interactive and information-theoretic secure verifiable secret shar- ing”. In: Annual International Cryptology Conference. Springer. 1991, pp. 129–140.

[^3]: M. Albrecht, L. Grassi, C. Rechberger, A. Roy, and T. Tiessen. “MiMC: Efficient en- cryption and cryptographic hashing with minimal multiplicative complexity”. In: In- ternational Conference on the Theory and Application of Cryptology and Information Security. Springer. 2016, pp. 191–219.

[^4]: G. Bertoni, J. Daemen, M. Peeters, and G. Van Assche. “On the indifferentiability of the sponge construction”. In: Annual International Conference on the Theory and Applica-
tions of Cryptographic Techniques. Springer. 2008, pp. 181–197.

