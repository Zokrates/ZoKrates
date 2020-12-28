# Proving schemes

## Curves

Proving schemes supported by ZoKrates require a pairing-friendly elliptic curve. The options are the following:

| Curve | CLI flag | Supported by Ethereum |
| ----- | -------- | --------------------- |
| ALT_BN128 | `--curve bn128` | Yes ([EIP-196](https://eips.ethereum.org/EIPS/eip-196), [EIP-197](https://eips.ethereum.org/EIPS/eip-197))  |
| BLS12_381 | `--curve bls12_381` | No ([EIP-2537](https://eips.ethereum.org/EIPS/eip-2537))|
| BLS12_377 | `--curve bls12_377` | No ([EIP-2539](https://eips.ethereum.org/EIPS/eip-2539))|
| BW6_761 | `--curve bw6_761` | No ([EIP-3026](https://eips.ethereum.org/EIPS/eip-3026)) |

Default: `ALT_BN128`

When not using the default, the CLI flag has to be provided for the following commands:
- `compile`
- `export-verifier`
- `verify`

## Schemes

ZoKrates supports different proving schemes. We identify the schemes by the reference to the paper that introduced them. Currently the options available are:

| Scheme | CLI flag | Curves |
| ---- | -------- | ------ |
| [G16](https://eprint.iacr.org/2016/260) | `--proving-scheme g16` | ALTBN_128, BLS12_381 |
| [GM17](https://eprint.iacr.org/2017/540) | `--proving-scheme gm17` | ALTBN_128, BLS12_377, BW6_761 |
| [PGHR13](https://eprint.iacr.org/2013/279) | `--proving-scheme pghr13` | ALTBN_128 |

Default: `G16`

When not using the default, the CLI flag has to be provided for the following commands:
- `setup`
- `export-verifier`
- `generate-proof`
- `verify`

## Supporting backends

ZoKrates supports multiple backends. The options are the following:

| Backend | CLI flag | Proving schemes | Curves |
| ---- | -------- | --------------- | ------ |
| Bellman | `--backend bellman` | G16 | ALTBN_128, BLS12_381 |
| Libsnark | `--backend libsnark` | GM17, PGHR13 | ALTBN_128 |
| Ark | `--backend ark` | GM17 | ALTBN_128, BLS12_377, BW6_761 |

Default: `bellman`

When not using the default, the CLI flag has to be provided for the following commands:
- `setup`
- `generate-proof`
- `verify`

To include libsnark in the build, compile ZoKrates from [source](https://github.com/ZoKrates/ZoKrates/) with the `libsnark` feature:
```bash
cargo +nightly -Z package-features build --release --package zokrates_cli --features="libsnark"
```
 Note, that this is only tested for Linux. If you are on another OS, consider using our Docker container, which includes a libsnark installation.

## G16 malleability

When using G16, developers should pay attention to the fact that an attacker, seeing a valid proof, can very easily generate a different but still valid proof. Therefore, depending on the use case, making sure on chain that the same proof cannot be submitted twice may *not* be enough to guarantee that attackers cannot replay proofs. Mechanisms to solve this issue include:
- signed proofs
- nullifiers
- usage of an ethereum address as a public input to the program
- usage of non-malleable schemes such as GM17
