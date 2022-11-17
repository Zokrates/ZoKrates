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
- `universal-setup`
- `compile`
- `export-verifier`
- `verify`

## Schemes

ZoKrates supports different proving schemes. We identify the schemes by the reference to the paper that introduced them. Currently the options available are:

| Scheme | CLI flag | Curves                                   | Universal |
| ---- | -------- |------------------------------------------| ------------|
| [G16](https://eprint.iacr.org/2016/260) | `--proving-scheme g16` | ALTBN_128, BLS12_381                     | No |
| [GM17](https://eprint.iacr.org/2017/540) | `--proving-scheme gm17` | ALTBN_128, BLS12_381, BLS12_377, BW6_761 | No |
| [Marlin](https://eprint.iacr.org/2019/1047) | `--proving-scheme marlin` | ALTBN_128, BLS12_381, BLS12_377, BW6_761 | Yes |

All schemes have a circuit-specific setup phase called `setup`. Universal schemes also feature a preliminary, circuit-agnostic step called `universal-setup`. The advantage of universal schemes is that only the `universal-setup` step requires trust, so that it can be run a single time and reused trustlessly for many programs.

Default: `G16`, except for `universal-setup` for which the default is `Marlin`

When not using the default, the CLI flag has to be provided for the following commands:
- `universal-setup`
- `setup`
- `export-verifier`
- `generate-proof`
- `verify`

## Supporting backends

ZoKrates supports multiple backends. The options are the following:

| Backend | CLI flag | Proving schemes   | Curves                                   |
| ---- | -------- |-------------------|------------------------------------------|
| Bellman | `--backend bellman` | G16               | ALTBN_128, BLS12_381                     |
| Ark | `--backend ark` | G16, GM17, MARLIN | ALTBN_128, BLS12_381, BLS12_377, BW6_761 |

Default: `ark`

When not using the default, the CLI flag has to be provided for the following commands:
- `universal-setup`
- `setup`
- `generate-proof`
- `verify`

## G16 malleability

When using G16, developers should pay attention to the fact that an attacker, seeing a valid proof, can very easily generate a different but still valid proof. Therefore, depending on the use case, making sure on chain that the same proof cannot be submitted twice may *not* be enough to guarantee that attackers cannot replay proofs. Mechanisms to solve this issue include:
- signed proofs
- nullifiers
- usage of an ethereum address as a public input to the program
- usage of non-malleable schemes such as GM17
