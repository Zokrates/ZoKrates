# Provin schemes

ZoKrates supports different proving schemes. All of the available schemes rely on the ALT_BN128 curve, which means that they're all compatible with Ethereum.

We identify the schemes by the reference to the paper that introduced them. Currently the options available are:

| Name | Paper | CLI flag | Requires libsnark |
| ---- | ----- | -------- | --------- |
| PGHR13 | [Here](https://eprint.iacr.org/2013/279) | `--proving-scheme pghr13` | Yes |
| G16 | [Here](https://eprint.iacr.org/2016/260) | `--proving-scheme g16` | No |
| GM17 | [Here](https://eprint.iacr.org/2017/540) | `--proving-scheme gm17` | Yes |

The default proving scheme is G16.

When not using the default, the CLI flag has to be provided for the following commands:
- `setup`
- `export-verifier`
- `generate-proof`

## G16 malleability

When using G16, developers should pay attention to the fact that an attacker seeing a valid proof can very easily generate a different but still valid proof. Therefore, depending on the use case, making sure on chain that the same proof cannot be submitted twice may *not* be enough to guarantee that attackers cannot replay proofs. Mechanisms to solve this issue include:
- signed proofs
- nullifiers
- usage of an ethereum address as a public input to the program
- usage of non-malleable schemes such as GM17