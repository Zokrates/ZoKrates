# Backends

ZoKrates supports different proof systems to be used as backends. All of the available backends rely on the ALT_BN128 curve, which means that they're all compatible with Ethereum.

We identify the backends by the reference to the paper that introduced them. Currently the options available are:

| Name | Paper | CLI flag |
| ---- | ----- | -------- |
| PGHR13 | [Here](https://eprint.iacr.org/2013/279) | `--backend pghr13` |
| GM17 | [Here](https://eprint.iacr.org/2017/540) | `--backend gm17` |

The default backend is PGHR13.

When not using the default, the CLI flag has to be provided for the following commands:
- `setup`
- `export-verifier`
- `generate-proof`