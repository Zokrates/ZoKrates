# Schemes

ZoKrates supports different proof systems we refer to as schemes. All of the available schemes rely on the ALT_BN128 curve, which means that they're all compatible with Ethereum.

We identify the schemes by the reference to the paper that introduced them. Currently the options available are:

| Name | Paper | CLI flag |
| ---- | ----- | -------- |
| PGHR13 | [Here](https://eprint.iacr.org/2013/279) | `--scheme pghr13` |
| G16 | [Here](https://eprint.iacr.org/2016/260) | `--scheme gm17` |
| GM17 | [Here](https://eprint.iacr.org/2017/540) | `--scheme gm17` |

The default scheme is G16.

When not using the default, the CLI flag has to be provided for the following commands:
- `setup`
- `export-verifier`
- `generate-proof`