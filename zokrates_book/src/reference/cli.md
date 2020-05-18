# Command Line Tool

ZoKrates provides a command line interface.
You can see an overview of the available subcommands by running

```sh
zokrates
```

You can get help about a particular subcommand with `--help`, for example:
```sh
zokrates compile --help
```

For each command, you can get the list of expected arguments using `--help`.

## `compile`

```sh
zokrates compile -i /path/to/add.zok
```

Compiles a `.zok` source code file into ZoKrates internal representation of arithmetic circuits.

Creates a compiled binary file at `./out`.
Unless the `--light` flag is set, a human-readable `.ztf` file is generated, which displays the compilation output in ZoKrates Text Format.

## `compute-witness`

```sh
zokrates compute-witness -a 1 2 3
```

Computes a witness for the compiled program found at `./out` and computes arguments of the program.
A witness is a valid assignment of the variables, including the results of the computation.
Arguments of the program are passed as a space-separated list with the `-a` flag, or over `stdin` with the `--stdin` flag.

With the `--abi` flag, arguments are passed in the ZoKrates JSON ABI format described [here](reference/abi.md):

```sh
cat arguments.json | zokrates compute-witness --stdin --abi
```

Creates a witness file at `./witness`

## `setup`

```sh
zokrates setup
```

Generates a trusted setup for the compiled program found at `./out`.

Creates a proving key and a verification key at `./proving.key` and `./verification.key`.
These keys are derived from a source of randomness, commonly referred to as "toxic waste". Anyone having access to the source of randomness can produce fake proofs that will be accepted by a verifier following the protocol.

The [proving scheme](proving_schemes.md) and curve can be chosen with the `proving-scheme` and `curve` flags.

## `export-verifier`

```sh
zokrates export-verifier
```

Using the verification key at `./verification.key`, generates a Solidity contract that contains the generated verification key and a public function to verify a solution to the compiled program at `./out`.

Creates a verifier contract at `./verifier.sol`.

## `generate-proof`

```sh
zokrates generate-proof
```

Using the proving key at `./proving.key`, generates a proof for a computation of the compiled program `./out` resulting in `./witness`.

Returns the proof, for example:

```json
{
  "proof": {
    "a": [
      "0x1b1c65dfd2987bba07bb6b14c35f95afd41be7e4113873fde31de40a94a5fe55",
      "0x10a9811ecc7b168d1fab0e806715d293c777aece4ff21d44300f2151e36b16e9"
    ],
    "b": [
      [
        "0x1ac6921597c999911bc8064722875bdfd2157f3d6278a1a12e1f4a27a063d173",
        "0x24db42163adfb1d6212fff6b8a4e414aec35d239b54a7443df40d5226289fbf7"
      ],
      [
        "0x1a2b44db88cd4d0dd069a0220ef39b6b540598d1f1849636cd266f15260f22d7",
        "0x03f8bafc4b085bcb99779b6004836a047a496c5c2e0ae0bdc0e03f0552eefe07"
      ]
    ],
    "c": [
      "0x181adc5d5b5c4b4be2c44e49fb80f0ce209a2957d5d12f3b9e25a21121b677e3",
      "0x0c0e936d36c812d03e86c1bb23f0c337aa0122fe1509050de2552216e77a9ec7"
    ]
  },
  "inputs": [
    "0x0000000000000000000000000000000000000000000000000000000000000003",
    "0x0000000000000000000000000000000000000000000000000000000000000001"
  ],
  "raw": "..."
}
```

Passed to the verifier contract, this proof can be checked. See 
[Verification](verification.md) section for more details.


## `verify`

```sh
zokrates verify
```

Natively verifies a given proof `./proof.json` with a given verification key `./verification.key`.
The [proving scheme](proving_schemes.md) and curve can be set with the `proving-scheme` and `curve` flags, expecting the same combination as defined in the setup.
