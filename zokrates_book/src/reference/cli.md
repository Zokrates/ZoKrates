# Command Line Tool

ZoKrates provides a command line interface.
You can see an overview of the available subcommands by running

```sh
zokrates
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

Creates a proving key and a verifying key at `./proving.key` and `./verifying.key`.
These keys are derived from a source of randomness, commonly referred to as "toxic waste". Anyone having access to the source of randomness can produce fake proofs that will be accepted by a verifier following the protocol.

## `export-verifier`

```sh
zokrates export-verifier
```

Using the verifying key at `./verifying.key`, generates a Solidity contract that contains the generated verification key and a public function to verify a solution to the compiled program at `./out`.

Creates a verifier contract at `./verifier.sol`.

## `generate-proof`

```sh
zokrates generate-proof
```

Using the proving key at `./proving.key`, generates a proof for a computation of the compiled program `./out` resulting in `./witness`.

Returns the proof, for example:

```k
A = 0x45582d7906c967b1fd1cac0aad3efefa526e4cd888b8ecb5907b46c2eb1f781, 0x8158089a63a6aafa4afc3bbfd5ebf392e5ef61d0c5faf2e2445c9112450f29c
A_p = 0x5e4fe0bfa79a571b8918138ee5d7b3d0ad394c9bb8f7d2e1549f7e3c3bab7e9, 0x1708b5ba3d138e433406c792f679ae6902fc9f7c6131305a9a5f826dbe2d71fb
B = [0x34f5c5b7518597452e55a69bf9171a63837a98a1c1c1870b610b2cfe79c4573, 0x18e56afd179d67960db838a8fdb128eb78d5dd2c1ffcd564f9d0dada928ed71f], [0xf160ea8d2dc33b564a45c0998309b4bf5a050cc8f6288793b7401b37d1eb1a2, 0x23ade8ba2c64300b5ff90e18641516407054a21179829252fd87f1bd61a3be34]
B_p = 0xc88b87d45f90da42b9c455da16dad76996ef5b1e859a4f0db7dcef4f7e3b2fd, 0x20ed7c62dd8c6c47506e6db1d4837daa42ae80b931227153054539dcbf6f3778
C = 0x2c230cbffbcb6211d2cf8f434df291a413721e3bef5ada4030d532d14b6ea504, 0x21421565f75429d0922c8cf00b68e4da23c61670e787ce6a5de14a5a86ebdcb0
C_p = 0xce11fe724ce1ce183c15c4f5405d9607d6c769422aa9f62f4868478324a2f5, 0x1e585b35ed22ef32fd70ef960818f1514d1dd94b3517c127e782de24173c69f9
H = 0x2306e74a1a7e318d2d3c40cbea708b0e0b91cd1548c9db6261fc2bd815740978, 0xde538e4e99b0e20e84cdbbd3bc08c37bca0af21edd67faf52bc4027a9b00f7c
K = 0x1868436121f271e9fbf78a8f75bb4077e2d4f208891793fd5b468afc3b05c0e4, 0x1021c3ecb15c3fd7340d4eb5bf446e1ad457020e4f8b7cc82f8af64507a35fbe
```

Passed to the verifier contract, this proof can be checked.
For example, using `web3`, a call would look like the following:

```k
Verifier.at(<verifier contract address>).verifyTx(A, A_p, B, B_p, C, C_p, H, K, [...publicInputs, ...outputs])
```

Where `A, ..., K` are defined as above (adding brackets and quotes: `A = ["0x123", "0x345"]`), `publicInputs` are the public inputs supplied to witness generation and `outputs` are the results of the computation.
