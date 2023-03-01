# Performing a trusted setup using a multi-party computation protocol (MPC)

The zk-SNARK schemes supported by ZoKrates require a trusted setup. This procedure must be run to generate the proving and verification keys. This procedure generates some data often referred to as "toxic waste" which can be used to create fake proofs which will be accepted by the verifier. The entity running the trusted setup is trusted to delete this toxic waste.
Using an MPC protocol, we can run the trusted setup in a decentralized way, so that this responsibility is shared among all participants of the setup. If at least one participant is honest and deletes their part of the toxic waste, then no fake proofs can be created by anyone.
This section of the book describes the steps to perform a trusted setup for the Groth16 scheme.

## Pre-requisites

The trusted setup is done in two steps. The first step, also known as "phase 1", does not depend on the program and is called Powers of Tau. The second step is called "phase 2" and is circuit-specific, so it should be done separately for each different program. The Ethereum community runs a phase 1 setup called [Perpetual Powers of Tau](https://github.com/weijiekoh/perpetualpowersoftau), whose output we can use. Therefore, we only need to run phase 2 of the setup.

## Compiling a circuit

We will start this tutorial by using ZoKrates to compile a basic program.
First, we create a new file named `program.zok` with the following content:

```zokrates
{{#include ../../../zokrates_cli/examples/book/mpc_tutorial/program.zok}}
```

We compile the program using the `compile` command.

```
{{#include ../../../zokrates_cli/examples/book/mpc_tutorial/test.sh:11}}
```

## Initializing a phase 2 ceremony

We then initialize a phase 2 ceremony with the following command:

```
$ {{#include ../../../zokrates_cli/examples/book/mpc_tutorial/test.sh:15}}

Initializing MPC...
Parameters written to `mpc.params`
```

Using the `-r` flag, we pass a path to the file which contains the parameters for our circuit with depth `2^n` (`phase1radix2m{n}`).
The parameters for various circuit depths can be computed using the [phase2-bn254](https://github.com/kobigurk/phase2-bn254) utility
by picking the latest response from the [Perpetual Powers of Tau](https://github.com/weijiekoh/perpetualpowersoftau) and following the instructions in the mentioned repositories.

## Making a contribution

In this example, we will conduct a ceremony that has 3 participants: Alice, Bob, and Charlie.
Participants will run the contributions in sequential order, managed by the coordinator (us).

Firstly, our initial `mpc.params` file is given to Alice who runs the following command:

```
$ {{#include ../../../zokrates_cli/examples/book/mpc_tutorial/test.sh:18}}

Contributing to `mpc.params`...
The BLAKE2b hash of your contribution is:

        4ebf1359 416fbc42 31af6476 9173cb33 
        32b8c2f9 475d143a 25634a5c e461eb67 
        5f7738b1 6478a020 7ec9d365 9170bca6 
        154b31df d307b78e ca0c025f 59c5a7fb

Your contribution has been written to `alice.params`
```

Alice must give some randomness to the contribution, which is done by the `-e` flag.

Examples of entropy sources:
* `/dev/urandom` from one or more devices
* The most recent block hash
* Randomly mashing keys on the keyboard

Secondly, the output file `alice.params` is sent to Bob who runs his contribution:

```
$ {{#include ../../../zokrates_cli/examples/book/mpc_tutorial/test.sh:21}}

Contributing to `alice.params`...
The BLAKE2b hash of your contribution is:

        1a4e0d17 449b00ec f31d2072 59bc173c
        f30f6dbd 78c81921 869091a8 e40f454e
        8c8d72e8 395bf044 cd777842 b6ab1d88
        9e24cf7f 7d88b473 2190fb0c 730fb6fc

Your contribution has been written to `bob.params`
```

Thirdly, with the same procedure as above, Charlie makes his contribution on top of Bob's:

```
$ {{#include ../../../zokrates_cli/examples/book/mpc_tutorial/test.sh:24}}

Contributing to `bob.params`...
The BLAKE2b hash of your contribution is:

        46dc6c01 ec778382 93b333b2 116a4bfb
        a9aca5dd eb6945f1 cbe07cda 6ffb3ffd 
        cf4e4736 62fe2339 166d5b87 db392ca6
        d2e87e36 92cc8f0e e618298f c3f7caf1

Your contribution has been written to `charlie.params`
```

## Applying a random beacon

To finalize the ceremony, we can apply a random beacon to get the final parameters:

```
$ {{#include ../../../zokrates_cli/examples/book/mpc_tutorial/test.sh:27}}

Creating a beacon RNG
0: b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9
1: bc62d4b80d9e36da29c16c5d4d9f11731f36052c72401a76c23c0fb5a9b74423
2: 76dfcb21a877aaeba06b3269d08dc2ed1d38c62ffec132800b46e94b14f72938
...removed for brevity
1022: dd842dc43d9ac5c6dff74cca18405123761d17edd36724b092ef57c237b31291
1023: a11c8a03c22e9c31c037aa0085c061ba8dd19a3f599314570702eeef1baacd79
Final result of beacon: ef8faec4fc31faf341f368084b82d267d380992e905c923a179e0717ce39708d

Contributing to `charlie.params`...
The BLAKE2b hash of your contribution is: 

        83d67a6f 935fc4d0 5733ebed d43f2074 
        5425b105 9a32a315 a790668a f5a1f021 
        66f840e2 e6a5d441 38593163 5b86df09 
        a00f352e 2ad2a88b ede07886 2134b889

Your contribution has been written to `final.params`
```

The random beacon is the `2^n` iteration of `SHA256` over the hash evaluated on
some high entropy and publicly available data. Possible sources of data could be:
* The closing value of the stock market on a certain date
* The output of a selected set of national lotteries
* The value of a block at a particular height in one or more blockchains
* [League of Entropy](https://www.cloudflare.com/leagueofentropy/) (drand)

## Verifying contributions

At any point in the ceremony we can verify contributions by running the following command:

```
$ {{#include ../../../zokrates_cli/examples/book/mpc_tutorial/test.sh:30}}

Verifying contributions...

Transcript contains 4 contributions:
0: 4ebf1359416fbc4231af64769173cb3332b8c2f9475d143a25634a5ce461eb675f7738b16478a0207ec9d3659170bca6154b31dfd307b78eca0c025f59c5a7fb
1: 1a4e0d17449b00ecf31d207259bc173cf30f6dbd78c81921869091a8e40f454e8c8d72e8395bf044cd777842b6ab1d889e24cf7f7d88b4732190fb0c730fb6fc
2: 46dc6c01ec77838293b333b2116a4bfba9aca5ddeb6945f1cbe07cda6ffb3ffdcf4e473662fe2339166d5b87db392ca6d2e87e3692cc8f0ee618298fc3f7caf1
3: 83d67a6f935fc4d05733ebedd43f20745425b1059a32a315a790668af5a1f02166f840e2e6a5d441385931635b86df09a00f352e2ad2a88bede078862134b889

Contributions verified
```

## Exporting keys

Once the ceremony is finalized, we can export the keys and use them to generate proofs and verify them.

```
{{#include ../../../zokrates_cli/examples/book/mpc_tutorial/test.sh:32:38}}
```

## Conclusion

The secure generation of parameters for zk-SNARKs is a crucial step in the trustworthiness of the resulting proof system.
The security of the ceremony relies entirely on the fact that at least one participant needs to securely delete their "toxic waste" for the resulting parameters to be generated honestly.
Opening the ceremony to a large number of participants reduces the probability that the resulting parameters are dishonest.
Once the ceremony is finalized, we can generate a verifier smart contract by using the keys we obtained through the trusted setup ceremony.
At this point, we can safely deploy the contract and verify proofs on-chain.
