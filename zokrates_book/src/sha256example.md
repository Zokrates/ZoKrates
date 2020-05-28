# Tutorial: Proving knowledge of a hash preimage

Let's jump into ZoKrates by working through a hands-on project together!

We'll implement an operation that's very typical in blockchain use-cases: proving knowledge of the preimage for a given hash digest.
In particular, we'll show how ZoKrates and the Ethereum blockchain can be used to allow a prover, let's call her Peggy, to demonstrate beyond any reasonable doubt to a verifier, let's call him Victor, that she knows a hash preimage for a digest chosen by Victor, without revealing what the preimage is.

## Pre-requisites

Make sure you have followed the instructions in the [Getting Started](gettingstarted.md) chapter and are able to run the "Hello World" example described there.

## Computing a Hash using ZoKrates

We will start this tutorial by using ZoKrates to compute the hash for an arbitrarily chosen preimage, being the number `5` in this example.

First, we create a new file named `hashexample.zok` with the following content:

```zokrates
{{#include ../../zokrates_cli/examples/book/hashexample.zok}}
```

The first line imports the `sha256packed` function from the ZoKrates standard library.

`sha256packed` is a SHA256 implementation that is optimized for the use in the ZoKrates DSL. Here is how it works: We want to pass 512 bits of input to SHA256. However, a `field` value can only hold 254 bits due to the size of the underlying prime field we are using. As a consequence, we use four field elements, each one encoding 128 bits, to represent our input. The four elements are then concatenated in ZoKrates and passed to SHA256. Given that the resulting hash is 256 bit long, we split it in two and return each value as a 128 bit number.

In case you are interested in an example that is fully compliant with existing SHA256 implementations in Python or Solidity, you can have a look at this [blog](https://blog.decentriq.ch/proving-hash-pre-image-zksnarks-zokrates) post.

Our code is really just using the `sha256packed`, returning the computed hash.

Having our problem described in ZoKrates' DSL, we can now continue using ZoKrates for the rest of our workflow.

First, we compile the program into an arithmetic circuit using the `compile` command.

```sh
./zokrates compile -i hashexample.zok
```

As a next step we can create a witness file using the following command:

```sh
./zokrates compute-witness -a 0 0 0 5
```

Using the flag `-a` we pass arguments to the program. Recall that our goal is to compute the hash for the number `5`. Consequently we set `a`, `b` and `c` to `0` and  `d` to  `5`.

Still here? Great! At this point, we can check the `witness` file for the return values:

```sh
grep '~out' witness
```

which should lead to the following output:

```sh
~out_0 263561599766550617289250058199814760685
~out_1 65303172752238645975888084098459749904
```

Hence, by concatenating the outputs as 128 bit numbers, we arrive at the following value as the hash for our selected pre-image :
`0xc6481e22c5ff4164af680b8cfaa5e8ed3120eeff89c4f307c4a6faaae059ce10`

## Prove knowledge of pre-image

For now, we have seen that we can compute a hash using ZoKrates.

Let's recall our goal: Peggy wants to prove that she knows a preimage for a digest chosen by Victor, without revealing what the preimage is. Without loss of generality, let's now assume that Victor chooses the digest to be the one we found in our example above.

To make it work, the two parties have to follow their roles in the protocol:

First, Victor has to specify what hash he is interested in. Therefore, we have to adjust the zkSNARK circuit, compiled by ZoKrates, such that in addition to computing the digest, it also validates it against the digest of interest, provided by Victor. This leads to the following update for `hashexample.zok`:

```zokrates
{{#include ../../zokrates_cli/examples/book/hashexample_updated.zok}}
```

Note that we now compare the result of `sha256packed` with the hard-coded correct solution defined by Victor. The lines which we added are treated as assertions: the verifier will not accept a proof where these constraints were not satisfied. Clearly, this program only returns 1 if all of the computed bits are equal.

So, having defined the program, Victor is now ready to compile the code:

```sh
./zokrates compile -i hashexample.zok
```

Based on that Victor can run the setup phase and export a verifier smart contract as a Solidity file:

```sh
./zokrates setup
./zokrates export-verifier
```

`setup` creates a `verifiation.key` file and a `proving.key` file. Victor gives the proving key to Peggy.

`export-verifier` creates a `verifier.sol` contract that contains our verification key and a function `verifyTx`. Victor deploys this smart contract to the Ethereum network.

Peggy provides the correct pre-image as an argument to the program.

```sh
./zokrates compute-witness -a 0 0 0 5
```

Finally, Peggy can run the command to construct the proof:

```sh
./zokrates generate-proof
```

As the inputs were declared as private in the program, they do not appear in the proof thanks to the zero-knowledge property of the protocol.

ZoKrates creates a file, `proof.json`,  consisting of the three elliptic curve points that make up the zkSNARKs proof. The `verifyTx` function in the smart contract deployed by Victor accepts these three values, along with an array of public inputs. The array of public inputs consists of:

* any public inputs to the main function, declared without the `private` keyword
* the return values of the ZoKrates function

In the example we're considering, all inputs are private and there is a single return value of `1`, hence Peggy has to define her public input array as follows: `[1]`.

Peggy can then submit her proof by calling `verifyTx`.

Victor monitors the verification smart contract for the return value of Peggy's transaction. As soon as he observes a transaction from Peggy's public address with a `true` return value, he can be sure that she has a valid pre-image for the hash he set in the smart contract.

## Conclusion

At this point, you've successfully ran you first zkSNARK on the Ethereum blockchain. Congratulations!

>Remember that in this example only two parties were involved. This special case makes it easy to deal with the trust assumptions of zkSNARKs: only Victor was interested in verifying the claim by Peggy, hence he can trust his execution of the setup phase.
>
>In general, multiple parties may be interested in verifying the correctness of Peggy's statement. For example, in the zero-knowledge based cryptocurrency Zcash, each node needs to be able to validate the correctness of transactions. In order to generalize the setup phase to these multi-party use-cases a tricky process, commonly referred to as "trusted setup" or "ceremony" needs to be conducted.
>
>ZoKrates would welcome ideas to add support for such ceremonies!
