# Proving Knowledge of a Hash Pre-Image

Let’s jump into ZoKrates by working through a hands-on project together! This chapter introduces you to the basic features of ZoKrates and how to use zkSNARKs in a real-world example.

We’ll implement a problem that's very typical in blockchain use-cases: proving the knowledge of a pre-image for a given hash digest.  
In particular, we show how ZoKrates and the Ethereum blockchain can be used to allow a prover, let’s call her Peggy, to demonstrate beyond any reasonable doubt to a verifier, let’s call him Victor, that she knows a hash pre-image for a chosen digest by Victor, without revealing what the pre-image is.

## Pre-requisites

Make sure you have followed the instructions in the [Getting Started](gettingstarted.md) chapter and are able to run the "Hello World" example described there.

## Computing a Hash using ZoKrates

We will start this tutorial by using ZoKrates to compute the hash-digest for an arbitrarily chosen pre-image, being the number `5` in this example.

First, we create a new file named `hashexample.code` with the following content:

```zokrates
import "LIBSNARK/sha256packed"

def main(private field a, private field b) -> (field):
	c = sha256packed(a, b)
	return c
```

Clearly, the first line imports the `sha256packed` function from the ZoKrates standard library.
`sha256packed` is a SHA256 implementation that is optimized for the use in the ZoKrates DSL. The function takes 2 field elements as inputs. A `field` value, however, can only hold 254 bits due to the size of the underlying prime field used for elliptic-curve computation. As a consequence, the function unpacks each field element to its 254 bits and pads `00` on the left to obtain the required 256 bits. The two elements are then concatenated and a full SHA256 round on the 512 bits input is computed. Given that the resulting SHA256 hash-digest is 256 bit long the two most significant bits get removed and then the result is packed to a field element again. In case you are interested in an example that is fully compliant with existing SHA256 implementations in Python or Solidity you can have a look at this [blog](https://blog.decentriq.ch/proving-hash-pre-image-zksnarks-zokrates) post.

After this small detour let's go through the rest of the code:
The `main` function takes two private input arguments which are used to call the imported `sha256packed` function. In addition, we declare a field element `c` which is set to output of the hash function and gets returned from the program.

Having our problem described in ZoKrates' DSL, we can now continue using ZoKrates for the rest of our workflow.

First, we compile the program into an arithmetic circuit using the `compile` command.

```sh
./zokrates compile -i hashexample.code
```

As a next step we can create a witness file using the following command:

```sh
./zokrates compute-witness -a 0 5
```

Using the flag `-a` we can set the input arguments of the program. Recall that our goal is to compute the hash for the number `5`. Consequently we set `a` to `0` and  `b` to  `5`.

Still here? Great! At this point, we can check the `witness` file for the return value:

```sh
grep '~out_0' witness
```

which should lead to the following output:

```sh
~out_0 2841298070043759859224314537332116230625666178017083621071552164634727927312
```

Hence, we finally arrive at the following field value as the hash-digest for our selected pre-image :
`2841298070043759859224314537332116230625666178017083621071552164634727927312`

## Prove knowledge of pre-image

At this point you might be wondering how all of this is useful. For now, we have seen that we can compute a hash using heavy finite field arithmetic on elliptic curves using ZoKrates.

Let's recall our goal: Peggy wants to proof that she knows a pre-image for a digest chosen by Victor, without revealing what the pre-image is. Without loss of generality, let's now assume that Victor choses the digest to be equivalent to our example above.  

To make it work, the two parties have to follow their roles in the protocol:

First, Victor has to specify what hash digest he is interested in. Therefore, we have to adjust the zkSNARK circuit, compiled by ZoKrates, such that in addition to computing the digest, it also validates it against the digest of interest, provided by Victor. This leads to the following update for `hashexample.code`:

```zokrates
import "LIBSNARK/sha256packed"

def main(private field a, private field b) -> (field):
	c = sha256packed(a, b)
	c == 2841298070043759859224314537332116230625666178017083621071552164634727927312
	return 1
```

Not that we now compare the result of `sha256packed` with the hard-coded correct solution defined by Victor. Clearly, this program only returns true if all of the computed bits are equivalent.

So, having defined the program Victor is now ready to compile the code:

```sh
./zokrates compile -i hashexample.code
```

Based on that Victor can run the setup phase and export the Solidity verifier smart contract:

```sh
./zokrates setup
./zokrates export-verifier
```

`setup` will create a `verifiation.key` file and a `proving.key` file. Victor must make the `proving.key` publicly available to Alice.

`export-verifier` creates a `verifier.sol` Solidity contract file that contains our verification key and a nifty function `verifyTx`. Victor deploys this smart contract to the Ethereum network.

Alice uses the `proving.key` to compute a witness to the problem:

```sh
./zokrates compute-witness -a 0 5
```

Note that Alice provides the correct pre-image as an argument to the program. However, these inputs are declared as private variables in the program  and don't leak to Victor due to the zero knowledge aspect of the protocol.

Finally, Alice can run the command to construct the proof:

```sh
./zokrates generate-proof
```

ZoKrates creates a file, `proof.json`,  consisting of the eight variables that make up the zkSNARKs proof. The `verifyTx` function in the smart contract deployed by Victor accepts these eight values, along with an array of public inputs. The array of public inputs consists of:

* any parameters in the ZoKrates function, which do not contain the `private` keyword
* the return value(s) of the ZoKrates function

In the example we're considering, all inputs are private and there is a single return value of `1`, hence Alice has to define her public input array as follows: `[1]`  

Victor is continuously monitoring the verification smart contract for the `Verified` event, which is emitted upon successful verification of a transaction. As soon as he observes the event triggered by a transaction from Alice's public address, he can be sure that Alice has a valid pre-image for the hash-digest he has put into the smart contract.

## Summary

At this point, you’ve successfully ran you first zkSNARK on the Ethereum blockchain! Congratulations!  

This project was a hands-on way to introduce you to ZoKrates and the workflow to develop dApps using zkSNARKs.  

Remember that in this example only two parties have been involved. This special case makes it easy to deal with zkSNARK's trust assumptions: only Vitor was interested in verifying the claim by Alice, hence he can trust his execution of the setup phase.

However, in more general use-cases there might be multiple parties interested in verifying the correctness of Alice's statement. For example, in the zero-knowledge based cryptocurrency Zcash every node needs to be able to validate the correctness of transactions. In order to generalize the setup phase to these multi-party use-cases a tricky process, commonly referred to as “trusted setup” or "ceremony" needs to be conducted.

Currently, ZoKrates doesn't provide support for these types of setups. 