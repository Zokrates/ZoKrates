# Tutorial: A SNARK Powered RNG

## Prerequisites

Make sure you have followed the instructions in the [Getting Started](../gettingstarted.md) chapter and are able to run the "Hello World" example described there.

## Description of the problem

Alice and Bob want to bet on the result of a series of coin tosses. To do so, they need to generate a series of random bits. They proceed as follows:

1. Each of them commits to a 512 bit value. Let’s call this value the ***preimage***. They publish the hash of the preimage.
2. Each time they need a new random value, they reveal one bit from their preimage, and agree that the new random value is the result of XORing these 
   two bits, so that neither of them can control the output.

Note that we are making a few assumptions here:

1. They make sure they do not use all 512 bits of their preimage, as the more they reveal, the easier it gets for the other to brute-force their preimage.
2. They need a way to be convinced that the bit the other revealed is indeed part of their preimage. 

In this tutorial you learn how to use Zokrates and zero knowledge proofs to reveal a single bit from the preimage of a hash value.

## Commit to a preimage

The first step is for Alice and Bob to each come up with a preimage value and calculate the hash to commit to it. 
There are many ways to calculate a hash, but here we use Zokrates. 

Create this file under the name `get_hash.zok`:
```zokrates
{{#include ../../../zokrates_cli/examples/book/rng_tutorial/get_hash.zok}}
```

Compile the program to a form that is usable for zero knowledge proofs. This command writes 
the binary to `get_hash`. You can see a textual representation, somewhat analogous to assembler 
coming from a compiler, at `get_hash.ztf` enabled by the `--ztf` command line option.
```
{{#include ../../../zokrates_cli/examples/book/rng_tutorial/test.sh:10}}
```

The input to the Zokrates program is sixteen 32 bit values, each in decimal. specify those values 
to get a hash. For example, to calculate the hash of `0x00000000000000010000000200000003000000040000000500000006...`
use this command:
```
{{#include ../../../zokrates_cli/examples/book/rng_tutorial/test.sh:11}}
```

The result is:
```
Computing witness...

Witness:

["3592665057","2164530888","1223339564","3041196771","2006723467","2963045520","3851824201","3453903005"]
```

Pick your own value and store it somewhere.

### Detailed explanation
This line imports a Zokrates function from the [standard library](https://github.com/Zokrates/ZoKrates/tree/latest/zokrates_stdlib/stdlib). 
You can see the specific function we are importing 
[here](https://github.com/Zokrates/ZoKrates/blob/latest/zokrates_stdlib/stdlib/hashes/sha256/512bit.zok). It will be
called `sha256`.
```zokrates
{{#include ../../../zokrates_cli/examples/book/rng_tutorial/get_hash.zok:1}}
```

This is the main function. The input (`u32[16]`) is an array of sixteen values, each an unsigned 32-bit integer (a number 
between \(0\) and \(2^{32} - 1\)). As you have seen above, you specify these numbers using the `-a` command
line parameter. The total number of input bits is *32 &times; 16 = 512*.

The output is `u32[8]`, a *32 &times; 8 = 256* bit value.

```zokrates
{{#include ../../../zokrates_cli/examples/book/rng_tutorial/get_hash.zok:3}}
```

This line does several things. First, `u32[8] h` defines a variable called `h`, whose type is an array of eight 32-bit unsigned integers.
This variable is initialized using `sha256`, the function we 
[imported from the standard library](https://github.com/Zokrates/ZoKrates/blob/latest/zokrates_stdlib/stdlib/hashes/sha256/512bit.zok).
The `sha256` function expects to get two arrays of eight values each, so we use a [slice `..`](https://zokrates.github.io/language/types.html#slices)
to divide `hashMe` into two arrays.

```zokrates
{{#include ../../../zokrates_cli/examples/book/rng_tutorial/get_hash.zok:4}}
```

Finally, return `h` to the caller to display the hash.

```zokrates
{{#include ../../../zokrates_cli/examples/book/rng_tutorial/get_hash.zok:5}}
```


## Reveal a single bit

The next step is to reveal a single bit.

Use this program, `reveal_bit.zok`:
```zokrates
{{#include ../../../zokrates_cli/examples/book/rng_tutorial/reveal_bit.zok}}
```

Compile and run as you did the previous program:
```
{{#include ../../../zokrates_cli/examples/book/rng_tutorial/test.sh:27:28}}
```
   
The output should be similar to:
```
Witness:

["3592665057","2164530888","1223339564","3041196771","2006723467","2963045520","3851824201","3453903005","1"]
```


### Detailed explanation

This line imports a function that converts a `u32` value to an array of 32 booleans. 
There are cast functions to convert `u8`s, `u16`s, and `u32`s to boolean arrays and back again, 
[you can see them here](https://github.com/Zokrates/ZoKrates/blob/master/zokrates_stdlib/stdlib/utils/casts).

```zokrates
{{#include ../../../zokrates_cli/examples/book/rng_tutorial/reveal_bit.zok:2}}
```

The preimage is declared `private` so it won't be revealed by the zero knowledge proof.

A Zokrates function can return multiple values. In this case, it returns the hash and a boolean which is the 
value of the bit being revealed.

```zokrates
{{#include ../../../zokrates_cli/examples/book/rng_tutorial/reveal_bit.zok:10}}
```

To find the value of the bit being revealed, we convert the entire preimage into bits and access it at the index `bitNum`. 
The first line defines an array of 512 boolean values (`bool[512]`) called `preimageBits`. It is initialized to
an array of 512 `false` values. The syntax `[<value>; <number>]` initializes the an array of `<number>` 
copies of `<value>`. It is necessary to include it here because a Zokrates variable must be initialized
when it is declared.

```zokrates
{{#include ../../../zokrates_cli/examples/book/rng_tutorial/reveal_bit.zok:11:12}}
```

This is a [for loop](https://zokrates.github.io/language/control_flow.html#for-loops). For loops 
have to have an index of type `u32`, and their bounds need to be known at compile time.
In this case, we go over each of the sixteen 32 bit words.
```zokrates
{{#include ../../../zokrates_cli/examples/book/rng_tutorial/reveal_bit.zok:13}}
```

The function we imported, `u32_to_bits`, converts a `u32` value to an array of bits.

```zokrates
{{#include ../../../zokrates_cli/examples/book/rng_tutorial/reveal_bit.zok:14}}
```

The inner loop copies the bits from `val` to `preimageBits`, the bit array for the preimage.

```zokrates
{{#include ../../../zokrates_cli/examples/book/rng_tutorial/reveal_bit.zok:15:18}}
```

To return multiple values, separate them by commas. 

```zokrates
{{#include ../../../zokrates_cli/examples/book/rng_tutorial/reveal_bit.zok:20}}
```



## Actually using zero knowledge proofs

The `reveal_bit.zok` program reveals a bit from the preimage, but who runs it?

1. If Alice runs the program, she can feed it her secret preimage and receive the correct result. However, when she sends the output there is no reason
   for Bob to trust that she is providing the correct output.
2. If Bob runs the program, he does not have Alice's secret preimage. If Alice discloses her secret preimage, Bob can know the value of all the bits.

Therefore, we need to have Alice run the program and produce the output, but produce it in such a way Bob will know it is the correct output. This is what Zero Knowledge
Proofs give us.

### Set up the environment

Create two separate directories, `alice` and `bob`. You will perform the actions of Alice in the `alice` directory,
and the actions of Bob in the `bob` directory.
   
### Bob's setup stage

Compile `reveal_bit.zok` and create the proving and verification keys.
```
{{#include ../../../zokrates_cli/examples/book/rng_tutorial/test.sh:20:21}}
```

Copy the file `proving.key` to Alice's directory.

### Alice reveals a bit

Alice should compile `reveal_bit.zok` independently to make sure it doesn't disclose information she wants to keep secret.
```
{{#include ../../../zokrates_cli/examples/book/rng_tutorial/test.sh:27}}
```
   
Next, Alice creates the `witness` file with the values of all the parameters in the program. Using this `witness`, 
Bob's `proving.key`, and the compiled program she generates the actual proof.
```
{{#include ../../../zokrates_cli/examples/book/rng_tutorial/test.sh:28:29}}
```
   
The proof is created in the file `proof.json`. Copy this file to Bob's directory.

### Bob accepts the proof

Finally, Bob verifies the proof:
```
{{#include ../../../zokrates_cli/examples/book/rng_tutorial/test.sh:35}}
```
   
As a sanity check, modify any of the values in `proof.json` and see that the verification fails.


## Connecting to Ethereum

So far, Alice and Bob calculated the random bit between themselves. However, it is often useful to have the values
published on the blockchain. To do this, Bob creates a Solidity program:

```
{{#include ../../../zokrates_cli/examples/book/rng_tutorial/test.sh:36}}
```

The Solidity program is called `verifier.sol`. 

Here are the instructions to use this program when using [Truffle and Ganache](https://www.trufflesuite.com/).
We'll assume they are installed, and the Ganache blockchain is running.

1. Create a new project with `truffle init` and copy `verify.sol` to the subdirectory `contracts`.
   
2. Identify the version of Solidity used by `verifier.sol`:
   ```
   grep solidity contracts/verifier.sol
   ```
   
3. Edit `truffle-config.js`:
   * Change `module.exports.compilers.solc.version` to the version required by `verifier.sol`.
   * Uncomment `modules.exports.networks.development`. Make sure you delete the comma after the definition.
   
4. Compile the contract.
   ```
   truffle compile
   ```
   
5. Start the Truffle console. The rest of this procedure is done in the JavaScript prompt inside that console.
   ```
   truffle console
   ```
   
6. Deploy the Verifier contract.
   ```javascript
   contract = await Verifier.new()
   ```
   
7. Read the content of `proof.json`.
   ```javascript
   proof = JSON.parse(fs.readFileSync("path/to/your/proof.json"))
   ```
   
8. Verify the proof. Check that you get the result `true`.
   ```javascript
   await contract.verifyTx(proof.proof.a, proof.proof.b, proof.proof.c, proof.inputs)
   ```
   
9. Pretend to be Alice and try to cheat. Create `cheat` which flips the result
   bit.
   ```javascript
   cheat = [...proof.inputs]
   cheat[cheat.length-1] = cheat[cheat.length-1].replace(/[01]$/, cheat[cheat.length-1][65] == '1' ? '0': '1')
   ```
   
10. As Bob, try to verify a cheating proof, and check that it fails.
    ```javascript
      await contract.verifyTx(proof.proof.a, proof.proof.b, proof.proof.c, cheat)
    ```
  
## Conclusion

At this point you should know how to use Zokrates to create zero knowledge proofs and verify them from the command
line. You should also be able to publish a verifier to a blockchain, generate proofs from the command line, and submit
them using JavaScript.


---------------------------------------------------------------

Original version of this tutorial by Ori Pomerantz qbzzt1@gmail.com
