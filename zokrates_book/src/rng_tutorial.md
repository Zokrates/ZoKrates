# Tutorial: Zero Knowledge Proofs for a Random Number Generator

## Prerequisites

Make sure you have followed the instructions in the [Getting Started](gettingstarted.md) chapter and are able to run the "Hello World" example described there.

## Description of the problem

We have two users, Alice and Bob, who want to have a random number generator so they can bet with each other. Each time they just need a single random
bit. However, they don't trust each other and want to make sure the other user can't influence the chosen value.

One way for them to do this is for each of them to commit to a 512 bit value by sending a hash. Then, they can reveal the 0th bit, the 1st bit, etc. The RNG value for 
each bit is *RNG<sub>n</sub>=ALICE<sub>n</sub> &oplus; BOB<sub>n</sub>*, so neither of them can know in advance what each bit will be. They can use the first 384 bits,
and when they get down to 128 bits commit to a new value because it is getting too easy to brute force the hash value.

In this tutorial you learn how to use Zokrates and zero knowledge proofs to reveal a single bit from the preimage of a hash value.

## Calculate the hash (so you can commit to it)

The first step is for Alice and Bob to each come up with a 512 bit value and calculate the hash to commit to it. There are many ways to calculate a hash,
but here we use Zokrates. 

1. Create this file under the name `get_hash.zok`:
```javascript
// Ori Pomerantz qbzzt1@gmail.com

import "hashes/sha256/512bit" as sha256

def main(private u32[16] hashMe) -> u32[8]:
  u32[8] h = sha256(hashMe[0..8], hashMe[8..16])
  return h
```
2. Compile the program to a form that is usable for zero knowledge proofs. This command writes 
the binary to `get_hash`. You can see a textual representation, somewhat analogous to assembler 
coming from a compiler, at `get_hash.ztf` if you remove the `--light` command line option.
```
zokrates compile -i get_hash.zok -o get_hash --light
```
3. The input to the Zokrates program is sixteen 32 bit values, each in decimal. specify those values 
to get a hash. For example, to calculate the hash of `0x000000000000000100000002000000030000000400000005000000060000000700000008000000090000000a0000000b0000000c0000000d0000000e0000000f`
use this command:
```
zokrates compute-witness --light -i get_hash -a 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15
```
The result is:
```
Computing witness...

Witness:

["3592665057","2164530888","1223339564","3041196771","2006723467","2963045520","3851824201","3453903005"]
```

Pick you own value and store it somewhere.

### Detailed explanation

This is the way you put comments in the code 
```javascript
// Ori Pomerantz qbzzt1@gmail.com
```

This line imports a Zokrates function from the standard library. 
[You can see the standard library here](https://github.com/Zokrates/ZoKrates/tree/master/zokrates_stdlib/stdlib). 
You can see the specific function we are importing 
[here](https://github.com/Zokrates/ZoKrates/blob/master/zokrates_stdlib/stdlib/hashes/sha256/512bit.zok). It will be
called `sha256`.
```javascript
import "hashes/sha256/512bit" as sha256
```

This is the main function. The input (`u32[16]`) is an array of sixteen values, each an unsigned 32-bit integer (a number 
between 0 and 2<sup>32</sup>-1). As you have seen above, you specify these numbers using the `-a` command
line parameter. The total number of input bits is *32 &times; 16 = 512*.

The input is `private`, meaning it will not be part of the output. This will be relevant
later when we actually create zero knowledge proofs.

The output is `u32[8]`, a *32 &times; 8 = 256* bit value.

```javascript
def main(private u32[16] hashMe) -> u32[8]:
```

This line does several things. First, `u32[8] h` defines a variable called `h`, whose type is an array of eight 32-bit unsigned integers.
To get the value of this variable, we call `sha256`, the function we 
[imported from the standard library](https://github.com/Zokrates/ZoKrates/blob/master/zokrates_stdlib/stdlib/hashes/sha256/512bit.zok).
The `sha256` function expects to get two arrays of eight values each, so we use a [slice `..`](https://zokrates.github.io/language/types.html#slices)
to divide `hashMe` into two arrays.

```javascript
  u32[8] h = sha256(hashMe[0..8], hashMe[8..16])
```

Finally, return `h` to the caller to display the hash.

```javascript
  return h
```


## Reveal a single bit

The next step is to reveal a single bit.

1. Use this program, `reveal_bit.zok`:
```javascript
// Ori Pomerantz qbzzt1@gmail.com

import "hashes/sha256/512bit" as sha256
import "EMBED/u32_to_bits" as u32_to_bits

// Reveal a bit from a 512 bit value, and return it with the corresponding hash
// for that value.
//
// WARNING, once enough bits have been revealed it is possible to brute force
// the remaining secret bits.

def main(private u32[16] secret, field bitNum) -> (u32[8], bool):
                                                                                                                       
  // Convert the secret to bits
  bool[512] secretBits = [false; 512]
  for field i in 0..16 do
    bool[32] val = u32_to_bits(secret[i])
    for field bit in 0..32 do
      secretBits[i*32+bit] = val[bit]
    endfor
  endfor

  return sha256(secret[0..8], secret[8..16]), secretBits[bitNum]
```

2. Compile and run as you did the previous program:
```bash
zokrates compile -i reveal_bit.zok -o reveal_bit --light
zokrates compute-witness --light -i reveal_bit -a 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 510
```
3. The output should be similar to:
```
Witness:

["3592665057","2164530888","1223339564","3041196771","2006723467","2963045520","3851824201","3453903005","1"]
```


### Detailed explanation (of the new parts)

This function converts a `u32` value to an array of 32 booleans. There are embedded functions to convert `u8`s, 
`u16`s, and `u32`s to boolean arrays and back again (`u32_from_bits`, etc.).

```javascript
import "EMBED/u32_to_bits" as u32_to_bits
```

Note that `u32_to_bits` is going to be added to the standard library soon, and you'll import it as 
`stdlib/u32_to_bits`.

A Zokrates function can return multiple values. In this case, it returns the hash and a boolean which is the 
value of the bit being revealed.

```javascript
def main(private u32[16] secret, field bitNum) -> (u32[8], bool):
```

To find the value of the bit being revealed, we convert the entire secret value into bits and then find it in
the array. In a normal programming environment that would be a *very inefficient* algorithm when we can just
find the word and bit and set a value to that. However, Zokrates is not a normal programming environment.
Instead of machine languages, it compiles to a list of equations. This limits our ability to do some operations
that are very simple in a normal language.

The first line defines an array of 512 boolean values (`bool[512]`) called `secretBits`. It is initialized to
an array of 512 `false` values. The syntax `[<value>; <number>]` initializes the an array of `<number>` 
copies of `<value>`. It is necessary to include it here because a Zokrates variable must be initialized
when it is declared.

```javascript
  // Convert the secret to bits
  bool[512] secretBits = [false; 512]
```

This is a [for loop](https://zokrates.github.io/language/control_flow.html#for-loops). For loops 
have to have an index of type `field`, and fixed boundaries that are known at compile time. 
In this case, we go over each of the sixteen 32 bit words.
```javascript
  for field i in 0..16 do
```

The function we imported, `u32_to_bits`, converts a `u32` value to an array of bits. We store the value
to avoid having to run this function 32 times.

```javascript
    bool[32] val = u32_to_bits(secret[i])
```

The inner loop copies the bits from `val` to the 512 bit array.

```javascript
    for field bit in 0..32 do
      secretBits[i*32+bit] = val[bit]
```

We use `endfor` to end a for loop.

```javascript
    endfor
  endfor
```

To return multiple values, separate them by commas. 

```javascript
  return sha256(secret[0..8], secret[8..16]), secretBits[bitNum]
```



## Actually using zero knowledge proofs

The `reveal_bit.zok`program reveals a bit from the preimage, but who runs it?

1. If Alice runs the program, she can feed it her secret preimage and receive the correct result. However, when she sends the output there is no reason
   for Bob to trust that she is providing the correct output.
2. If Bob runs the program, he does not have Alice's secret preimage. If Alice discloses her secret preimage, Bob can know the value of all the bits.

So we need to have Alice run the program and produce the output, but produce it in such a way Bob will know it is the correct output. This is what Zero Knowledge
Proofs give us.

### Set up the environment

1. Create two separate directories, `alice` and `bob`. You will perform the actions of Alice in the `alice` directory,
   and the Bob actions in the `bob` directory.
   
### Bob's setup stage

2. Compile `reveal_bit.zok` and create the proving and verification keys.
   ```
   zokrates compile -i reveal_bit.zok -o reveal_bit --light
   zokrates setup -i reveal_bit
   ```
3. Copy the file `proving.key` to Alice's directory.

### Alice reveals a bit

4. Alice should compile `reveal_bit.zok` independently to make sure it doesn't disclose information she wants to keep a secret.
   ```
   zokrates compile -i reveal_bit.zok -o reveal_bit --light
   ```   
   
5. Next, Alice creates the `witness` file with the values of all the parameters in the program, and out of it generates a 
   proof with Bob's `proving.key`
   ```
   zokrates compute-witness -i reveal_bit -a 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 510 --light
   zokrates generate-proof -i reveal_bit
   ``` 
   
6. The proof is created in the file `proof.json`. Copy this file to Bob's directory.

### Bob accepts the proof

7. Finally, Bob verifies the proof:
   ```
   zokrates verify
   ```
   
8. As a sanity check, modify `proof.json` to an invalid value and see that the verification fails.


## Connecting to Ethereum

So far Alice and Bob calculated the random bit between themselves. However, it is often useful to have the values
published on the blockchain. To do this, Bob creates a Solidity program:

```
zokrates export-verifier
```

The Solidity program is called `verifier.sol`. The exact mechanism to run it depends on your Ethereum development environment. 
Here is how you do it using the [HardHat](https://hardhat.org/) environment:

1. Install the environment [as explained here](https://hardhat.org/tutorial/setting-up-the-environment.html)
2. In a new project directory, install and initialize HardHat:
   ```
   npm init --yes
   npm install --save-dev hardhat
   npx hardhat 
   ```
   In the last step, choose **Create an empty hardhat.config.js**.
3. Install some HardHat plugins we'll use:
   ```
   npm install --save-dev @nomiclabs/hardhat-ethers ethers @nomiclabs/hardhat-waffle ethereum-waffle chai
   ```
4. Create a `contracts` directory and copy `verifier.sol` to `<project directory>/contracts/verifier.sol`.
5. Get the version of Solidity required for the project:
   ```
   grep "pragma solidity" contracts/verifier.sol
   ```
6. Edit `hardhat.config.js`:
   * Add this line at the top:
     ```
     require("@nomiclabs/hardhat-waffle")
     ```
   * Use the version of Solidity required for the verifier (0.6.1 at writing).
7. Compile the verifier:
   ```
   npx hardhat compile
   ```
   
