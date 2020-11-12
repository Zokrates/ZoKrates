# Tutorial: A SNARK Powered RNG

## Prerequisites

Make sure you have followed the instructions in the [Getting Started](gettingstarted.md) chapter and are able to run the "Hello World" example described there.

## Description of the problem

Alice and Bob want to bet on the result of a series of coin tosses. To do so, they need to generate a series of random bits. They proceed as follows:

1. Each of them commits to a 512 bit value. Let’s call this value the ***preimage***. They publish the hash of the preimage.
2. Each time they need a new random value, they reveal one bit from their preimage, and agree that the new random value is the result of XORing these 
   two bits, so that neither of them can control the output.

Note that We are making a few assumptions here:

1. They make sure they do not use all 512 bits of their preimage, as the more they reveal, the easier it gets for the other to brute-force their preimage.
2. They need a way to be convinced that the bit the other revealed is indeed part of their preimage. 

In this tutorial you learn how to use Zokrates and zero knowledge proofs to reveal a single bit from the preimage of a hash value.

## Commit to a preimage

The first step is for Alice and Bob to each come up with a preimage value and calculate the hash to commit to it. There are many ways to calculate a hash,
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
to get a hash. For example, to calculate the hash of `0x00000000000000010000000200000003000000040000000500000006...`
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

Pick your own value and store it somewhere.

### Detailed explanation

This is the way you put comments in the code 
```javascript
// Ori Pomerantz qbzzt1@gmail.com
```

&nbsp;

This line imports a Zokrates function from the standard library. 
[You can see the standard library here](https://github.com/Zokrates/ZoKrates/tree/master/zokrates_stdlib/stdlib). 
You can see the specific function we are importing 
[here](https://github.com/Zokrates/ZoKrates/blob/master/zokrates_stdlib/stdlib/hashes/sha256/512bit.zok). It will be
called `sha256`.
```javascript
import "hashes/sha256/512bit" as sha256
```

&nbsp;

This is the main function. The input (`u32[16]`) is an array of sixteen values, each an unsigned 32-bit integer (a number 
between 0 and 2<sup>32</sup>-1). As you have seen above, you specify these numbers using the `-a` command
line parameter. The total number of input bits is *32 &times; 16 = 512*.

The input is `private`, meaning it will not be revealed to the verifier. This will be relevant
later when we actually create zero knowledge proofs.

The output is `u32[8]`, a *32 &times; 8 = 256* bit value.

```javascript
def main(private u32[16] hashMe) -> u32[8]:
```

&nbsp;

This line does several things. First, `u32[8] h` defines a variable called `h`, whose type is an array of eight 32-bit unsigned integers.
This variable is initialized using `sha256`, the function we 
[imported from the standard library](https://github.com/Zokrates/ZoKrates/blob/master/zokrates_stdlib/stdlib/hashes/sha256/512bit.zok).
The `sha256` function expects to get two arrays of eight values each, so we use a [slice `..`](https://zokrates.github.io/language/types.html#slices)
to divide `hashMe` into two arrays.

```javascript
  u32[8] h = sha256(hashMe[0..8], hashMe[8..16])
```

&nbsp;

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
import "utils/casts/u32_to_bits" as u32_to_bits

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

This function converts a `u32` value to an array of 32 booleans. There are cast functions to convert `u8`s, 
`u16`s, and `u32`s to boolean arrays and back again, 
[you can see them here](https://github.com/Zokrates/ZoKrates/blob/master/zokrates_stdlib/stdlib/utils/casts).

```javascript
import "utils/casts/u32_to_bits" as u32_to_bits
```

&nbsp;

A Zokrates function can return multiple values. In this case, it returns the hash and a boolean which is the 
value of the bit being revealed.

```javascript
def main(private u32[16] secret, field bitNum) -> (u32[8], bool):
```

&nbsp;

To find the value of the bit being revealed, we convert the entire preimage into bits and then find it in
the array. The first line defines an array of 512 boolean values (`bool[512]`) called `secretBits`. It is initialized to
an array of 512 `false` values. The syntax `[<value>; <number>]` initializes the an array of `<number>` 
copies of `<value>`. It is necessary to include it here because a Zokrates variable must be initialized
when it is declared.

```javascript
  // Convert the secret to bits
  bool[512] secretBits = [false; 512]
```

&nbsp;

This is a [for loop](https://zokrates.github.io/language/control_flow.html#for-loops). For loops 
have to have an index of type `field`, and their bounds need to be known at compile time.
In this case, we go over each of the sixteen 32 bit words.
```javascript
  for field i in 0..16 do
```

The function we imported, `u32_to_bits`, converts a `u32` value to an array of bits.

```javascript
    bool[32] val = u32_to_bits(secret[i])
```

&nbsp;

The inner loop copies the bits from `val` to `secretBits` the bit array for the preimage.

```javascript
    for field bit in 0..32 do
      secretBits[i*32+bit] = val[bit]
    endfor
  endfor
```

&nbsp;

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
   zokrates setup -i reveal_bit --light
   ```
3. Copy the file `proving.key` to Alice's directory.

### Alice reveals a bit

4. Alice should compile `reveal_bit.zok` independently to make sure it doesn't disclose information she wants to keep secret.
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
   
8. As a sanity check, modify any of the values in `proof.json` and see that the verification fails.


## Connecting to Ethereum

So far Alice and Bob calculated the random bit between themselves. However, it is often useful to have the values
published on the blockchain. To do this, Bob creates a Solidity program:

```
zokrates export-verifier
```

The Solidity program is called `verifier.sol`. 
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
8. Create a `test` directory. In it place `Verifier.js`:
   ```javascript
   // Ori Pomerantz qbzzt1@gmail.com 
   
   const proofFileName = "/home/qbzzt1/tutorial_zok/alice/proof.json"

   const { expect } = require("chai")
   const fs = require("fs")

   const proof = JSON.parse(fs.readFileSync(proofFileName))


   describe("Verifier should only verify correct submissions", async () => {

      it("Reject random values", async () => {
          const contract = await (await ethers.getContractFactory("Verifier")).deploy()
          const result = await contract.verifyTx(
                 [0,0],           // a
                 [[0,0],[0,0]],   // b
                 [0,0],           // c
                 [1,2,3,4,5,6,7,8,9,10])   // input
          expect(result).to.equal(false)
      })    // it "Reject random values"

      it("Accept valid proofs", async () => {
          const contract = await (await ethers.getContractFactory("Verifier")).deploy()
          const result = await contract.verifyTx(
                 proof.proof.a,
                 proof.proof.b,
                 proof.proof.c,
                 proof.inputs)
          expect(result).to.equal(true)
      })    // it "Accept valid proofs"

      it("Reject cheats", async () => {
          const contract = await (await ethers.getContractFactory("Verifier")).deploy()

          // Try to cheat, create an inputs array that flips the last value,
          // the result bit (the other values are the bit's number and the hash)
          var cheatInputs = [...proof.inputs]
          var resultBit = proof.inputs[proof.inputs.length-1]
          if (resultBit.slice(-1) === '1')
              cheatInputs[proof.inputs.length-1] = 0
           else
              cheatInputs[proof.inputs.length-1] = 1

          const result = await contract.verifyTx(
                 proof.proof.a,
                 proof.proof.b,
                 proof.proof.c,
                 cheatInputs)
          expect(result).to.equal(false)
      })   // it "Reject cheats"
   })      // describe "Verifier..."

   ```
   Remember to change the `proofFileName` definition to point to Alice's `proof.json`.
   
### Detailed Explanation

This is the path to Alice's `proof.json`. Modify it as appropriate to your environment.

```javascript
const proofFileName = "/home/qbzzt1/tutorial_zok/alice/proof.json"
```

[Chai](https://www.chaijs.com/) is an assertion package for JavaScript. [FS](https://nodejs.org/dist/latest-v12.x/docs/api/fs.html)
is the file system package we use to access `proof.json`.

```javascript
const { expect } = require("chai")
const fs = require("fs")
```

Read `proof.json`, and parse it as [JSON](https://www.w3schools.com/js/js_json_parse.asp). 

```javascript
const proof = JSON.parse(fs.readFileSync(proofFileName))
```

The two testing functions we use, `describe` and `it`, are part of the [Mocha](https://mochajs.org/) package. 

```javascript
describe("Verifier should only verify correct submissions", async () => {

  it("Reject random values", async () => {
```

The package we use to talk to the blockchain is [Ethers](https://docs.ethers.io/v5/).
The first step is to create a [Contract object](https://docs.ethers.io/v5/api/contract/contract/),
using this process:

1. Create a [contract factory](https://docs.ethers.io/v5/api/contract/contract-factory/) with the
   name of the contract. This is a relatively long process, so it has to 
   run [asynchronously](https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Asynchronous/Async_await)
   using the `await` keyword.
2. Using that contract factory, `deploy` an instance of the contract itself into the blockchain.

```javascript
     const contract = await (await ethers.getContractFactory("Verifier")).deploy()
```

Verifiers exported by Zokrates have a `verifyTx` function that verifies transactions.

```javascript
     const result = await contract.verifyTx(
```     
   
The proof is composed of four points: *a*, *b[0]*, *b[1]*, and *c*.   
   
```javascript   
             [0,0],           // a
             [[0,0],[0,0]],   // b
             [0,0],           // c
```

In addition, `verifyTx` requires the public inputs and the results from `compute-witness`,
which are used as the input for `generate-proof`.

```javascript
             [1,2,3,4,5,6,7,8,9,10])   // input
```

This is one of the ways to asset a value in Chai. In this case we expect the result
to be `false` because the inputs to `verifyTx` are not valid.

```javascript
     expect(result).to.equal(false)
  })    // it "Reject random values"
```

The next step is to use the values we read from `proof.json` to verify the legitimate
proof.

```javascript
  it("Accept valid proofs", async () => {
```

Every `it` test is supposed to start from scratch, so we deploy the contract again.

```javascript
       const contract = await (await ethers.getContractFactory("Verifier")).deploy()
       const result = await contract.verifyTx(
              proof.proof.a,
              proof.proof.b,
              proof.proof.c,
              proof.inputs)
       expect(result).to.equal(true)
   })    // it "Accept valid proofs"
```

Finally, pretend the Alice tried to cheat by flipping the revealed bit's value.

```javascript
   it("Reject cheats", async () => {
       const contract = await (await ethers.getContractFactory("Verifier")).deploy()

       // Try to cheat, create an inputs array that flips the last value,
       // the result bit (the other values are the bit's number and the hash)
```

This syntax, `[...<array>]`, creates a copy of an array.

```javascript
       var cheatInputs = [...proof.inputs]
```

The last value in `proof.inputs` is the revealed bit. The values in the proof
are all of type `uint`, which is a 256 bit value, so they are represented in JavaScript 
as strings. Because we know the value is a bit, either one or zero, we can just look at
the last character.

```javascript
       var resultBit = proof.inputs[proof.inputs.length-1]
       if (resultBit.slice(-1) === '1')
```

The default representation is a string, but an integer works just as well for values that
fit in an integer.

```javascript
           cheatInputs[proof.inputs.length-1] = 0
        else
           cheatInputs[proof.inputs.length-1] = 1

       const result = await contract.verifyTx(
              proof.proof.a,
              proof.proof.b,
              proof.proof.c,
              cheatInputs)
       expect(result).to.equal(false)
   })   // it "Reject cheats"
})      // describe "Verifier..."

```  
  
## Conclusion

At this point you should know how to use Zokrates to create zero knowledge proofs and verify them from the command
line. You should also be able to publish a verifier to a blockchain, generate proofs from the command line, and submit
them using JavaScript.

However, one important feature is still missing. Users don't typically use the command line when they communicate with 
the blockchain. They use dapps written in JavaScript, so they can do all the processing inside their own browsers without
having to worry about installing software.

I hope to have another tutorial soon that teachs you how to create dapps that use Zokrates and submit proofs to the
blockchain.
