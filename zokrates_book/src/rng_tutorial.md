# Tutorial: Zero Knowledge Proofs for a Random Number Generator

## Prerequisites

Make sure you have followed the instructions in the [Getting Started](gettingstarted.md) chapter and are able to run the "Hello World" example described there.

## Description of the problem

We have two users, Alice and Bob, who want to have a random number generator so they can bet with each other. However, they don't trust each other
and want to make sure the other user can't influence the chosen value.

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
coming from a compiler, at `get_hash.ztf`.
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

```
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

### Detailed explanation


## Putting it all together
