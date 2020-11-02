# Tutorial: Using Hash and Zero Knowledge Proofs for a Random Number Generator

## Pre-requisites

Make sure you have followed the instructions in the [Getting Started](gettingstarted.md) chapter and are able to run the "Hello World" example described there.

## Description of the problem

We have two users, Alice and Bob, who want to have a random number generator so they can bet with each other. However, they don't trust each other
and want to make sure the other user can't influence the chosen value.

One way for them to do this is for each of them to commit to a 512 bit value by sending a hash. Then, they can reveal the 0th bit, the 1st bit, etc. The RNG value for 
each bit is *RNG<sub>n</sub>=ALICE<sub>n</sub> &oplus; BOB<sub>n</sub>*, so neither of them can know in advance what each bit will be. They can use the first 384 bits,
and when they get down to 128 bits commit to a new value because it is getting too easy to brute force the hash value.

In this tutorial you learn how to use Zokrates and zero knowledge proofs to reveal a single bit from the preimage of a hash value.

## Calculate the hash (so you can commit to it)

```
// Ori Pomerantz qbzzt1@gmail.com

import "hashes/sha256/512bit" as sha256

def main(private u32[16] hashMe) -> u32[8]:
  u32[8] h = sha256(hashMe[0..8], hashMe[8..16])
  return h
```

### Detailed explanation



## Reveal a single bit

```
// Ori Pomerantz qbzzt1@gmail.com

import "hashes/sha256/512bit" as sha256
import "EMBED/u32_to_bits" as u32_to_bits

def main(private u32[16] hashMe, u32[8] hashVal, field bitNum) -> bool:
  bool[512] hashMeBits = [false; 512]
  for field i in 0..16 do
    bool[32] val = u32_to_bits(hashMe[i])
    for field bit in 0..32 do
      hashMeBits[i*32+bit] = val[bit]
    endfor
  endfor
  u32[8] hashCalculated = sha256(hashMe[0..8], hashMe[8..16])
  assert(hashVal == hashCalculated)
  return hashMeBits[bitNum]

// WARNING: After enough bits have been revealed the whole value can be brute
// forced
```

### Detailed explanation


## Putting it all together
