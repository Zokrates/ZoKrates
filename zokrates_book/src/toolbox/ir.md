# ZIR

ZIR is the intermediate representation ZoKrates uses to represent programs. It is close to R1CS but still encapsulates witness generation.

**Note that ZIR is still in development and can change without notice.**

## Serialisation

ZIR programs are serialised with the following format:

| Fields | Length in bytes | Description |
| -------- | -------- | -------- |
| Magic     | 4     | `ZOK` in ASCII, right-padded by 0: `0x5a4f4b00`     |
| Version     | 4     | This format's version, as a big endian number: `0x00000001`     |
| Field size     | 4     | The first 4 bytes of `sha256(FIELD_MODULUS)`: `0xb4f7b5bd` for bn128 for example    |
| Program     | n     | The [`bincode`](https://docs.rs/bincode/1.1.4/bincode/)-encoded program    |

## Display

When generating R1CS constraints, very large numbers are often used, which can make reading ZIR hard for humans.
To mitigate this, ZIR applies an isomorphism when displaying field elements: they are shown as members of the interval `[- (p - 1)/2, (p - 1)/2]`. In other words, the following mapping is used:
- elements in `[0, (p - 1)/2]` map to themselves
- elements in `[(p + 1)/2, p - 1]` map to themselves minus `p`

Therefore, instead of writing `p - 1` as:
```
21888242871839275222246405745257275088548364400416034343698204186575808495616
```
... in ZIR, we simply write:
```
-1
```
