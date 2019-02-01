# ZIR

ZIR is the intermediate representation ZoKrates uses to represent programs. It is close to R1CS but still encapsulates witness generation.

**Note that ZIR is still in development and can change without notice.**

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
