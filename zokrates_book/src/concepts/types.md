## Types

ZoKrates currently exposes three types:

### `field`

This is the most basic type in ZoKrates, and it represents a positive integer between `0` and `p - 1`, where `p` is a (large) prime number.

The prime `p` is set to `21888242871839275222246405745257275088548364400416034343698204186575808495616` as imposed by the pairing curve supported by Ethereum.

While `field` values mostly behave like unsigned integers, one should keep in mind that they overflow at `p` and not some power of 2 and underflow at 0, so that we have:

```zokrates
def main() -> (field):
    field p_minus_one = 21888242871839275222246405745257275088548364400416034343698204186575808495616
    0 - 1 == p_minus_one
    return 1
```

### `bool`

ZoKrates has limited support for booleans, to the extent that they can only be used as the condition in `if ... else ... endif` expressions.

You can use them for equality checks, inequality checks and inequality checks between `field` values.

Note that while equality checks are cheap, inequality checks should be use wisely as they are orders of magnitude more expensive.

### `field[n]`

Static arrays of `field` can be instantiated with a constant size, and their elements can be accessed and updated:

```zokrates
def main() -> (field):
    field[3] a = [1, 2, 3]
    a[2] = 4
    return a[0] + a[2]
```