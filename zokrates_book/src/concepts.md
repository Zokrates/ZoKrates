# ZoKrates Programming Concepts

## Variables

Variables can have any name which does not start with a number. Underscores are not allowed in variable names.

## Types

ZoKrates currently exposes three types:

### `field`

This is the most basic type in ZoKrates, and it represents a positive integer between `0` and `p - 1`, where `p` is a (large) prime number.

The prime `p` is set to `21888242871839275222246405745257275088548364400416034343698204186575808495616` as imposed by the pairing curve supported by Ethereum.

While `field` values mostly behave like unsigned integers, there are some things to keep in mind:

- They overflow at p and not some power of 2 and underflow at 0, so that we have:

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

## Comments

Comments can be added with double-slashes.

```zokrates
def main() -> (field):
    field a = 42 // this is an end of line comment
    // this is a full line comment
    return a
```

## Functions

A function has to be declared at the top level before it is called.

```zokrates
def foo() -> (field):
    return 1

def bar() -> (field):
    return foo()
```

A function's signature has to be explicitely provided.
Functions can return many values simply by providing them as a comma-separated list.

```zokrates
def main() -> (field, field[3]):
    return 1, [2, 3, 4]
```

### Inference

When defining a variable as the return value of a function, types are optional:

```zokrates
def foo() -> (field, field):
    return 21, 42

def main() -> (field):
    a, b = foo()
    return 1
```

If there is an ambiguity, providing the types of some of the assigned variables is necessary.

```zokrates
def foo() -> (field, field[3]):
    return 1, [2, 3, 4]

def foo() -> (field, field):
    return 1, 2

def main() -> (field):
    a, field[3] b = foo()
    return 1
```

## Control Flow

ZoKrates provide a single thread of execution with two control flow constructs.

### Function calls

Function calls can help make programs clearer and more modular. However, using function calls is not always zero-cost, so deep call chains should be avoided.
Arguments are always passed by value, so that no side effects inside the callee will be visible to the caller.

```zokrates
def incr(field a) -> (field)
    a = a + 1
    return 1

def main() -> (field):
    field x = 1
    field res = incr(x)
    x == 1 // x has not changed
    return 1
```

### For loops

For loops are available with the following syntax:

```zokrates
def main() -> (field):
    field res = 0
    for field i in 0..4 do
        res = res + i
    endfor
    return res
```

The bounds have to be known at compile time, so only constants are allowed.
For loops have define their own scope.

## Standard library

ZoKrates comes with a number of reusable components. For now, these components are:

### sha256

```zokrates
import "LIBSNARK/sha256"
```

A function that takes 512 field elements as inputs, checks that they are all bits, and returns their sha256 hash as 256 field elements.

### sha256compression

```zokrates
import "LIBSNARK/sha256compression"
```

A function that takes 512 field elements as inputs, checks that they are all bits, and returns the result of applying the sha256 compression function on them. The difference with `sha256` is that no padding is added at the end of the message, which makes it more efficient but also less compatible with Solidity.

### sha256packed

```zokrates
import "LIBSNARK/sha256packed"
```

A function that takes 2 field elements as inputs, unpacks each of them to 254 bits (big endian), pads each of them to 256 bits on the left, concatenates them and applies sha256. It then removes the two most significant bits and returns the rest as one field element. The rationale is that one `field` value can only hold 254 bits due to the size of `p`.

### pack254

```zokrates
import "PACKING/pack254"
```

Packs 254 field elements as one.

### unpack254

```zokrates
import "PACKING/unpack254"
```

Unpacks a field element to 254 field elements.