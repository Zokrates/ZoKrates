# Types

ZoKrates currently exposes two primitive types and two complex types:

## Primitive Types

### `field`

This is the most basic type in ZoKrates, and it represents a field element with positive integer values in `[0,  p - 1]` where `p` is a (large) prime number.

As an example, `p` is set to `21888242871839275222246405745257275088548364400416034343698204186575808495617` when working with the [ALT_BN128](../toolbox/proving_schemes.md#curves) curve supported by Ethereum.

While `field` values mostly behave like unsigned integers, one should keep in mind that they overflow at `p` and not some power of 2, so that we have:

```zokrates
{{#include ../../../zokrates_cli/examples/book/field_overflow.zok}}
```

Note that [division in the finite field](https://en.wikipedia.org/wiki/Finite_field_arithmetic) behaves differently than in the case of integers.
For field elements, the division operation multiplies the numerator with the denominator's inverse field element. The results coincide with integer divisions for cases with remainder 0, but differ otherwise.

### `bool`

Booleans are available in ZoKrates. When a boolean is used as a parameter of the main function, the program is constrained to only accept `0` or `1` for that parameter. A boolean can be asserted to be true using an `assert(bool)` statement.

### `u8/u16/u32/u64`

Unsigned integers represent positive numbers of the interval `[0, 2 ** bitwidth[`, where `bitwidth` is specified in the type's name, e.g., 32 bits in the case of u32. Their arithmetics are defined modulo `2 ** bitwidth`.

Internally, they use a binary encoding, which makes them particularly efficient for implementing programs that operate on that binary representation, e.g., the SHA256 hash function.

Similarly to booleans, unsigned integer inputs of the main function only accept values of the appropriate range.

The division operation calculates the standard floor division for integers. The `%` operand can be used to obtain the remainder.

### Numeric inference

In the case of decimal literals like `42`, the compiler tries to find the appropriate type (`field`, `u8`, `u16`, `u32` or `u64`) depending on the context. If it cannot converge to a single option, an error is returned. This means that there is no default type for decimal literals.

All operations between literals have the semantics of the inferred type.

```zokrates
{{#include ../../../zokrates_cli/examples/book/numeric_inference.zok}}
```

## Complex Types

ZoKrates provides two complex types: arrays and structs.

### Arrays

ZoKrates supports static arrays, i.e., whose length needs to be known at compile time. For more details on generic array sizes, see [constant generics](../language/generics.md)
Arrays can contain elements of any type and have arbitrary dimensions.

The following example code shows examples of how to use arrays:

```zokrates
{{#include ../../../zokrates_cli/examples/book/array.zok}}
```

#### Declaration and Initialization
An array is defined by appending `[]` to a type literal representing the type of the array's elements.

Initialization always needs to happen in the same statement as a declaration, unless the array is declared within a function's signature.

For initialization, a list of comma-separated values is provided within brackets `[]`.

ZoKrates offers a special shorthand syntax to initialize an array with a constant value:
`[value; repetitions]`


The following code provides examples for declaration and initialization:
```zokrates
field[3] a = [1, 2, 3]; // initialize a field array with field values
bool[13] b = [false; 13]; // initialize a bool array with value false
```

#### Multidimensional Arrays

As an array can contain any type of elements, it can contain arrays again.
There is a special syntax to declare such multi-dimensional arrays, i.e., arrays of arrays.
To declare an array of an inner array, i.e., and an array of elements of a type, prepend brackets `[size]` to the declaration of the inner array.
In summary, this leads to the following scheme for array declarations:
`data_type[size of 1st dimension][size of 2nd dimension]`.
Consider the following example:

```zokrates
{{#include ../../../zokrates_cli/examples/book/multidim_array.zok}}
```

#### Spreads and Slices
ZoKrates provides some syntactic sugar to retrieve subsets of arrays.

##### Spreads
The spread operator `...` applied to an array copies the elements of the existing array.
This can be used to conveniently compose new arrays, as shown in the following example:
```
field[3] a = [1, 2, 3];
field[4] c = [...a, 4]; // initialize an array copying values from `a`, followed by 4
```

##### Slices
An array can also be assigned to by creating a copy of a subset of an existing array.
This operation is called slicing, and the following example shows how to slice in ZoKrates:
```
field[3] a = [1, 2, 3];
field[2] b = a[1..3];   // initialize an array copying a slice from `a`
```

### Tuples
A tuple is a composite datatype representing a numbered collection of values.
The following code shows an example of how to use tuples.

```zokrates
{{#include ../../../zokrates_cli/examples/book/tuples.zok}}
```

In tuple types and values, the trailing comma is optional, unless the tuple contains a single element, in which case it is mandatory.

### Structs
A struct is a composite datatype representing a named collection of values. Structs can be generic over constants, in order to wrap arrays of generic size. For more details on generic array sizes, see [constant generics](../language/generics.md). The contained variables can be of any type.

The following code shows an example of how to use structs.

```zokrates
{{#include ../../../zokrates_cli/examples/book/structs.zok}}
```

#### Definition
Before a struct data type can be used, it needs to be defined.
A struct definition starts with the `struct` keyword followed by a name. Afterwards, a new-line separated list of variables is declared in curly braces `{}`. For example:

```zokrates
struct Point {
    field x;
    field y;
}
```

Note that two struct definitions with the same members still introduce two entirely different types. For example, they cannot be compared with each other.

#### Declaration and Initialization

Initialization of a variable of a struct type always needs to happen in the same statement as a declaration, unless the struct-typed variable is declared within a function's signature.

The following example shows declaration and initialization of a variable of the `Point` struct type:

```zokrates
{{#include ../../../zokrates_cli/examples/book/struct_init.zok}}
```

#### Assignment
The variables within a struct instance, the so called members, can be accessed through the `.` operator as shown in the following extended example:

```zokrates
{{#include ../../../zokrates_cli/examples/book/struct_assign.zok}}
```

### Type aliases

Type aliases can be defined for any existing type. This can be useful for readability, or to specialize generic types.

Note that type aliases are just syntactic sugar: in the type system, a type and its alias are exactly equivalent. For example, they can be compared.

```zokrates
{{#include ../../../zokrates_cli/examples/book/type_aliases.zok}}
```
