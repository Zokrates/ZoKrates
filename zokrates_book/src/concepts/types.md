# Types

ZoKrates currently exposes two primitive types and two complex types:

## Primitive Types

### `field`

This is the most basic type in ZoKrates, and it represents a positive integer in `[0,  p - 1]` where `p` is a (large) prime number.

The prime `p` is set to `21888242871839275222246405745257275088548364400416034343698204186575808495617` as imposed by the pairing curve supported by Ethereum.

While `field` values mostly behave like unsigned integers, one should keep in mind that they overflow at `p` and not some power of 2, so that we have:

```zokrates
{{#include ../../../zokrates_cli/examples/book/field_overflow.zok}}
```

### `bool`

ZoKrates has limited support for booleans, to the extent that they can only be used as the condition in `if ... else ... endif` expressions.

You can use them for equality and inequality checks between `field` values.

Note that while equality checks are cheap, inequality checks should be used wisely as they are orders of magnitude more expensive.

## Complex Types

ZoKrates provides two complex types, Arrays and Structs.

### Arrays

ZoKrates supports static arrays, i.e., their length needs to be known at compile time.
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
`[value;repetitions]`


The following code provides examples for declaration and initialization:
```zokrates
    field[3] a = [1, 2, 3] // initialize a field array with field values
    bool[13] b = [false; 13] // initialize a bool array with value false
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
field[3] a = [1, 2, 3]
field[4] c = [...a, 4] // initialize an array copying values from `a`, followed by 4
```

##### Slices
An array can also be assigned to by creating a copy of a subset of an existing array.
This operation is called slicing, and the following example shows how to slice in ZoKrates:
```
field[3] a = [1, 2, 3]
field[2] b = a[1..3]   // initialize an array copying a slice from `a`
```

### Structs
A struct is a composite datatype representing a named collection of variables.
The contained variables can be of any type.

The following code shows an example of how to use structs.

```zokrates
{{#include ../../../zokrates_cli/examples/book/structs.code}}
```

#### Definition
Before a struct data type can be used, it needs to be defined.
A struct definition starts with the `struct` keyword followed by a name. Afterwards, a new-line separated list of variables is declared in curly braces `{}`. For example:

```zokrates
struct Point {
	field x
	field y
}
```

#### Declaration and Initialization

Initialization of a variable of a struct type always needs to happen in the same statement as a declaration, unless the struct-typed variable is declared within a function's signature.

The following example shows declaration and initialization of a variable of the `Point` struct type:

```zokrates
{{#include ../../../zokrates_cli/examples/book/struct_init.code}}
```

#### Assignment
The variables within a struct instance, the so called members, can be accessed through the `.` operator as shown in the following extended example:

```zokrates
{{#include ../../../zokrates_cli/examples/book/struct_assign.code}}
```
