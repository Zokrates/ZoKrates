## Functions

Functions are declared using the `def` keyword. A function's signature has to be explicitly provided. 
Its arguments are type annotated, just like variables, and, if the function returns a value, 
the return type must be specified after an arrow `->`. 

A function has to be declared at the top level before it is called.

```zokrates
{{#include ../../../zokrates_cli/examples/book/function_declaration.zok}}
```

A function can be generic over any number of values of type `u32`.

```zokrates
{{#include ../../../zokrates_cli/examples/book/generic_function_declaration.zok}}
```

The generic parameters can be provided explicitly, especially when they cannot be inferred.

```zokrates
{{#include ../../../zokrates_cli/examples/book/explicit_generic_parameters.zok}}
```

If the return type of a function is the empty tuple `()`, the return type as well as the return statement can be omitted.

```zokrates
{{#include ../../../zokrates_cli/examples/book/no_return.zok}}
```