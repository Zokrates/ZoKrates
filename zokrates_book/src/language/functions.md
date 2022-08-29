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

Functions that "don't" return a value, actually return an empty tuple `()`. 
When a function returns an empty tuple `()`, the return type can be omitted from 
the signature. In this case, a return statement can be omitted.