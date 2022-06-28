## Functions

A function has to be declared at the top level before it is called.

```zokrates
{{#include ../../../zokrates_cli/examples/book/function_declaration.zok}}
```

A function's signature has to be explicitly provided.

A function can be generic over any number of values of type `u32`.

```zokrates
{{#include ../../../zokrates_cli/examples/book/generic_function_declaration.zok}}
```

The generic parameters can be provided explicitly, especially when they cannot be inferred.

```zokrates
{{#include ../../../zokrates_cli/examples/book/explicit_generic_parameters.zok}}
```