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

Functions can return multiple values by providing them as a comma-separated list.

```zokrates
{{#include ../../../zokrates_cli/examples/book/multi_return.zok}}
```

### Inference

When defining a variable as the return value of a function, types are provided when the variable needs to be declared:

```zokrates
{{#include ../../../zokrates_cli/examples/book/multi_def.zok}}
```