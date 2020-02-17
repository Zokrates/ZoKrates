## Functions

A function has to be declared at the top level before it is called.

```zokrates
{{#include ../../../zokrates_cli/examples/book/function_declaration.zok}}
```

A function's signature has to be explicitly provided.
Functions can return many values by providing them as a comma-separated list.

```zokrates
{{#include ../../../zokrates_cli/examples/book/multi_return.zok}}
```

### Inference

When defining a variable as the return value of a function, types are optional:

```zokrates
{{#include ../../../zokrates_cli/examples/book/multi_def.zok}}
```

If there is any ambiguity, providing the types of some of the assigned variables is necessary.

```zokrates
{{#include ../../../zokrates_cli/examples/book/type_annotations.zok}}
```