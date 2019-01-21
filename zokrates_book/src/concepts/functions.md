## Functions

A function has to be declared at the top level before it is called.

```zokrates
{{#include ../../../zokrates_cli/examples/book/function_declaration.code}}
```

A function's signature has to be explicitly provided.
Functions can return many values by providing them as a comma-separated list.

```zokrates
{{#include ../../../zokrates_cli/examples/book/multi_return.code}}
```

### Inference

When defining a variable as the return value of a function, types are optional:

```zokrates
{{#include ../../../zokrates_cli/examples/book/multi_def.code}}
```

If there is an ambiguity, providing the types of some of the assigned variables is necessary.

```zokrates
{{#include ../../../zokrates_cli/examples/book/type_annotations.code}}
```