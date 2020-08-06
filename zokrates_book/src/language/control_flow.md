## Control Flow

ZoKrates provides a single thread of execution with a few flow constructs.

### Function calls

Function calls help make programs clear and modular.

Arguments are passed by value.

```zokrates
{{#include ../../../zokrates_cli/examples/book/side_effects.zok}}
```

### If-expressions

An if-expression allows you to branch your code depending on a boolean condition.

```zokrates
{{#include ../../../zokrates_cli/examples/book/if_else.zok}}
```

### For loops

For loops are available with the following syntax:

```zokrates
{{#include ../../../zokrates_cli/examples/book/for.zok}}
```

The bounds have to be constant at compile-time, therefore they cannot depend on execution inputs.

### Assertions

Any boolean can be asserted to be true using the `assert` function.

```zokrates
{{#include ../../../zokrates_cli/examples/book/assert.zok}}
```

If any assertion fails, execution stops as no valid proof could be generated from it.
