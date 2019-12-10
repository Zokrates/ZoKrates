## Variables

Variables can have any name which does not start with a number. Underscores are not allowed in variable names.
Variables are mutable, and always passed by value to functions.

### Shadowing

Shadowing is not allowed.
```zokrates
{{#include ../../../zokrates_cli/examples/book/no_shadowing.zok}}
```

### Scope

#### Function

Functions have their own scope
```zokrates
{{#include ../../../zokrates_cli/examples/book/function_scope.zok}}
```

#### For-loop
For-loops have their own scope
```zokrates
{{#include ../../../zokrates_cli/examples/book/for_scope.zok}}
```