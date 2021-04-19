## Constants

Constants must be globally defined outside all other scopes by using a `const` keyword. Constants can be set only to a constant expression.

```zokrates
{{#include ../../../zokrates_cli/examples/book/constant_definition.zok}}
```

The value of a constant can't be changed through reassignment, and it can't be redeclared.  Constants are essentially inlined wherever they are used, meaning that they are copied directly into the relevant context when used.

Constants must be explicitly typed. One can reference other constants inside the expression, as long as the referenced constant is defined before the constant.

```zokrates
{{#include ../../../zokrates_cli/examples/book/constant_reference.zok}}
```

The naming convention for constants are similar to that of variables. All characters in a constant name are usually in uppercase.