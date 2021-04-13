## Generics

ZoKrates supports code that is generic over constants of the `u32` type. No specific keyword is used: the compiler determines if the generic parameters are indeed constant at compile time. Here's an example of generic code in ZoKrates:

```zokrates
{{#include ../../../zokrates_cli/examples/book/generics.zok}}
```