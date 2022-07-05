## Logging

ZoKrates supports a command to log messages during execution in the interpreter.

The values of expressions can be checked and basic string interpolation is supported:

```zokrates
{{#include ../../../zokrates_cli/examples/book/logging.zok}}
```

By default, logs get removed during compilation. In order to include them in the compiled program, the `--debug` flag has to be enabled.