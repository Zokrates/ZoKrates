## Macros

ZoKrates currently exposes a single macro:

```
#pragma curve $CURVE
```

The effect of this macro is to abort compilation if this file is being compiled for a curve different from `$CURVE`.