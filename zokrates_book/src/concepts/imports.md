## Imports

You can separate your code into multiple ZoKrates files using `import` statements, ignoring the `.zok` extension of the imported file:

### Relative Imports

You can import a resource in the same folder directly, like this:
```zokrates
import "./mycode"
```

There also is a handy syntax to import from the parent directory:
```zokrates
import "../mycode"
```

Also imports further up the file-system are supported:
```zokrates
import "../../../mycode"
```

You can also choose to rename the imported resource, like so:
```zokrates
import "./mycode" as abc
```

### Absolute Imports

Absolute imports don't start with `./` or `../` in the path and are used to import components from the ZoKrates standard library. Please check the according [section](./stdlib.html) for more details.
`