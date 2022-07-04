## Imports

You can separate your code into multiple ZoKrates files using `import` statements to import symbols, ignoring the `.zok` extension of the imported file.

### Import syntax

#### Symbol selection

The preferred way to import a symbol is by module and name:
```zokrates
from "./path/to/my/module" import MySymbol;

// `MySymbol` is now in scope.
```

To import multiple symbols with a single import statement, separate the symbols names with commas:

```zokrates
from "./path/to/my/module" import MySymbol, MyOtherSymbol;
```

#### Aliasing

The `as` keyword enables renaming symbols:

```zokrates
from "./path/to/my/module" import MySymbol as MyAlias;

// `MySymbol` is now in scope under the alias MyAlias.
```
#### Legacy

The legacy way to import a symbol is by only specifying a module:
```
import "./path/to/my/module";
```
In this case, the name of the symbol is assumed to be `main` and the alias is assumed to be the module's filename so that the above is equivalent to
```zokrates
from "./path/to/my/module" import main as module;

// `main` is now in scope under the alias `module`.
```

Note that this legacy method is likely to become deprecated, so it is recommended to use the preferred way instead.
### Symbols

Three types of symbols can be imported

#### Functions
Functions are imported by name. If many functions have the same name but different signatures, all of them get imported, and which one to use in a particular call is inferred.

#### User-defined types
User-defined types declared with the `struct` keyword are imported by name.

#### Constants
Constants declared with the `const` keyword are imported by name.

### Relative Imports

You can import a resource in the same folder directly, like this:
```zokrates
from "./mycode" import foo;
```

Imports up the file-system tree are supported:
```zokrates
from "../../../mycode" import foo;
```

### Absolute Imports

Absolute imports don't start with `./` or `../` in the path and are used to import components from the ZoKrates standard library. Please check the according [section](../toolbox/stdlib.md) for more details.