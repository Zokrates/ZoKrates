## Functions

A function has to be declared at the top level before it is called.

```zokrates
def foo() -> (field):
    return 1

def bar() -> (field):
    return foo()
```

A function's signature has to be explicitly provided.
Functions can return many values by providing them as a comma-separated list.

```zokrates
def main() -> (field, field[3]):
    return 1, [2, 3, 4]
```

### Inference

When defining a variable as the return value of a function, types are optional:

```zokrates
def foo() -> (field, field):
    return 21, 42

def main() -> (field):
    a, b = foo()
    return 1
```

If there is an ambiguity, providing the types of some of the assigned variables is necessary.

```zokrates
def foo() -> (field, field[3]):
    return 1, [2, 3, 4]

def foo() -> (field, field):
    return 1, 2

def main() -> (field):
    a, field[3] b = foo()
    return 1
```