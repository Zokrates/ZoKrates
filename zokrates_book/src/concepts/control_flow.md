## Control Flow

ZoKrates provide a single thread of execution with two control flow constructs.

### Function calls

Function calls can help make programs clearer and more modular. However, using function calls is not always zero-cost, so deep call chains should be avoided.

Arguments are passed by value.

```zokrates
def incr(field a) -> (field)
    a = a + 1
    return 1

def main() -> (field):
    field x = 1
    field res = incr(x)
    x == 1 // x has not changed
    return 1
```

### If expressions

An if expression allows you to branch your code depending on conditions.

```zokrates
def main(field x) -> (field):
  field y = if x + 2 == 3 then 1 else 5 fi
  return y
```

### For loops

For loops are available with the following syntax:

```zokrates
def main() -> (field):
    field res = 0
    for field i in 0..4 do
        res = res + i
    endfor
    return res
```

The bounds have to be known at compile time, so only constants are allowed.
For-loops define their own scope.