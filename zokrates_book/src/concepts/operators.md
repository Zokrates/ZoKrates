## Operators

The ZoKrates programming language constists of different operands that can be used on variables

### Available Operators

#### Or

```zokrates
{{#include ../../../zokrates_cli/examples/book/or.code}}
```

#### Xor

```zokrates
{{#include ../../../zokrates_cli/examples/book/xor.code}}
```

#### And

```zokrates
{{#include ../../../zokrates_cli/examples/book/and.code}}
```

#### Equal

```zokrates
{{#include ../../../zokrates_cli/examples/book/equal.code}}
```

#### Not Equal

```zokrates
{{#include ../../../zokrates_cli/examples/book/not_equal.code}}
```

#### Greater/Lower

```zokrates
{{#include ../../../zokrates_cli/examples/book/gtl.code}}
```

#### Add

```zokrates
{{#include ../../../zokrates_cli/examples/book/add.code}}
```

#### Subtract

```zokrates
{{#include ../../../zokrates_cli/examples/book/subtract.code}}
```

#### Multiply

```zokrates
{{#include ../../../zokrates_cli/examples/book/mul.code}}
```

#### Divide

```zokrates
{{#include ../../../zokrates_cli/examples/book/div.code}}
```

#### Power

```zokrates
{{#include ../../../zokrates_cli/examples/book/pow.code}}
```

### Operator Precedence
The following table lists the precedence and associativity of all available operators. Operators are listed top to bottom, in descending precedence.

| Precedence | Operator                               | Description                        | Associativity                     |
|------------|----------------------------------------|------------------------------------|-----------------------------------|
| 1          | ** <br>                                | Power                              | Left                              |
| 2          | * <br> /<br>                           | Multiplication <br>  Division <br> | Left <br> Left                    |
| 3          | + <br> - <br>                          | Addition <br>  Subtraction <br>    | Left <br> Left                    |
| 4          | >= <br> > <br> <= <br> <               | gte <br> gt <br> lte <br> lt       | Left <br> Left <br> Left <br> Left|
| 5          | == <br> != <br>                        | Equal <br> Not Equal  <br>         | Left <br> Left                    |
| 6          | &&                                     | And                                | Left                              |
| 7          | ^                                      | Xor                                | Left                              |
| 8          | \|\|                                   | Or                                 | Left                              |