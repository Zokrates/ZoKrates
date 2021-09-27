## Operators

The following table lists the precedence and associativity of all operators. Operators are listed top to bottom, in ascending precedence. Operators in the same box group have the same precedence. Operators are binary, unless the syntax is provided.

| Operator                        | Description                                                       | Field                             | Unsigned integers | Bool                              | Associativity | Remarks |
|---------------------------------|-------------------------------------------------------------------|-----------------------------------|-------------------|-----------------------------------|---------------|---------|
| `**` <br>                       | Power                                                             | &check;                           | &times;           | &times;                           | Left          | [^1]    |
| `+x` <br> `-x` <br> `!x` <br>   | Positive <br> Negative <br> Negation <br>                         | &check;                           | &check;           | &times; <br> &times; <br> &check; | Right         |         |
| `*` <br> `/` <br> `%` <br>      | Multiplication <br>  Division <br>  Remainder <br>                | &check; <br> &check; <br> &times; | &check;           | &times;                           | Left          |         |
| `+` <br> `-` <br>               | Addition <br>  Subtraction <br>                                   | &check;                           | &check;           | &times;                           | Left          |         |
| `<<` <br> `>>` <br>             | Left shift <br>  Right shift <br>                                 | &times;                           | &check;           | &times;                           | Left          | [^2]    |
| `&`                             | Bitwise AND                                                       | &times;                           | &check;           | &times;                           | Left          |         |
| <code>&#124;</code>             | Bitwise OR                                                        | &times;                           | &check;           | &times;                           | Left          |         |
| `^`                             | Bitwise XOR                                                       | &times;                           | &check;           | &times;                           | Left          |         |
| `>=` <br> `>` <br> `<=` <br> `<`| Greater or equal <br> Greater <br> Lower or equal <br> Lower <br> | &check;                           | &check;           | &times;                           | Left          | [^3]    |
| `!=` <br> `==` <br>             | Not Equal <br> Equal  <br>                                        | &check;                           | &check;           | &check;                           | Left          |         |
| `&&`                            | Boolean AND                                                       | &times;                           | &times;           | &check;                           | Left          |         |
| <code>&#124;&#124;</code>       | Boolean OR                                                        | &times;                           | &times;           | &check;                           | Left          |         |
| `if c then x else y fi`         | Conditional expression                                            | &check;                           | &check;           | &check;                           | Right         |         |

[^1]: The exponent must be a compile-time constant of type `u32`

[^2]: The right operand must be a compile time constant of type `u32`

[^3]: Both operands are asserted to be strictly lower than the biggest power of 2 lower than `p/2`, unless one of them can be determined to be a compile-time constant