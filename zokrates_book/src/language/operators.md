## Operators

The following table lists the precedence and associativity of all operators. Operators are listed top to bottom, in ascending precedence. Operators in the same box group left to right. Operators are binary, unless the syntax is provided.

| Operator                        | Description                                                       | Remarks |
|---------------------------------|-------------------------------------------------------------------|---------|
| `**` <br>                       | Power                                                             |  [^1]   |
| `+x` <br> `-x` <br> `!x` <br>   | Positive <br> Negative <br> Negation <br>                         |         |
| `*` <br> `/` <br> `%` <br>      | Multiplication <br>  Division <br>  Remainder <br>                |         |
| `+` <br> `-` <br>               | Addition <br>  Subtraction <br>                                   |         |
| `<<` <br> `>>` <br>             | Left shift <br>  Right shift <br>                                 |  [^2]   |
| `&`                             | Bitwise AND                                                       |         |
| <code>&#124;</code>             | Bitwise OR                                                        |         |
| `^`                             | Bitwise XOR                                                       |         |
| `>=` <br> `>` <br> `<=` <br> `<`| Greater or equal <br> Greater <br> Lower or equal <br> Lower <br> |  [^3]   |
| `!=` <br> `==` <br>             | Not Equal <br> Equal  <br>                                        |         |
| `&&`                            | Boolean AND                                                       |         |
| <code>&#124;&#124;</code>       | Boolean OR                                                        |         |
| `if c then x else y fi`         | Conditional expression                                            |         |

[^1]: The exponent must be a compile-time constant of type `u32`

[^2]: The right operand must be a compile time constant of type `u32`

[^3]: Both operands are asserted to be strictly lower than the biggest power of 2 lower than `p/2`