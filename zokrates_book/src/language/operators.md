## Operators

The following table lists the precedence and associativity of all operators. Operators are listed top to bottom, in ascending precedence. Operators in the same cell have the same precedence. Operators are binary, unless the syntax is provided.

| Operator                   | Description                                                | `field`                      | `u8/u16` `u32/u64`            | `bool`                      | Associativity | Remarks |
|----------------------------|------------------------------------------------------------|------------------------------|-------------------------------|-----------------------------|---------------|---------|
| `**`<br>                   | Power                                                      | &check;                      | &nbsp;                        | &nbsp;                      | Left          | [^1]    |
| `+x`<br>`-x`<br>`!x`<br>   | Positive<br>Negative<br>Negation<br>                       | &check;<br>&check;<br>&nbsp; | &check;<br>&check;<br>&nbsp;  | &nbsp;<br>&nbsp;<br>&check; | Right         |         |
| `*`<br>`/`<br>`%`<br>      | Multiplication<br> Division<br> Remainder<br>              | &check;<br>&check;<br>&nbsp; | &check;<br>&check;<br>&check; | &nbsp;<br>&nbsp;<br>&nbsp;  | Left          |         |
| `+`<br>`-`<br>             | Addition<br> Subtraction<br>                               | &check;                      | &check;                       | &nbsp;                      | Left          |         |
| `<<`<br>`>>`<br>           | Left shift<br> Right shift<br>                             | &nbsp;                       | &check;                       | &nbsp;                      | Left          | [^2]    |
| `&`                        | Bitwise AND                                                | &nbsp;                       | &check;                       | &nbsp;                      | Left          |         |
| <code>&#124;</code>        | Bitwise OR                                                 | &nbsp;                       | &check;                       | &nbsp;                      | Left          |         |
| `^`                        | Bitwise XOR                                                | &nbsp;                       | &check;                       | &nbsp;                      | Left          |         |
| `>=`<br>`>`<br>`<=`<br>`<` | Greater or equal<br>Greater<br>Lower or equal<br>Lower<br> | &check;                      | &check;                       | &nbsp;                      | Left          | [^3]    |
| `!=`<br>`==`<br>           | Not Equal<br>Equal<br>                                     | &check;                      | &check;                       | &check;                     | Left          |         |
| `&&`                       | Boolean AND                                                | &nbsp;                       | &nbsp;                        | &check;                     | Left          |         |
| <code>&#124;&#124;</code>  | Boolean OR                                                 | &nbsp;                       | &nbsp;                        | &check;                     | Left          |         |
| `if c then x else y fi`    | Conditional expression                                     | &check;                      | &check;                       | &check;                     | Right         | [^4]    |

[^1]: The exponent must be a compile-time constant of type `u32`

[^2]: The right operand must be a compile time constant of type `u32`

[^3]: Both operands are asserted to be strictly lower than the biggest power of 2 lower than `p/2`, unless one of them can be determined to be a compile-time constant

[^4]: Conditional expression can also be written using a ternary operator: `c ? x : y`