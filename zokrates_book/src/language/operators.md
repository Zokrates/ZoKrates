## Operators

The following table lists the precedence and associativity of all available operators. Operators are listed top to bottom, in ascending precedence.

| Operator                     | Description                                                  | Associativity                      | Remarks |
|------------------------------|--------------------------------------------------------------|------------------------------------|---------|
| ** <br>                      | Power                                                        | Left                               | [^1]     |
| *<br> /<br> %<br>                | Multiplication <br>  Division <br>  Remainder                | Left <br> Left <br>Left                     |         |
| + <br> - <br>                | Addition <br>  Subtraction <br>                              | Left <br> Left                     |         |
| << <br> >> <br>              | Left shift <br>  Right shift <br>                            | Left <br> Left                     | [^2]     |
| &                            | Bitwise AND                                                  | Left <br> Left                     |         |
| \|                           | Bitwise OR                                                   | Left <br> Left                     |         |
| ^                            | Bitwise XOR                                                  | Left <br> Left                     |         |
| >= <br><br> > <br> <= <br> < | Greater or equal <br> Greater <br> Lower or equal <br> Lower | Left <br> Left <br> Left <br> Left | [^3]     |
| != <br> == <br>              | Not Equal <br> Equal  <br>                                   | Left <br> Left                     |         |
| &&                           | Boolean AND                                                  | Left                               |         |
| \|\|                         | Boolean OR                                                   | Left                               |         |



[^1]: The exponent must be a compile-time constant

[^2]: The right operand must be a compile time constant

[^3]: Both operands are asserted to be strictly lower than the biggest power of 2 lower than `p/2`, unless one of them can be determined to be a compile-time constant