## Control Flow

ZoKrates provides a single thread of execution with a few flow constructs.

### Function calls

Function calls help make programs clear and modular.

Arguments are passed by value.

Function parameters can be declared as mutable to allow for mutation within the function's body. However, mutable function arguments are still passed by value, so the original value can never be mutated.

```zokrates
{{#include ../../../zokrates_cli/examples/book/side_effects.zok}}
```

Generic parameters, if any, must be compile-time constants. They are inferred by the compiler if that is possible, but can also be provided explicitly.

```zokrates
{{#include ../../../zokrates_cli/examples/book/generic_call.zok}}
```

### Conditional expressions

A conditional expression allows you to branch your code depending on a boolean condition.

```zokrates
{{#include ../../../zokrates_cli/examples/book/conditional.zok}}
```

The conditional expression can also be written using a ternary operator:

```zokrates
{{#include ../../../zokrates_cli/examples/book/conditional_ternary.zok}}
```

There are two important caveats when it comes to conditional expressions. Before we go into them, let's define two concepts:
- for an execution of the program, *an executed branch* is a branch which has to be paid for when executing the program, generating proofs, etc.
- for an execution of the program, *a logically executed branch* is a branch which is "chosen" by the condition of an if-expression. This is the more intuitive notion of execution, and there is only one for each if-expression.

Now the two caveats:
- **Both branches are always executed**. No short-circuiting happens based on the value of the condition. Therefore, the complexity of a program in terms of the number of constraints it compiles down to is the *sum* of the cost of all branches.
```zokrates
{{#include ../../../zokrates_cli/examples/book/conditional_expensive.zok}}
```
- **An unsatisfied constraint inside any branch will make the whole execution fail, even if this branch is not logically executed**. Also, the compiler itself inserts assertions which can fail. This can lead to unexpected results:
```zokrates
{{#include ../../../zokrates_cli/examples/book/conditional_panic.zok}}
```
The experimental flag `--branch-isolation` can be activated in the CLI in order to restrict any unsatisfied constraint to make the execution fail only if it is in a logically executed branch. This way, the execution of the program above will always succeed.

>The reason for these caveats is that the program is compiled down to an arithmetic circuit. This construct does not support jumping to a branch depending on a condition as you could do on traditional architectures. Instead, all branches are inlined as if they were printed on a circuit board. The `branch-isolation` feature comes with overhead for each assertion in each branch, and this overhead compounds when deeply nesting conditionals.

### For loops

For loops are available with the following syntax:

```zokrates
{{#include ../../../zokrates_cli/examples/book/for.zok}}
```

The bounds have to be constant at compile-time, therefore they cannot depend on execution inputs. They can depend on generic parameters.
The range is half-open, meaning it is bounded inclusively below and exclusively above. The range `start..end` contains all values within `start <= x < end`. The range is empty if `start >= end`.

> For loops are only syntactic sugar for repeating a block of statements many times. No condition of the type `index < max` is being checked at run-time after each iteration. Instead, at compile-time, the index is incremented and the block is executed again. Therefore, assigning to the loop index does not have any influence on the number of iterations performed and is considered bad practice.

### Assertions

Any boolean can be asserted to be true using the `assert` function.

```zokrates
{{#include ../../../zokrates_cli/examples/book/assert.zok}}
```

If any assertion fails, execution stops as no valid proof could be generated from it.
