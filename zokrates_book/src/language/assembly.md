## Assembly

ZoKrates allows developers to define constraints through assembly blocks. Assembly blocks are considered **unsafe**, as safety and correctness of the resulting arithmetic circuit is in the hands of the developer. Usage of assembly is recommended only  in optimization efforts for the experienced developers to minimize constraint count of an arithmetic circuit.

## Writing assembly

All constraints must be enclosed within an `asm` block. In an assembly block we can do the following:

1. Assign to a witness variable using `<--`
2. Define a constraint using `===`

Assigning a value, in general, should be combined with adding a constraint:

```zok
def main(field a, field b) {
    field mut c = 0;
    asm {
        c <-- a / b;
        a === b * c;
    }
}
```

> The operator `<--` can be sometimes misused, as this operator does not generate any constraints, resulting in unconstrained variables in the constraint system.

In some cases we can combine the witness assignment and constraint generation with the `<==` operator:

```zok
asm {
    c <== 1 - a*b;
}
```

which is equivalent to:

```zok
asm {
    c <-- 1 - a*b;
    c === 1 - a*b;
}
```

A constraint can contain arithmetic expressions that are built using multiplication, addition, and other variables or `field` values. Only quadratic expressions are allowed to be included in constraints. Non-quadratic expressions or usage of other arithmetic operators like division or power are not allowed as constraints, but can be used in the witness assignment expression.

The following code is not allowed:

```zok
asm {
    d === a*b*c;
}
```

as the constraint `d === a*b*c` is not quadratic.

In some cases, ZoKrates will apply minor transformations on the defined constraints in order to meet the correct format:

```zok
asm {
    x * (x - 1) === 0;
}
```

will be transformed to:

```zok
asm {
    x === x * x;
}
```

## Type casting

Assembly is a low-level part of the compiler which does not have type safety. In some cases we might want to do zero-cost conversions between `field` and `bool` type.

### field_to_bool_unsafe

This call is unsafe because it is the responsibility of the user to constrain the field input:

```zok
from "EMBED" import field_to_bool_unsafe;

def main(field x) -> bool {
    // we constrain `x` to be 0 or 1
    asm {
        x * (x - 1) === 0;
    }
    // we can treat `x` as `bool` afterwards, as we constrained it properly
    // `field_to_bool_unsafe` call does not produce any extra constraints
    bool out = field_to_bool_unsafe(x);
    return out;
}
```

### bool_to_field

This call is safe as `bool` types are constrained by the compiler:

```zok
from "EMBED" import bool_to_field;

def main(bool x) -> field {
    // `x` is constrained by the compiler automatically so we can safely 
    //  treat it as `field` with no extra cost
    field out = bool_to_field(x);
    return out;
}
```