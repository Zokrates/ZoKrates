use bimap::BiMap;
use flat_absy::flat_parameter::FlatParameter;
use flat_absy::flat_variable::FlatVariable;
use flat_absy::*;
use helpers::{DirectiveStatement, Helper};
use reduce::Reduce;
use types::constraints::Constraint;
use types::signature::Signature;
use types::Type;
use zokrates_field::field::Field;

fn use_variable(
    bijection: &mut BiMap<String, FlatVariable>,
    name: String,
    index: &mut usize,
) -> FlatVariable {
    let var = FlatVariable::new(*index);
    bijection.insert(name, var);
    *index = *index + 1;
    var
}

pub fn pack<T: Field>(nbits: usize) -> FlatProg<T> {
    assert!(nbits <= T::get_required_bits()); // we cannot pack more bits than the field

    let arguments = (0..nbits)
        .map(|i| FlatParameter {
            id: FlatVariable::new(i),
            private: true,
        })
        .collect();

    let signature = Signature {
        inputs: vec![Type::FieldElement; nbits],
        outputs: vec![Type::FieldElement],
    };

    // sum check
    let mut ret = FlatExpression::Number(T::from(0));

    for i in 0..nbits {
        ret = FlatExpression::Add(
            box ret,
            box FlatExpression::Mult(
                box FlatExpression::Identifier(FlatVariable::new(i)),
                box FlatExpression::Number(T::from(2).pow(nbits - i - 1)),
            ),
        );
    }

    let statements = vec![FlatStatement::Return(FlatExpressionList {
        expressions: vec![ret],
    })];

    FlatProg {
        functions: vec![FlatFunction {
            id: String::from("main"),
            arguments,
            statements,
            signature,
        }],
    }
}

pub fn unpack<T: Field>(nbits: usize) -> FlatProg<T> {
    assert!(nbits <= T::get_required_bits()); // we cannot pack more bits than the field

    let mut counter = 0;

    let mut bijection = BiMap::new();

    let arguments = vec![FlatParameter {
        id: FlatVariable::new(0),
        private: true,
    }];

    // o0, ..., o253 = ToBits(i0)

    let directive_inputs = vec![FlatExpression::Identifier(use_variable(
        &mut bijection,
        format!("i0"),
        &mut counter,
    ))];
    let directive_outputs: Vec<FlatVariable> = (0..T::get_required_bits())
        .map(|index| use_variable(&mut bijection, format!("o{}", index), &mut counter))
        .collect();

    let helper = Helper::bits();

    let signature = Signature {
        inputs: vec![Type::FieldElement],
        outputs: vec![Type::FieldElement; nbits],
    };

    let outputs = directive_outputs
        .iter()
        .enumerate()
        .filter(|(index, _)| *index >= T::get_required_bits() - nbits)
        .map(|(_, o)| FlatExpression::Identifier(o.clone()))
        .collect();

    // o253, o252, ... o{253 - (nbits - 1)} are bits
    let mut statements: Vec<FlatStatement<T>> = (0..nbits)
        .map(|index| {
            let bit = FlatExpression::Identifier(FlatVariable::new(T::get_required_bits() - index));
            FlatStatement::Condition(
                bit.clone(),
                FlatExpression::Mult(box bit.clone(), box bit.clone()),
            )
        })
        .collect();

    // sum check: o253 + o252 * 2 + ... + o{253 - (nbits - 1)} * 2**(nbits - 1)
    let mut lhs_sum = FlatExpression::Number(T::from(0));

    for i in 0..nbits {
        lhs_sum = FlatExpression::Add(
            box lhs_sum,
            box FlatExpression::Mult(
                box FlatExpression::Identifier(FlatVariable::new(T::get_required_bits() - i)),
                box FlatExpression::Number(T::from(2).pow(i)),
            ),
        );
    }

    statements.push(FlatStatement::Condition(
        lhs_sum,
        FlatExpression::Mult(
            box FlatExpression::Identifier(FlatVariable::new(0)),
            box FlatExpression::Number(T::from(1)),
        ),
    ));

    statements.insert(
        0,
        FlatStatement::Directive(DirectiveStatement {
            inputs: directive_inputs,
            outputs: directive_outputs,
            helper: helper,
        }),
    );

    statements.push(FlatStatement::Return(FlatExpressionList {
        expressions: outputs,
    }));

    FlatProg {
        functions: vec![FlatFunction {
            id: String::from("main"),
            arguments,
            statements,
            signature,
        }],
    }
}

pub fn cast<T: Field>(from: &Type, to: &Type) -> FlatFunction<T> {
    let mut counter = 0;

    let mut bijection = BiMap::new();

    let arguments = (0..from.get_primitive_count())
        .enumerate()
        .map(|(index, _)| FlatParameter {
            id: FlatVariable::new(index),
            private: true,
        })
        .collect();

    let directive_inputs = (0..from.get_primitive_count())
        .map(|index| use_variable(&mut bijection, format!("i{}", index), &mut counter))
        .collect();
    let directive_outputs: Vec<FlatVariable> = (0..to.get_primitive_count())
        .map(|index| use_variable(&mut bijection, format!("o{}", index), &mut counter))
        .collect();

    let constraints = to.get_constraints::<T>().constraints;

    let intermediate_variables = match constraints.len() {
        0 => vec![],
        _ => constraints[0]
            .a
            .iter()
            .enumerate()
            .map(|(_, index)| use_variable(&mut bijection, format!("inter{}", index), &mut counter))
            .collect(),
    };

    let conditions: Vec<FlatStatement<T>> = to
        .get_constraints()
        .constraints
        .iter()
        .map(|constraint: &Constraint<T>| {
            let rhs_a = match constraint
                .a
                .iter()
                .enumerate()
                .map(|(key, val)| {
                    FlatExpression::Mult(
                        box FlatExpression::Number(val.clone()),
                        box FlatExpression::Identifier(intermediate_variables[key]),
                    )
                })
                .reduce(|acc, e| FlatExpression::Add(box acc, box e))
            {
                Some(e @ FlatExpression::Mult(..)) => {
                    FlatExpression::Add(box FlatExpression::Number(T::zero()), box e)
                } // the R1CS serializer only recognizes Add
                Some(e) => e,
                None => FlatExpression::Number(T::zero()),
            };

            let rhs_b = match constraint
                .b
                .iter()
                .enumerate()
                .map(|(key, val)| {
                    FlatExpression::Mult(
                        box FlatExpression::Number(val.clone()),
                        box FlatExpression::Identifier(intermediate_variables[key]),
                    )
                })
                .reduce(|acc, e| FlatExpression::Add(box acc, box e))
            {
                Some(e @ FlatExpression::Mult(..)) => {
                    FlatExpression::Add(box FlatExpression::Number(T::zero()), box e)
                } // the R1CS serializer only recognizes Add
                Some(e) => e,
                None => FlatExpression::Number(T::zero()),
            };

            let lhs = match constraint
                .c
                .iter()
                .enumerate()
                .map(|(key, val)| {
                    FlatExpression::Mult(
                        box FlatExpression::Number(val.clone()),
                        box FlatExpression::Identifier(intermediate_variables[key]),
                    )
                })
                .reduce(|acc, e| FlatExpression::Add(box acc, box e))
            {
                Some(e @ FlatExpression::Mult(..)) => {
                    FlatExpression::Add(box FlatExpression::Number(T::zero()), box e)
                } // the R1CS serializer only recognizes Add
                Some(e) => e,
                None => FlatExpression::Number(T::zero()),
            };

            FlatStatement::Condition(lhs, FlatExpression::Mult(box rhs_a, box rhs_b))
        })
        .collect();

    let helper = match (from, to) {
        (Type::Boolean, Type::FieldElement) => Helper::identity(),
        (Type::FieldElement, Type::Boolean) => Helper::identity(),
        _ => panic!(format!("can't cast {} to {}", from, to)),
    };

    let signature = Signature {
        inputs: vec![from.clone()],
        outputs: vec![to.clone()],
    };

    let outputs = directive_outputs
        .iter()
        .map(|o| FlatExpression::Identifier(o.clone()))
        .collect();

    let mut statements = conditions;

    statements.insert(
        0,
        FlatStatement::Directive(DirectiveStatement::new(
            directive_outputs,
            helper,
            directive_inputs,
        )),
    );

    statements.push(FlatStatement::Return(FlatExpressionList {
        expressions: outputs,
    }));

    FlatFunction {
        id: format!("_{}_to_{}", from, to),
        arguments,
        statements,
        signature,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    #[cfg(test)]
    mod cast {
        use super::*;

        #[test]
        fn field_to_bool() {
            let f2b: FlatFunction<FieldPrime> = cast(&Type::FieldElement, &Type::Boolean);
            assert_eq!(f2b.id, String::from("_field_to_bool"));
            assert_eq!(
                f2b.arguments,
                vec![FlatParameter::private(FlatVariable::new(0))]
            );
            assert_eq!(f2b.statements.len(), 3); // 1 directive, 1 constraint, 1 return
            assert_eq!(
                f2b.statements[0],
                FlatStatement::Directive(DirectiveStatement::new(
                    vec![FlatVariable::new(1)],
                    Helper::identity(),
                    vec![FlatVariable::new(0)]
                ))
            );
            assert_eq!(
                f2b.statements[2],
                FlatStatement::Return(FlatExpressionList {
                    expressions: vec![FlatExpression::Identifier(FlatVariable::new(1))]
                })
            );
            assert_eq!(f2b.signature.outputs.len(), 1);
        }

        #[test]
        fn bool_to_field() {
            let b2f: FlatFunction<FieldPrime> = cast(&Type::Boolean, &Type::FieldElement);
            assert_eq!(b2f.id, String::from("_bool_to_field"));
            assert_eq!(
                b2f.arguments,
                vec![FlatParameter::private(FlatVariable::new(0))]
            );
            assert_eq!(b2f.statements.len(), 2); // 1 directive, 1 return
            assert_eq!(
                b2f.statements[0],
                FlatStatement::Directive(DirectiveStatement::new(
                    vec![FlatVariable::new(1)],
                    Helper::identity(),
                    vec![FlatVariable::new(0)]
                ))
            );
            assert_eq!(
                b2f.statements[1],
                FlatStatement::Return(FlatExpressionList {
                    expressions: vec![FlatExpression::Identifier(FlatVariable::new(1))]
                })
            );
            assert_eq!(b2f.signature.outputs.len(), 1);
        }
    }

    #[cfg(test)]
    mod unpack {
        use super::*;

        #[test]
        fn unpack128() {
            let nbits = 128;

            let unpack: FlatProg<FieldPrime> = unpack(nbits);
            let unpack = &unpack.functions[0];

            assert_eq!(unpack.id, String::from("main"));
            assert_eq!(
                unpack.arguments,
                vec![FlatParameter::private(FlatVariable::new(0))]
            );
            assert_eq!(unpack.statements.len(), nbits + 1 + 1 + 1); // 128 bit checks, 1 directive, 1 sum check, 1 return
            assert_eq!(
                unpack.statements[0],
                FlatStatement::Directive(DirectiveStatement::new(
                    (0..FieldPrime::get_required_bits())
                        .map(|i| FlatVariable::new(i + 1))
                        .collect(),
                    Helper::bits(),
                    vec![FlatVariable::new(0)]
                ))
            );
            assert_eq!(
                *unpack.statements.last().unwrap(),
                FlatStatement::Return(FlatExpressionList {
                    expressions: (FieldPrime::get_required_bits() - nbits
                        ..FieldPrime::get_required_bits())
                        .map(|i| FlatExpression::Identifier(FlatVariable::new(i + 1)))
                        .collect()
                })
            );
        }

        #[test]
        fn pack128() {
            let pack: FlatProg<FieldPrime> = pack(128);
            let pack = &pack.functions[0];

            assert_eq!(pack.id, String::from("main"));
            assert_eq!(pack.arguments.len(), 128);
            assert_eq!(pack.statements.len(), 1); // just sum bits * 2**i
        }
    }
}
