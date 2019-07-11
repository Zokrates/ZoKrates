use crate::flat_absy::flat_parameter::FlatParameter;
use crate::flat_absy::flat_variable::FlatVariable;
use crate::flat_absy::*;
use crate::helpers::{DirectiveStatement, Helper};
use crate::types::signature::Signature;
use crate::types::Type;
use std::collections::HashMap;
use zokrates_field::field::Field;

fn use_variable(
    layout: &mut HashMap<String, FlatVariable>,
    name: String,
    index: &mut usize,
) -> FlatVariable {
    let var = FlatVariable::new(*index);
    layout.insert(name, var);
    *index = *index + 1;
    var
}

pub fn split<T: Field>() -> FlatProg<T> {
    let nbits = T::get_required_bits();

    let mut counter = 0;

    let mut layout = HashMap::new();

    let arguments = vec![FlatParameter {
        id: FlatVariable::new(0),
        private: true,
    }];

    // o0, ..., o253 = ToBits(i0)

    let directive_inputs = vec![FlatExpression::Identifier(use_variable(
        &mut layout,
        format!("i0"),
        &mut counter,
    ))];
    let directive_outputs: Vec<FlatVariable> = (0..T::get_required_bits())
        .map(|index| use_variable(&mut layout, format!("o{}", index), &mut counter))
        .collect();

    let helper = Helper::bits();

    let signature = Signature {
        inputs: vec![Type::FieldElement],
        outputs: vec![Type::array(Type::FieldElement, nbits)],
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

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    #[cfg(test)]
    mod split {
        use super::*;

        #[test]
        fn split254() {
            let unpack: FlatProg<FieldPrime> = split();
            let unpack = &unpack.functions[0];

            assert_eq!(unpack.id, String::from("main"));
            assert_eq!(
                unpack.arguments,
                vec![FlatParameter::private(FlatVariable::new(0))]
            );
            assert_eq!(
                unpack.statements.len(),
                FieldPrime::get_required_bits() + 1 + 1 + 1
            ); // 128 bit checks, 1 directive, 1 sum check, 1 return
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
                    expressions: (0..FieldPrime::get_required_bits())
                        .map(|i| FlatExpression::Identifier(FlatVariable::new(i + 1)))
                        .collect()
                })
            );
        }
    }
}
