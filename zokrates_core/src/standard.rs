use crate::flat_absy::{FlatExpression, FlatExpressionList, FlatFunction, FlatStatement};
use crate::flat_absy::{FlatParameter, FlatVariable};
use crate::helpers::{DirectiveStatement, Helper, RustHelper};
use crate::types::{Signature, Type};
use bellman::pairing::ff::ScalarEngine;
use reduce::Reduce;
use zokrates_embed::{generate_sha256_round_constraints, BellmanConstraint};
use zokrates_field::field::Field;

// util to convert a vector of `(variable_id, coefficient)` to a flat_expression
fn flat_expression_from_vec<T: Field>(
    v: Vec<(usize, <<T as Field>::BellmanEngine as ScalarEngine>::Fr)>,
) -> FlatExpression<T> {
    match v
        .into_iter()
        .map(|(key, val)| {
            FlatExpression::Mult(
                box FlatExpression::Number(T::from_bellman(val)),
                box FlatExpression::Identifier(FlatVariable::new(key)),
            )
        })
        .reduce(|acc, e| FlatExpression::Add(box acc, box e))
    {
        Some(e @ FlatExpression::Mult(..)) => {
            FlatExpression::Add(box FlatExpression::Number(T::zero()), box e)
        } // the R1CS serializer only recognizes Add
        Some(e) => e,
        None => FlatExpression::Number(T::zero()),
    }
}

impl<T: Field> From<BellmanConstraint<T::BellmanEngine>> for FlatStatement<T> {
    fn from(c: zokrates_embed::BellmanConstraint<T::BellmanEngine>) -> FlatStatement<T> {
        let rhs_a = flat_expression_from_vec(c.a);
        let rhs_b = flat_expression_from_vec(c.b);
        let lhs = flat_expression_from_vec(c.c);

        FlatStatement::Condition(lhs, FlatExpression::Mult(box rhs_a, box rhs_b))
    }
}

/// Returns a flat function which computes a sha256 round
///
/// # Remarks
///
/// The variables inside the function are set in this order:
/// - constraint system variables
/// - arguments
pub fn sha_round<T: Field>() -> FlatFunction<T> {
    // Define iterators for all indices at hand
    let (r1cs, input_indices, current_hash_indices, output_indices) =
        generate_sha256_round_constraints::<T::BellmanEngine>();

    // indices of the input
    let input_indices = input_indices.into_iter();
    // indices of the current hash
    let current_hash_indices = current_hash_indices.into_iter();
    // indices of the output
    let output_indices = output_indices.into_iter();

    let variable_count = r1cs.aux_count + 1; // auxiliary and ONE

    // indices of the sha256round constraint system variables
    let cs_indices = (0..variable_count).into_iter();

    // indices of the arguments to the function
    // apply an offset of `variable_count` to get the indice of our dummy `input` argument
    let input_argument_indices = input_indices
        .clone()
        .into_iter()
        .map(|i| i + variable_count);
    // apply an offset of `variable_count` to get the indice of our dummy `current_hash` argument
    let current_hash_argument_indices = current_hash_indices
        .clone()
        .into_iter()
        .map(|i| i + variable_count);

    // define the signature of the resulting function
    let signature = Signature {
        inputs: vec![
            Type::FieldElementArray(input_indices.len()),
            Type::FieldElementArray(current_hash_indices.len()),
        ],
        outputs: vec![Type::FieldElementArray(output_indices.len())],
    };

    // define parameters to the function based on the variables
    let arguments = input_argument_indices
        .clone()
        .chain(current_hash_argument_indices.clone())
        .map(|i| FlatParameter {
            id: FlatVariable::new(i),
            private: true,
        })
        .collect();

    // define a binding of the first variable in the constraint system to one
    let one_binding_statement = FlatStatement::Condition(
        FlatVariable::new(0).into(),
        FlatExpression::Number(T::from(1)),
    );

    let input_binding_statements =
    // bind input and current_hash to inputs
    input_indices.clone().chain(current_hash_indices).zip(input_argument_indices.clone().chain(current_hash_argument_indices.clone())).map(|(cs_index, argument_index)| {
        FlatStatement::Condition(
            FlatVariable::new(cs_index).into(),
            FlatVariable::new(argument_index).into(),
        )
    });

    // insert flattened statements to represent constraints
    let constraint_statements = r1cs.constraints.into_iter().map(|c| c.into());

    // define which subset of the witness is returned
    let outputs: Vec<FlatExpression<T>> = output_indices
        .map(|o| FlatExpression::Identifier(FlatVariable::new(o)))
        .collect();

    // insert a directive to set the witness based on the bellman gadget and  inputs
    let directive_statement = FlatStatement::Directive(DirectiveStatement {
        outputs: cs_indices.map(|i| FlatVariable::new(i)).collect(),
        inputs: input_argument_indices
            .chain(current_hash_argument_indices)
            .map(|i| FlatVariable::new(i).into())
            .collect(),
        helper: Helper::Rust(RustHelper::Sha256Round),
    });

    // insert a statement to return the subset of the witness
    let return_statement = FlatStatement::Return(FlatExpressionList {
        expressions: outputs,
    });

    let statements = std::iter::once(directive_statement)
        .chain(std::iter::once(one_binding_statement))
        .chain(input_binding_statements)
        .chain(constraint_statements)
        .chain(std::iter::once(return_statement))
        .collect();

    FlatFunction {
        id: "main".to_owned(),
        arguments,
        statements,
        signature,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    #[test]
    fn generate_sha256_constraints() {
        let compiled = sha_round();

        // function should have a signature of 768 inputs and 256 outputs
        assert_eq!(
            compiled.signature,
            Signature::new()
                .inputs(vec![
                    Type::FieldElementArray(512),
                    Type::FieldElementArray(256)
                ])
                .outputs(vec![Type::FieldElementArray(256)])
        );

        // function should have 768 inputs
        assert_eq!(compiled.arguments.len(), 768,);

        // function should return 256 values
        assert_eq!(
            compiled
                .statements
                .iter()
                .filter_map(|s| match s {
                    FlatStatement::Return(v) => Some(v),
                    _ => None,
                })
                .next()
                .unwrap()
                .expressions
                .len(),
            256,
        );

        // directive should take 768 inputs and return n_var outputs
        let directive = compiled
            .statements
            .iter()
            .filter_map(|s| match s {
                FlatStatement::Directive(d) => Some(d.clone()),
                _ => None,
            })
            .next()
            .unwrap();
        assert_eq!(directive.inputs.len(), 768);
        assert_eq!(directive.outputs.len(), 26935);
        // function input should be offset by variable_count
        assert_eq!(
            compiled.arguments[0].id,
            FlatVariable::new(directive.outputs.len() + 1)
        );

        // bellman variable #0: index 0 should equal 1
        assert_eq!(
            compiled.statements[1],
            FlatStatement::Condition(
                FlatVariable::new(0).into(),
                FlatExpression::Number(FieldPrime::from(1))
            )
        );

        // bellman input #0: index 1 should equal zokrates input #0: index v_count
        assert_eq!(
            compiled.statements[2],
            FlatStatement::Condition(FlatVariable::new(1).into(), FlatVariable::new(26936).into())
        );

        let f = crate::ir::Function::from(compiled);
        let prog = crate::ir::Prog {
            main: f,
            private: vec![true; 768],
        };

        let input = (0..512).map(|_| 0).chain((0..256).map(|_| 1)).collect();

        prog.execute(&input).unwrap();
    }
}
