use flat_absy::{FlatExpression, FlatExpressionList, FlatFunction, FlatStatement};
use flat_absy::{FlatParameter, FlatVariable};
use helpers::{DirectiveStatement, Helper, RustHelper};
use reduce::Reduce;
use types::{Signature, Type};
use zokrates_embed::{generate_sha256_round_constraints, BellmanConstraint};
use zokrates_field::field::Field;

impl<T: Field> From<BellmanConstraint<T::BellmanEngine>> for FlatStatement<T> {
    fn from(c: zokrates_embed::BellmanConstraint<T::BellmanEngine>) -> FlatStatement<T> {
        let rhs_a = match c
            .a
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
        };

        let rhs_b = match c
            .b
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
        };

        let lhs = match c
            .c
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
        };

        FlatStatement::Condition(lhs, FlatExpression::Mult(box rhs_a, box rhs_b))
    }
}

pub fn sha_round<T: Field>() -> FlatFunction<T> {
    let (r1cs, input, current_hash, output) =
        generate_sha256_round_constraints::<T::BellmanEngine>();

    let variable_count = r1cs.aux_count + 1; // auxiliary and ONE

    // define the inputs with dummy variables: arguments to the function and to the directive
    let input_variables: Vec<FlatVariable> = input
        .iter()
        .chain(current_hash.iter())
        .map(|i| FlatVariable::new(i + variable_count))
        .collect();
    let arguments = input_variables
        .iter()
        .map(|i| FlatParameter {
            id: i.clone(),
            private: true,
        })
        .collect();
    let inputs: Vec<FlatExpression<T>> = input_variables
        .into_iter()
        .map(|i| FlatExpression::Identifier(i))
        .collect();

    let input_binding_statements = // bind first variable to ~one
    std::iter::once(FlatStatement::Condition(
        FlatVariable::new(0).into(),
        FlatExpression::Number(T::from(1)),
    ))
    // bind input and current_hash to inputs
    .chain(input.iter().chain(current_hash.iter()).map(|i| {
        FlatStatement::Condition(
            FlatVariable::new(*i).into(),
            FlatVariable::new(i + variable_count).into(),
        )
    }));

    // insert flattened statements to represent constraints
    let constraint_statements = r1cs.constraints.into_iter().map(|c| c.into());

    // define the entire witness
    let variables = (0..variable_count).map(|i| FlatVariable::new(i)).collect();

    // define which subset of the witness is returned
    let outputs: Vec<FlatExpression<T>> = output
        .into_iter()
        .map(|o| FlatExpression::Identifier(FlatVariable::new(o)))
        .collect();

    let signature = Signature {
        inputs: vec![Type::FieldElement; inputs.len()],
        outputs: vec![Type::FieldElement; outputs.len()],
    };

    // insert a directive to set the witness based on the bellman gadget and  inputs
    let directive_statement = FlatStatement::Directive(DirectiveStatement {
        outputs: variables,
        inputs: inputs,
        helper: Helper::Rust(RustHelper::Sha256Round),
    });

    // insert a statement to return the subset of the witness
    let return_statement = FlatStatement::Return(FlatExpressionList {
        expressions: outputs,
    });

    let statements = std::iter::once(directive_statement)
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
                .inputs(vec![Type::FieldElement; 768])
                .outputs(vec![Type::FieldElement; 256])
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

        let f = ::ir::Function::from(compiled);
        let prog = ::ir::Prog {
            main: f,
            private: vec![true; 768],
        };

        let input = (0..512).map(|_| 0).chain((0..256).map(|_| 1)).collect();

        prog.execute(&input).unwrap();
    }
}
