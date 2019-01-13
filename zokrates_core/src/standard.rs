use flat_absy::{FlatExpression, FlatExpressionList, FlatFunction, FlatStatement};
use flat_absy::{FlatParameter, FlatVariable};
use helpers::{DirectiveStatement, Helper, LibsnarkGadgetHelper};
use reduce::Reduce;
use std::collections::{BTreeMap, HashSet};
use types::{Signature, Type};
use zokrates_field::field::Field;

// for r1cs import, can be moved.
// r1cs data structure reflecting JSON standard format:
// {
//     input_count: count,  // # of inputs to pass
//     outputs: [offset_42, offset_63, offset_55],  // indices of the outputs in the witness
//     constraints: [   // constraints verified by the witness
//         [
//             {offset_1: value_a1, offset_2: value_a2, ...},
//             {offset_1: value_b1, offset_2: value_b2, ...},
//             {offset_1: value_c1, offset_2: value_c2, ...}
//         ]
// }
#[derive(Serialize, Deserialize, Debug)]
pub struct R1CS {
    pub input_count: usize,
    pub outputs: Vec<usize>,
    pub constraints: Vec<Constraint>,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct Witness {
    pub variables: Vec<usize>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct Constraint {
    a: BTreeMap<usize, String>,
    b: BTreeMap<usize, String>,
    c: BTreeMap<usize, String>,
}

pub struct DirectiveR1CS {
    pub r1cs: R1CS,
    pub directive: LibsnarkGadgetHelper,
}

impl<T: Field> Into<FlatStatement<T>> for Constraint {
    fn into(self: Constraint) -> FlatStatement<T> {
        let rhs_a = match self
            .a
            .into_iter()
            .map(|(key, val)| {
                FlatExpression::Mult(
                    box FlatExpression::Number(T::from_dec_string(val.to_string())),
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

        let rhs_b = match self
            .b
            .into_iter()
            .map(|(key, val)| {
                FlatExpression::Mult(
                    box FlatExpression::Number(T::from_dec_string(val.to_string())),
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

        let lhs = match self
            .c
            .into_iter()
            .map(|(key, val)| {
                FlatExpression::Mult(
                    box FlatExpression::Number(T::from_dec_string(val.to_string())),
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

impl<T: Field> Into<FlatFunction<T>> for DirectiveR1CS {
    fn into(self: DirectiveR1CS) -> FlatFunction<T> {
        let r1cs = self.r1cs;

        // determine the number of variables, assuming there is no i so that column i is only zeroes in a, b and c
        let mut variables_set = HashSet::new();
        for constraint in r1cs.constraints.iter() {
            for (key, _) in &constraint.a {
                variables_set.insert(key.clone());
            }
            for (key, _) in &constraint.b {
                variables_set.insert(key.clone());
            }
            for (key, _) in &constraint.c {
                variables_set.insert(key.clone());
            }
        }

        let variables_count = variables_set.len();

        // insert flattened statements to represent constraints
        let mut statements: Vec<FlatStatement<T>> =
            r1cs.constraints.into_iter().map(|c| c.into()).collect();

        // define the entire witness
        let variables = vec![0; variables_count]
            .iter()
            .enumerate()
            .map(|(i, _)| FlatVariable::new(i))
            .collect();

        // define the inputs with dummy variables: arguments to the function and to the directive
        let input_variables: Vec<FlatVariable> = vec![0; r1cs.input_count]
            .iter()
            .enumerate()
            .map(|(i, _)| FlatVariable::new(i + variables_count))
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

        // define which subset of the witness is returned
        let outputs: Vec<FlatExpression<T>> = r1cs
            .outputs
            .into_iter()
            .map(|o| FlatExpression::Identifier(FlatVariable::new(o)))
            .collect();

        let signature = Signature {
            inputs: vec![Type::FieldElement; inputs.len()],
            outputs: vec![Type::FieldElement; outputs.len()],
        };

        // insert a directive to set the witness based on the libsnark gadget and  inputs
        match self.directive {

            LibsnarkGadgetHelper::Sha256Round => {
                statements.insert(
                    0,
                    FlatStatement::Directive(DirectiveStatement {
                        outputs: variables,
                        inputs: inputs,
                        helper: Helper::LibsnarkGadget(LibsnarkGadgetHelper::Sha256Round),
                    }),
                );
            }
        }

        // insert a statement to return the subset of the witness
        statements.push(FlatStatement::Return(FlatExpressionList {
            expressions: outputs,
        }));

        FlatFunction {
            id: "main".to_owned(),
            arguments,
            statements,
            signature,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json;
    use zokrates_field::field::FieldPrime;

    #[test]
    fn deserialize_constraint() {
        let constraint = r#"[{"2026": "1"}, {"0": "1", "2026": "1751751751751751751751751751751751751751751"}, {"0": "0"}]"#;
        let _c: Constraint = serde_json::from_str(constraint).unwrap();
    }

    #[test]
    fn constraint_into_flat_statement() {
        let constraint = r#"[{"2026": "1"}, {"0": "1", "2026": "1751751751751751751751751751751751751751751"}, {"0": "0"}]"#;
        let c: Constraint = serde_json::from_str(constraint).unwrap();
        let _statement: FlatStatement<FieldPrime> = c.into();
    }

    #[test]
    fn generate_sha256_constraints() {
        use flat_absy::FlatProg;
        use libsnark::get_sha256round_constraints;
        let r1cs: R1CS = serde_json::from_str(&get_sha256round_constraints()).unwrap();
        let v_count = r1cs.variable_count;

        let dr1cs: DirectiveR1CS = DirectiveR1CS {
            r1cs,
            directive: LibsnarkGadgetHelper::Sha256Round,
        };
        let compiled: FlatProg<FieldPrime> = FlatProg::from(dr1cs);

        // libsnark variable #0: index 0 should equal 1
        assert_eq!(
            compiled.functions[0].statements[1],
            FlatStatement::Condition(
                FlatVariable::new(0).into(),
                FlatExpression::Number(FieldPrime::from(1))
            )
        );

        // libsnark input #0: index 1 should equal zokrates input #0: index v_count
        assert_eq!(
            compiled.functions[0].statements[2],
            FlatStatement::Condition(
                FlatVariable::new(1).into(),
                FlatVariable::new(v_count).into()
            )
        );
    }
}
