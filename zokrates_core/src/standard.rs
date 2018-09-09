
use std::collections::{BTreeMap, HashSet};
use flat_absy::{FlatStatement, FlatExpression, FlatFunction, FlatExpressionList};
use field::Field;
use flat_absy::flat_parameter::FlatParameter;
use reduce::Reduce;
use helpers::{DirectiveStatement, Helper, LibsnarkGadgetHelper};

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
    pub variables: Vec<usize>
}

#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct Constraint {
	a: BTreeMap<String, String>,
	b: BTreeMap<String, String>,
	c: BTreeMap<String, String>,
}

impl<T: Field> Into<FlatStatement<T>> for Constraint {
	fn into(self: Constraint) -> FlatStatement<T> {
		let rhs_a = match self.a.iter()
			.map(|(key, val)| FlatExpression::Mult(box FlatExpression::Number(T::from_dec_string(val.to_string())), box FlatExpression::Identifier(format!("inter{}",key.clone()))))
			.reduce(|acc, e| FlatExpression::Add(box acc, box e)) {
                Some(e @ FlatExpression::Mult(..)) => FlatExpression::Add(box FlatExpression::Number(T::zero()), box e), // the R1CS serializer only recognizes Add
                Some(e) => e,
                None => FlatExpression::Number(T::zero())
            };
		
		let rhs_b = match self.b.iter()
			.map(|(key, val)| FlatExpression::Mult(box FlatExpression::Number(T::from_dec_string(val.to_string())), box FlatExpression::Identifier(format!("inter{}",key.clone()))))
			.reduce(|acc, e| FlatExpression::Add(box acc, box e)) {
                Some(e @ FlatExpression::Mult(..)) => FlatExpression::Add(box FlatExpression::Number(T::zero()), box e), // the R1CS serializer only recognizes Add
                Some(e) => e,
                None => FlatExpression::Number(T::zero())
            };
		
		let lhs = match self.c.iter()
			.map(|(key, val)| FlatExpression::Mult(box FlatExpression::Number(T::from_dec_string(val.to_string())), box FlatExpression::Identifier(format!("inter{}",key.clone()))))
			.reduce(|acc, e| FlatExpression::Add(box acc, box e)) {
                Some(e @ FlatExpression::Mult(..)) => FlatExpression::Add(box FlatExpression::Number(T::zero()), box e), // the R1CS serializer only recognizes Add
                Some(e) => e,
                None => FlatExpression::Number(T::zero())
            };

		FlatStatement::Condition(lhs, FlatExpression::Mult(box rhs_a, box rhs_b))
	}
}

impl<T: Field> Into<FlatFunction<T>> for R1CS {
	fn into(self: R1CS) -> FlatFunction<T> {

		// determine the number of variables, assuming there is no i so that column i is only zeroes in a, b and c
        let mut variables_set = HashSet::new();
        for constraint in self.constraints.iter() {
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
        let mut statements: Vec<FlatStatement<T>> = self.constraints.into_iter().map(|c| c.into()).collect();

        // define the entire witness
        let variables = vec![0; variables_count].iter().enumerate().map(|(i, _)| format!("inter{}", i)).collect();

        // define the inputs with dummy variables: arguments to the function and to the directive
        let inputs: Vec<String> = vec![0; self.input_count].iter().enumerate().map(|(i, _)| format!("input{}", i)).collect();
        let input_parameters = inputs.iter().map(|i| FlatParameter { id: i.clone(), private: true }).collect();

        // define which subset of the witness is returned
        let outputs: Vec<FlatExpression<T>> = self.outputs.iter()
         				.map(|o| FlatExpression::Identifier(format!("inter{}", o))).collect();

        let return_count = outputs.len();

        // insert a directive to set the witness based on the inputs
        statements.insert(0, FlatStatement::Directive(
            DirectiveStatement {
                outputs: variables,
                inputs: inputs,
                helper: Helper::LibsnarkGadget(LibsnarkGadgetHelper::Sha256Compress),
            })
        );

        // insert a statement to return the subset of the witness
        statements.push(FlatStatement::Return(
        	FlatExpressionList {
        		expressions: outputs
         	})
        );
        
        FlatFunction { 
            id: "main".to_owned(), 
            arguments: input_parameters, 
            statements: statements, 
            return_count: return_count
        }
	}
} 

#[cfg(test)]
mod tests {
	use super::*;
	use field::FieldPrime;
	use serde_json;

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
}

