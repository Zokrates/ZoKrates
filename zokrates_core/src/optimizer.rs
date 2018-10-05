//! Module containing the `Optimizer` to optimize a flattened program.
//!
//! @file optimizer.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

use substitution::direct_substitution::DirectSubstitution;
use substitution::Substitution;
use flat_absy::*;
use field::Field;
use flat_absy::flat_variable::FlatVariable;

pub struct Optimizer {
	/// Map of renamings for reassigned variables while processing the program.
	substitution: DirectSubstitution,
	/// Index of the next introduced variable while processing the program.
	next_var_idx: Counter
}

pub struct Counter {
	value: usize
}

impl Counter {
	fn increment(&mut self) -> usize {
		let index = self.value;
		self.value = self.value + 1;
		index
	}
}

impl Optimizer {
	pub fn new() -> Optimizer {
		Optimizer {
			substitution: DirectSubstitution::new(),
    		next_var_idx: Counter {
    			value: 0
    		}
		}
	}

	pub fn optimize_program<T: Field>(&mut self, prog: FlatProg<T>) -> FlatProg<T> {
		let optimized_program = FlatProg {
			functions: prog.functions.into_iter().filter_map(|func| {
				if func.id == "main" {
					return Some(self.optimize_function(func));
				}
				return None;
			}).collect()
		};
		optimized_program
	}

	pub fn optimize_function<T: Field>(&mut self, funct: FlatFunction<T>) -> FlatFunction<T> {
		// Add arguments to substitution map
		for arg in funct.arguments.clone() {
			self.substitution.insert(arg.id, FlatVariable::new(self.next_var_idx.increment()));
		};

		// generate substitution map
		//
		//	(b = a, c = b) => ( b -> a, c -> a )
		// The first variable to appear is used for its synonyms.

		for statement in &funct.statements {
			match *statement {
				// Synonym definition
				// if the right side of the assignment is already being reassigned to `x`,
				// reassign the left side to `x` as well, otherwise reassign to a new variable
				FlatStatement::Definition(ref left, FlatExpression::Identifier(ref right)) => {
					let r = match self.substitution.get(right) {
						Some(value) => {
							value.clone()
						},
						None => {
							FlatVariable::new(self.next_var_idx.increment())
						}
					};
					self.substitution.insert(left.clone(), r);
				},
				// Other definitions
				FlatStatement::Definition(ref left, _) => {
					self.substitution.insert(left.clone(), FlatVariable::new(self.next_var_idx.increment()));
				},
				FlatStatement::Directive(ref d) => {
					for o in d.outputs.iter() {
						self.substitution.insert(o.clone(), FlatVariable::new(self.next_var_idx.increment()));
					}
				},
				_ => ()
			}
		}

		// generate optimized statements by removing synonym declarations and renaming variables
		let optimized_statements = funct.statements.into_iter().filter_map(|statement| {
			match statement {
				// filter out synonyms definitions
				FlatStatement::Definition(_, FlatExpression::Identifier(_)) => {
					None
				},
				// substitute all other statements
				_ => {
					Some(statement.apply_direct_substitution(&self.substitution))
				}
			}
		}).collect();

		// generate optimized arguments by renaming them
		let optimized_arguments = funct.arguments.into_iter().map(|arg| arg.apply_direct_substitution(&self.substitution)).collect();

		FlatFunction {
			arguments: optimized_arguments,
			statements: optimized_statements,
			..funct
		}
	}
}

#[cfg(test)]
mod tests {
	use types::{Type, Signature};
	use super::*;
	use field::FieldPrime;
	use flat_absy::flat_parameter::FlatParameter;

	#[test]
	fn remove_synonyms() {

		// def main(x):
		//    y = x
		//    z = y
		//    return z

		let x = FlatVariable::new(0);
		let y = FlatVariable::new(1);
		let z = FlatVariable::new(2);

		let f: FlatFunction<FieldPrime> = FlatFunction {
            id: "foo".to_string(),
            arguments: vec![FlatParameter {id: x, private: false}],
            statements: vec![
            	FlatStatement::Definition(y, FlatExpression::Identifier(x)),
            	FlatStatement::Definition(z, FlatExpression::Identifier(y)),
            	FlatStatement::Return(FlatExpressionList {
            		expressions: vec![FlatExpression::Identifier(z)]
            	})
            ],
            signature: Signature {
            	inputs: vec![Type::FieldElement],
            	outputs: vec![Type::FieldElement]
            }
        };

        let optimized: FlatFunction<FieldPrime> = FlatFunction {
            id: "foo".to_string(),
        	arguments: vec![FlatParameter {id: x, private: false}],
        	statements: vec![
        		FlatStatement::Return(FlatExpressionList {
            		expressions: vec![FlatExpression::Identifier(x)]
            	})
        	],
        	signature: Signature {
            	inputs: vec![Type::FieldElement],
            	outputs: vec![Type::FieldElement]
            }
        };

        let mut optimizer = Optimizer::new();
        assert_eq!(optimizer.optimize_function(f), optimized);
	}


	#[test]
	fn remove_multiple_synonyms() {

		// def main(x):
		//    y = x
		//    t = 1
		//    z = y
		//    w = t
		//    return z, w

		let x = FlatVariable::new(0);
		let y = FlatVariable::new(1);
		let z = FlatVariable::new(2);
		let t = FlatVariable::new(3);
		let w = FlatVariable::new(4);

		let f: FlatFunction<FieldPrime> = FlatFunction {
            id: "foo".to_string(),
            arguments: vec![FlatParameter {id: x, private: false}],
            statements: vec![
            	FlatStatement::Definition(y, FlatExpression::Identifier(x)),
            	FlatStatement::Definition(t, FlatExpression::Number(FieldPrime::from(1))),
            	FlatStatement::Definition(z, FlatExpression::Identifier(y)),
            	FlatStatement::Definition(w, FlatExpression::Identifier(t)),
            	FlatStatement::Return(FlatExpressionList {
            		expressions: vec![FlatExpression::Identifier(z), FlatExpression::Identifier(w)]
            	})
            ],
        	signature: Signature {
            	inputs: vec![Type::FieldElement],
            	outputs: vec![Type::FieldElement, Type::FieldElement]
            }
        };

        let optimized: FlatFunction<FieldPrime> = FlatFunction {
            id: "foo".to_string(),
        	arguments: vec![FlatParameter {id: x, private: false}],
        	statements: vec![
            	FlatStatement::Definition(y, FlatExpression::Number(FieldPrime::from(1))),
        		FlatStatement::Return(FlatExpressionList {
            		expressions: vec![FlatExpression::Identifier(x), FlatExpression::Identifier(y)]
            	})
        	],
        	signature: Signature {
            	inputs: vec![Type::FieldElement],
            	outputs: vec![Type::FieldElement, Type::FieldElement]
            }
        };

        let mut optimizer = Optimizer::new();
        assert_eq!(optimizer.optimize_function(f), optimized);
	}
}