//! Module containing the `Optimizer` to optimize a flattened program.
//!
//! @file optimizer.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

use prefixed_substitution::PrefixedSubstitution;
use substitution::Substitution;
use flat_absy::*;
use field::Field;

pub struct Optimizer {
	/// Map of renamings for reassigned variables while processing the program.
	substitution: PrefixedSubstitution,
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
			substitution: PrefixedSubstitution::new(),
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
		for arg in &funct.arguments {
			self.substitution.insert(arg.id.clone(), format!("_{}", self.next_var_idx.increment()));
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
							format!("_{}", self.next_var_idx.increment())
						}
					};
					self.substitution.insert(left.clone(), r);
				},
				// Other definitions
				FlatStatement::Definition(ref left, _) => {
					self.substitution.insert(left.clone(), format!("_{}", self.next_var_idx.increment()));
				},
				FlatStatement::Directive(ref d) => {
					for o in d.outputs.iter() {
						self.substitution.insert(o.clone(), format!("_{}", self.next_var_idx.increment()));
					}
				},
				_ => ()
			}
		}

		// generate optimized statements by removing synonym declarations and renaming variables
		let optimized_statements = funct.statements.iter().filter_map(|statement| {
			match *statement {
				// filter out synonyms definitions
				FlatStatement::Definition(_, FlatExpression::Identifier(_)) => {
					None
				},
				// substitute all other statements
				_ => {
					Some(statement.apply_substitution(&self.substitution))
				}
			}
		}).collect();

		// generate optimized arguments by renaming them
		let optimized_arguments = funct.arguments.iter().map(|arg| arg.apply_substitution(&self.substitution)).collect();

		// clone function
		let mut optimized_funct = funct.clone();
		// update statements with optimized ones
		optimized_funct.statements = optimized_statements;
		optimized_funct.arguments = optimized_arguments;

		optimized_funct
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use field::FieldPrime;
	use parameter::Parameter;

	#[test]
	fn remove_synonyms() {
		let f: FlatFunction<FieldPrime> = FlatFunction {
            id: "foo".to_string(),
            arguments: vec![Parameter {id: "a".to_string(), private: false}],
            statements: vec![
            	FlatStatement::Definition("b".to_string(), FlatExpression::Identifier("a".to_string())),
            	FlatStatement::Definition("c".to_string(), FlatExpression::Identifier("b".to_string())),
            	FlatStatement::Return(FlatExpressionList {
            		expressions: vec![FlatExpression::Identifier("c".to_string())]
            	})
            ],
            return_count: 1
        };

        let optimized: FlatFunction<FieldPrime> = FlatFunction {
            id: "foo".to_string(),
        	arguments: vec![Parameter {id: "_0".to_string(), private: false}],
        	statements: vec![
        		FlatStatement::Return(FlatExpressionList {
            		expressions: vec![FlatExpression::Identifier("_0".to_string())]
            	})
        	],
        	return_count: 1
        };

        let mut optimizer = Optimizer::new();
        assert_eq!(optimizer.optimize_function(f), optimized);
	}


	#[test]
	fn remove_multiple_synonyms() {
		let f: FlatFunction<FieldPrime> = FlatFunction {
            id: "foo".to_string(),
            arguments: vec![Parameter {id: "a".to_string(), private: false}],
            statements: vec![
            	FlatStatement::Definition("b".to_string(), FlatExpression::Identifier("a".to_string())),
            	FlatStatement::Definition("d".to_string(), FlatExpression::Number(FieldPrime::from(1))),
            	FlatStatement::Definition("c".to_string(), FlatExpression::Identifier("b".to_string())),
            	FlatStatement::Definition("e".to_string(), FlatExpression::Identifier("d".to_string())),
            	FlatStatement::Return(FlatExpressionList {
            		expressions: vec![FlatExpression::Identifier("c".to_string()), FlatExpression::Identifier("e".to_string())]
            	})
            ],
            return_count: 2
        };

        let optimized: FlatFunction<FieldPrime> = FlatFunction {
            id: "foo".to_string(),
        	arguments: vec![Parameter {id: "_0".to_string(), private: false}],
        	statements: vec![
            	FlatStatement::Definition("_1".to_string(), FlatExpression::Number(FieldPrime::from(1))),
        		FlatStatement::Return(FlatExpressionList {
            		expressions: vec![FlatExpression::Identifier("_0".to_string()), FlatExpression::Identifier("_1".to_string())]
            	})
        	],
        	return_count: 2
        };

        let mut optimizer = Optimizer::new();
        assert_eq!(optimizer.optimize_function(f), optimized);
	}
}