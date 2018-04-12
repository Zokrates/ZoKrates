//! Module containing the `Optimizer` to optimize a flattened program.
//!
//! @file optimizer.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

use absy::*;
use field::Field;
use std::collections::{HashMap};

pub struct Optimizer {
	/// Map of renamings for reassigned variables while processing the program.
	substitution: HashMap<String,String>,
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
			substitution: HashMap::new(),
    		next_var_idx: Counter {
    			value: 0
    		}
		}
	}

	pub fn optimize_program<T: Field>(&mut self, prog: Prog<T>) -> Result<Prog<T>, String> {
		let optimized_program = Prog {
			functions: prog.functions.into_iter().filter_map(|func| {
				if func.id == "main" {
					return Some(self.optimize_function(func).unwrap());
				}
				return None;
			}).collect()
		};
		Ok(optimized_program)
	}

	pub fn optimize_function<T: Field>(&mut self, funct: Function<T>) -> Result<Function<T>, String> {

		// Add arguments to substitution map
		for arg in &funct.arguments {
			self.substitution.insert(arg.id.clone(), format!("_{}", self.next_var_idx.increment()));
		};

		// generate substitution map
		//
		//	(b = a, c = b) => ( b -> a, c -> a )
		// The first variable to appear is used for its synonyms.

		for statement in &funct.statements {
			match statement {
				// Synonym definition
				// if the right side of the assignment is already being reassigned to `x`,
				// reassign the left side to `x` as well, otherwise reassign to a new variable
				Statement::Definition(left, Expression::Identifier(right)) => {
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
				Statement::Definition(left, _) => {
					self.substitution.insert(left.clone(), format!("_{}", self.next_var_idx.increment()));
				},
				// Compiler statements introduce variables before they are defined, so add them to the substitution
				Statement::Compiler(id, _) => {
					self.substitution.insert(id.clone(), format!("_{}", self.next_var_idx.increment()));
				},
				_ => ()
			}
		}

		// generate optimized statements by removing synonym declarations and renaming variables
		let optimized_statements = funct.statements.iter().filter_map(|statement| {
			match statement {
				// filter out synonyms definitions
				Statement::Definition(_, Expression::Identifier(_)) => {
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

		Ok(optimized_funct)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use field::FieldPrime;

	#[test]
	fn remove_synonyms() {
		let f: Function<FieldPrime> = Function {
            id: "foo".to_string(),
            arguments: vec![Parameter {id: "a".to_string(), private: false}],
            statements: vec![
            	Statement::Definition("b".to_string(), Expression::Identifier("a".to_string())),
            	Statement::Definition("c".to_string(), Expression::Identifier("b".to_string())),
            	Statement::Return(ExpressionList {
            		expressions: vec![Expression::Identifier("c".to_string())]
            	})
            ],
            return_count: 1
        };

        let optimized: Function<FieldPrime> = Function {
            id: "foo".to_string(),
        	arguments: vec![Parameter {id: "_0".to_string(), private: false}],
        	statements: vec![
        		Statement::Return(ExpressionList {
            		expressions: vec![Expression::Identifier("_0".to_string())]
            	})
        	],
        	return_count: 1
        };

        let mut optimizer = Optimizer::new();
        assert_eq!(optimizer.optimize_function(f), Ok(optimized));
	}


	#[test]
	fn remove_multiple_synonyms() {
		let f: Function<FieldPrime> = Function {
            id: "foo".to_string(),
            arguments: vec![Parameter {id: "a".to_string(), private: false}],
            statements: vec![
            	Statement::Definition("b".to_string(), Expression::Identifier("a".to_string())),
            	Statement::Definition("d".to_string(), Expression::Number(FieldPrime::from(1))),
            	Statement::Definition("c".to_string(), Expression::Identifier("b".to_string())),
            	Statement::Definition("e".to_string(), Expression::Identifier("d".to_string())),
            	Statement::Return(ExpressionList {
            		expressions: vec![Expression::Identifier("c".to_string()), Expression::Identifier("e".to_string())]
            	})
            ],
            return_count: 2
        };

        let optimized: Function<FieldPrime> = Function {
            id: "foo".to_string(),
        	arguments: vec![Parameter {id: "_0".to_string(), private: false}],
        	statements: vec![
            	Statement::Definition("_1".to_string(), Expression::Number(FieldPrime::from(1))),
        		Statement::Return(ExpressionList {
            		expressions: vec![Expression::Identifier("_0".to_string()), Expression::Identifier("_1".to_string())]
            	})
        	],
        	return_count: 2
        };

        let mut optimizer = Optimizer::new();
        assert_eq!(optimizer.optimize_function(f), Ok(optimized));
	}
}