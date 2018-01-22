//! Module containing semantic analysis tools to run at compile time
//! The goal is to detect semantic errors such as undefined variables
//! A variable is undefined if it isn't present in the static scope
//!
//! @file semantics.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2017

use std::collections::HashSet;
use absy::*;
use field::Field;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Symbol {
	id: String,
	level: usize
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct FunctionDeclaration {
	id: String,
	return_count: usize,
	arg_count: usize,
}

// Checker, checks the semantics of a program.
pub struct Checker {
	scope: HashSet<Symbol>,
	functions: HashSet<FunctionDeclaration>,
	level: usize
}

impl Checker {
	pub fn new() -> Checker {
		Checker {
			scope: HashSet::new(),
			functions: HashSet::new(),
			level: 0
		}
	}

	#[test]
	pub fn new_with_args(scope: HashSet<Symbol>, level: usize, functions: HashSet<FunctionDeclaration>) -> Checker {
		Checker {
			scope: scope,
			functions: functions,
			level: level,
		}
	}

	pub fn check_program<T: Field>(&mut self, prog: Prog<T>) -> Result<(), String> {
		for func in prog.functions {
			self.functions.insert(FunctionDeclaration {
				id: func.clone().id,
				return_count: func.clone().return_count,
				arg_count: func.clone().arguments.len()
			});
			self.check_function(func)?;
		}
		Ok(())
	}

	fn check_function<T: Field>(&mut self, funct: Function<T>) -> Result<(), String> {
		self.level += 1;
		for arg in funct.arguments {
			self.scope.insert(Symbol {
				id: arg.id.to_string(),
				level: self.level
			});
		}
		for stat in funct.statements {
			self.check_statement(stat)?;
		}
		let current_level = self.level.clone();
		let current_scope = self.scope.clone();
		let to_remove = current_scope.iter().filter(|symbol| symbol.level == current_level);
		for symbol in to_remove {
			self.scope.remove(symbol);
		}
		self.level -= 1;
		Ok(())
	}

	fn check_statement<T: Field>(&mut self, stat: Statement<T>) -> Result<(), String> {
		match stat {
			Statement::Return(expr) => {
				self.check_expression(expr)?;
				Ok(())
			}
			Statement::Definition(id, expr) | Statement::Compiler(id, expr) => {
				self.check_expression(expr)?;
				self.scope.insert(Symbol {
					id: id.to_string(),
					level: self.level
				});
				Ok(())

			}
			Statement::Condition(lhs, rhs) => {
				self.check_expression(lhs)?;
				self.check_expression(rhs)?;
				Ok(())
			}
			Statement::For(id, _, _, statements) => {
				self.level += 1;
				let index = Symbol {
					id: id.to_string(),
					level: self.level
				};
				self.scope.insert(index.clone());
				for stat in statements {
					self.check_statement(stat)?;
				}
				self.scope.remove(&index);
				self.level -= 1;
				Ok(())
			},
            Statement::MultipleDefinition(e1, e2) => {
            	println!("{:?} = {:?}", e1, e2);
                match e1 {
                    Expression::List(ref values) => {
                    	println!("{:?}", values);
                    	let all_identifiers = values.into_iter().fold(true, |acc, x| {
                    		match x.clone() {
                    			Expression::Identifier(_) => {
                    				acc && true
                    			},
                    			_ => false
                    		}
                    	});
                    	match all_identifiers {
                    		true => {
		                        match e2 {
		                            Expression::FunctionCall(id, arguments) => {
		                            	println!("{:?} , {:?}", id, arguments);
		                            	match self.find_function(id, arguments) {
		                            		Some(f) => {
		                            			if f.return_count == values.len() {
		                            				return Ok(())
		                            			}
		                            			Err(format!("{:?} returns {} values but left side is of size {}", f.id, f.return_count, values.len()))
		                            		},
		                            		None => Err(format!("Function definition for function ??? with ??? argument(s) not found."))
		                            	}
		                            },
		                            _ => Err(format!("{:?} should be a FunctionCall", e2))
		                        }
                    		},
                    		_ => Err(format!("{:?} should be a List of Identifiers", e1))
                    	}
                    },
                    _ =>  Err(format!("{:?} should be a List", e1))
                }
            },
		}
	}

	fn check_expression<T: Field>(&mut self, expr: Expression<T>) -> Result<(), String> {
		match expr {
			Expression::Identifier(id) => {
				// check that `id` is defined in the scope
				match self.scope.iter().find(|symbol| symbol.id == id.to_string()) {
					Some(_) => Ok(()),
					None => Err(format!("{:?} is undefined", id.to_string())),
				}
			}
			Expression::Add(box e1, box e2) | Expression::Sub(box e1, box e2) | Expression::Mult(box e1, box e2) |
			Expression::Div(box e1, box e2) | Expression::Pow(box e1, box e2) => {
				self.check_expression(e1)?;
				self.check_expression(e2)?;
				Ok(())
			}
			Expression::IfElse(box condition, box consequence, box alternative) => {
				self.check_condition(condition)?; 
				self.check_expression(consequence)?;
				self.check_expression(alternative)?;
				Ok(())
			}
			Expression::FunctionCall(_, param_expressions) => {
				for expr in param_expressions {
					self.check_expression(expr)?;
				}
				Ok(())
			}
			Expression::Number(_) => Ok(()),
			Expression::List(exprs) => {
				for expr in exprs {
					self.check_expression(expr)?
				}
				Ok(())
			}
		}
	}

	fn check_condition<T: Field>(&mut self, cond: Condition<T>) -> Result<(), String> {
		match cond {
			Condition::Lt(e1, e2) |
			Condition::Le(e1, e2) |
			Condition::Eq(e1, e2) |
			Condition::Ge(e1, e2) |
			Condition::Gt(e1, e2) => {
				self.check_expression(e1)?;
				self.check_expression(e2)?;
				Ok(())
			}
		}
	}

	fn find_function<T: Field>(&mut self, id: String, args: Vec<Expression<T>>) -> Option<FunctionDeclaration> {
		self.functions.clone().into_iter().find(|fun| fun.id == id && fun.arg_count == args.len())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use field::FieldPrime;

	#[test]
	fn undefined_variable_in_statement() {
		// a = b
		// b undefined
		let statement: Statement<FieldPrime> = Statement::Definition(
			String::from("a"),
			Expression::Identifier(String::from("b"))
		);
		let mut checker = Checker::new();
		assert_eq!(checker.check_statement(statement), Err("\"b\" is undefined".to_string()));
	}

	#[test]
	fn defined_variable_in_statement() {
		// a = b
		// b defined
		let statement: Statement<FieldPrime> = Statement::Definition(
			String::from("a"),
			Expression::Identifier(String::from("b"))
		);
		let mut scope = HashSet::new();
		scope.insert(Symbol {
			id: String::from("b"),
			level: 0
		});
		let mut checker = Checker::new_with_args(scope, 1, HashSet::new());
		assert_eq!(checker.check_statement(statement), Ok(()));
	}

	#[test]
	fn declared_in_other_function() {
		// def foo():
		//   a = 1
		// def bar():
		//   return a
		// should fail
		let foo_args = Vec::<Parameter>::new();
		let mut foo_statements = Vec::<Statement<FieldPrime>>::new();
		foo_statements.push(Statement::Definition(
			String::from("a"),
			Expression::Number(FieldPrime::from(1)))
		);
		let foo = Function {
            id: "foo".to_string(),
            arguments: foo_args,
            statements: foo_statements,
            return_count: 1,
        };

        let bar_args = Vec::<Parameter>::new();
		let mut bar_statements = Vec::<Statement<FieldPrime>>::new();
		bar_statements.push(Statement::Return(
			Expression::Identifier(String::from("a"))
		));
		let bar = Function {
            id: "bar".to_string(),
            arguments: bar_args,
            statements: bar_statements,
            return_count: 1,
        };

        let mut funcs = Vec::<Function<FieldPrime>>::new();
        funcs.push(foo);
        funcs.push(bar);
        let prog = Prog {
			functions: funcs
        };

		let mut checker = Checker::new();
		assert_eq!(checker.check_program(prog), Err("\"a\" is undefined".to_string()));
	}

	#[test]
	fn declared_in_two_scopes() {
		// def foo():
		//   a = 1
		// def bar():
		//   a = 2
		//   return a
		// should pass
		let foo_args = Vec::<Parameter>::new();
		let mut foo_statements = Vec::<Statement<FieldPrime>>::new();
		foo_statements.push(Statement::Definition(
			String::from("a"),
			Expression::Number(FieldPrime::from(1)))
		);
		let foo = Function {
            id: "foo".to_string(),
            arguments: foo_args,
            statements: foo_statements,
            return_count: 1,
        };

        let bar_args = Vec::<Parameter>::new();
		let mut bar_statements = Vec::<Statement<FieldPrime>>::new();
		bar_statements.push(Statement::Definition(
			String::from("a"),
			Expression::Number(FieldPrime::from(2))
		));
		bar_statements.push(Statement::Return(
			Expression::Identifier(String::from("a"))
		));
		let bar = Function {
            id: "bar".to_string(),
            arguments: bar_args,
            statements: bar_statements,
            return_count: 1,
        };

        let mut funcs = Vec::<Function<FieldPrime>>::new();
        funcs.push(foo);
        funcs.push(bar);
        let prog = Prog {
			functions: funcs
        };

		let mut checker = Checker::new();
		assert_eq!(checker.check_program(prog), Ok(()));
	}

	#[test]
	fn for_index_after_end() {
		// def foo():
		//   for i in 0..10 do
		//   endfor
		//   return i
		// should fail
		let mut foo_statements = Vec::<Statement<FieldPrime>>::new();
		foo_statements.push(Statement::For(
			String::from("i"),
			FieldPrime::from(0),
			FieldPrime::from(10),
			Vec::<Statement<FieldPrime>>::new())
		);
		foo_statements.push(Statement::Return(
			Expression::Identifier(String::from("i"))
		));
		let foo = Function {
			id: "foo".to_string(),
			arguments: Vec::<Parameter>::new(),
			statements: foo_statements,
            return_count: 1,
		};

		let mut checker = Checker::new();
		assert_eq!(checker.check_function(foo), Err("\"i\" is undefined".to_string()));
	}

	#[test]
	fn for_index_in_for() {
		// def foo():
		//   for i in 0..10 do
		//     a = i
		//   endfor
		// should pass
		let mut foo_statements = Vec::<Statement<FieldPrime>>::new();
		let mut for_statements = Vec::<Statement<FieldPrime>>::new();
		for_statements.push(Statement::Definition(
			String::from("a"),
			Expression::Identifier(String::from("i"))
		));
		foo_statements.push(Statement::For(
			String::from("i"),
			FieldPrime::from(0),
			FieldPrime::from(10),
			for_statements
		));
		let foo = Function {
			id: "foo".to_string(),
			arguments: Vec::<Parameter>::new(),
			statements: foo_statements,
            return_count: 1,
		};

		let mut checker = Checker::new();
		assert_eq!(checker.check_function(foo), Ok(()));
	}

	#[test]
	fn arity_mismatch() {
		// def foo():
		//   return 1, 2
		// def bar():
		//   c = foo()
		// should fail
		let bar_statements: Vec<Statement<FieldPrime>> = vec![Statement::MultipleDefinition(
			Expression::List(vec![Expression::Identifier("c".to_string())]), 
			Expression::FunctionCall("foo".to_string(), vec![])
		)];

		let foo = FunctionDeclaration {
			id: "foo".to_string(),
			arg_count: 0,
            return_count: 2,
		};

		let mut functions = HashSet::new();
		functions.insert(foo);

		let bar = Function {
			id: "bar".to_string(),
			arguments: vec![],
			statements: bar_statements,
			return_count: 1
		};

		let mut checker = Checker::new_with_args(HashSet::new(), 0, functions);
		assert_eq!(checker.check_function(bar), Err(("\"foo\" returns 2 values but left side is of size 1".to_string())));
	}

	#[test]
	fn function_undefined() {
		// def bar():
		//   c = foo()
		// should fail
		let bar_statements: Vec<Statement<FieldPrime>> = vec![Statement::MultipleDefinition(
			Expression::List(vec![Expression::Identifier("c".to_string())]), 
			Expression::FunctionCall("foo".to_string(), vec![])
		)];

		let bar = Function {
			id: "bar".to_string(),
			arguments: vec![],
			statements: bar_statements,
			return_count: 1
		};

		let mut checker = Checker::new_with_args(HashSet::new(), 0, HashSet::new());
		assert_eq!(checker.check_function(bar), Err(("Function definition for function ??? with ??? argument(s) not found.".to_string())));
	}

	#[test]
	fn return_undefined() {
		// def bar():
		//   return a, b
		// should fail
		let bar_statements: Vec<Statement<FieldPrime>> = vec![Statement::Return(
			Expression::List(vec![
				Expression::Identifier("a".to_string()),
				Expression::Identifier("b".to_string())
			])
		)];

		let bar = Function {
			id: "bar".to_string(),
			arguments: vec![],
			statements: bar_statements,
			return_count: 2
		};

		let mut checker = Checker::new_with_args(HashSet::new(), 0, HashSet::new());
		assert_eq!(checker.check_function(bar), Err(("\"a\" is undefined".to_string())));
	}
}