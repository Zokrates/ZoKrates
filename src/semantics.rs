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
use std::fmt;

#[derive(PartialEq, Debug)]
pub struct Error {
	message: String
}

impl fmt::Display for Error {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{}", self.message)
	}
}

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

	pub fn check_program<T: Field>(&mut self, prog: Prog<T>) -> Result<(), Error> {
		for func in prog.functions {
			self.check_function(&func)?;
			self.functions.insert(FunctionDeclaration {
				id: func.id,
				return_count: func.return_count,
				arg_count: func.arguments.len()
			});
		}
		self.check_single_main()?;
		Ok(())
	}

	fn check_single_main(&mut self) -> Result<(), Error> {
		match self.functions.clone().into_iter().filter(|fun| fun.id == "main").count() {
			1 => Ok(()),
			0 => Err(Error { message: format!("No main function found") }),
			n => Err(Error { message: format!("Only one main function allowed, found {}", n) })
		}
	}

	fn check_function<T: Field>(&mut self, funct: &Function<T>) -> Result<(), Error> {
		match self.find_function(&funct.id, funct.arguments.len()) {
			Some(_) => {
				return Err(Error { message: format!("Duplicate definition for function {} with {} arguments", funct.id, funct.arguments.len()) })
			},
			None => {

			}
		}
		self.level += 1;
		for arg in funct.arguments.clone() {
			self.scope.insert(Symbol {
				id: arg.id.to_string(),
				level: self.level
			});
		}
		for stat in funct.statements.clone() {
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

	fn check_statement<T: Field>(&mut self, stat: Statement<T>) -> Result<(), Error> {
		match stat {
			Statement::Return(list) => {
				self.check_expression_list(list)?;
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
            Statement::MultipleDefinition(ids, rhs) => {
        		// All elements of the left side have to be identifiers
                match rhs {
                	// Right side has to be a function call
                    Expression::FunctionCall(ref fun_id, ref arguments) => {
                    	match self.find_function(fun_id, arguments.len()) {
                    		// the function has to be defined
                    		Some(f) => {
                    			// the return count has to match the left side
                    			if f.return_count == ids.len() {
                    				// check the arguments
                    				for arg in arguments {
                    					self.check_expression(arg.clone())?;
                    				}

                    				for id in ids {
                        				self.scope.insert(Symbol {
											id: id.to_string(),
											level: self.level
										});
                    				}
                    				return Ok(())
                    			}
                    			Err(Error { message: format!("{} returns {} values but left side is of size {}", f.id, f.return_count, ids.len()) })
                    		},
                    		None => Err(Error { message: format!("Function definition for function {} with {} argument(s) not found.", fun_id, arguments.len()) })
                    	}
                    },
                    _ => Err(Error { message: format!("{} should be a FunctionCall", rhs) })
                }
            },
		}
	}

	fn check_expression<T: Field>(&mut self, expr: Expression<T>) -> Result<(), Error> {
		match expr {
			Expression::Identifier(id) => {
				// check that `id` is defined in the scope
				match self.scope.iter().find(|symbol| symbol.id == id.to_string()) {
					Some(_) => Ok(()),
					None => Err(Error { message: format!("{} is undefined", id.to_string()) }),
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
			Expression::FunctionCall(ref fun_id, ref arguments) => {
				match self.find_function(fun_id, arguments.len()) {
					// the function has to be defined
					Some(f) => {
						if f.return_count == 1 { // Functions must return a single value when not in a MultipleDefinition
							for expr in arguments {
								self.check_expression(expr.clone())?;
							}
							return Ok(())
						}
						Err(Error { message: format!("{} returns {} values but is called outside of a definition", fun_id, f.return_count) })
					},
                   	None => Err(Error { message: format!("Function definition for function {} with {} argument(s) not found.", fun_id, arguments.len()) })
				}
			}
			Expression::Number(_) => Ok(())
		}
	}

	fn check_expression_list<T: Field>(&mut self, list: ExpressionList<T>) -> Result<(), Error> {
		for expr in list.expressions { // implement Iterator trait?
			self.check_expression(expr)?
		}
		Ok(())
	}

	fn check_condition<T: Field>(&mut self, cond: Condition<T>) -> Result<(), Error> {
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

	fn find_function(&mut self, id: &str, arg_count: usize) -> Option<FunctionDeclaration> {
		self.functions.clone().into_iter().find(|fun| fun.id == id && fun.arg_count == arg_count)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use field::FieldPrime;

	pub fn new_with_args(scope: HashSet<Symbol>, level: usize, functions: HashSet<FunctionDeclaration>) -> Checker {
		Checker {
			scope: scope,
			functions: functions,
			level: level,
		}
	}

	#[test]
	fn undefined_variable_in_statement() {
		// a = b
		// b undefined
		let statement: Statement<FieldPrime> = Statement::Definition(
			String::from("a"),
			Expression::Identifier(String::from("b"))
		);
		let mut checker = Checker::new();
		assert_eq!(checker.check_statement(statement), Err(Error { message: "b is undefined".to_string() }));
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
		let mut checker = new_with_args(scope, 1, HashSet::new());
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
			ExpressionList {
				expressions: vec![Expression::Identifier(String::from("a"))]
			}
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
		assert_eq!(checker.check_program(prog), Err(Error { message: "a is undefined".to_string() }));
	}

	#[test]
	fn declared_in_two_scopes() {
		// def foo():
		//   a = 1
		// def bar():
		//   a = 2
		//   return a
		// def main():
		//   return 1
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
			ExpressionList {
				expressions: vec![Expression::Identifier(String::from("a"))]
			}
		));
		let bar = Function {
            id: "bar".to_string(),
            arguments: bar_args,
            statements: bar_statements,
            return_count: 1,
        };

        let main_args = Vec::<Parameter>::new();
		let mut main_statements = Vec::<Statement<FieldPrime>>::new();
		main_statements.push(Statement::Return(
			ExpressionList {
				expressions: vec![Expression::Number(FieldPrime::from(1))]
			})
		);
		let main = Function {
            id: "main".to_string(),
            arguments: main_args,
            statements: main_statements,
            return_count: 1,
        };

        let mut funcs = Vec::<Function<FieldPrime>>::new();
        funcs.push(foo);
        funcs.push(bar);
        funcs.push(main);
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
			ExpressionList {
				expressions: vec![Expression::Identifier(String::from("i"))]
			}
		));
		let foo = Function {
			id: "foo".to_string(),
			arguments: Vec::<Parameter>::new(),
			statements: foo_statements,
            return_count: 1,
		};

		let mut checker = Checker::new();
		assert_eq!(checker.check_function(&foo), Err(Error { message: "i is undefined".to_string() }));
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
		assert_eq!(checker.check_function(&foo), Ok(()));
	}

	#[test]
	fn arity_mismatch() {
		// def foo():
		//   return 1, 2
		// def bar():
		//   c = foo()
		// should fail
		let bar_statements: Vec<Statement<FieldPrime>> = vec![Statement::MultipleDefinition(
			vec!["c".to_string()],
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

		let mut checker = new_with_args(HashSet::new(), 0, functions);
		assert_eq!(checker.check_function(&bar), Err(Error { message: "foo returns 2 values but left side is of size 1".to_string() }));
	}

	#[test]
	fn multi_return_outside_multidef() {
		// def foo():
		//   return 1, 2
		// def bar():
		//   4 == foo()
		// should fail
		let bar_statements: Vec<Statement<FieldPrime>> = vec![Statement::Condition(
			Expression::Number(FieldPrime::from(2)),
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

		let mut checker = new_with_args(HashSet::new(), 0, functions);
		assert_eq!(checker.check_function(&bar), Err(Error { message: "foo returns 2 values but is called outside of a definition".to_string() }));
	}

	#[test]
	fn function_undefined_in_multidef() {
		// def bar():
		//   c = foo()
		// should fail
		let bar_statements: Vec<Statement<FieldPrime>> = vec![Statement::MultipleDefinition(
			vec!["c".to_string()],
			Expression::FunctionCall("foo".to_string(), vec![])
		)];

		let bar = Function {
			id: "bar".to_string(),
			arguments: vec![],
			statements: bar_statements,
			return_count: 1
		};

		let mut checker = new_with_args(HashSet::new(), 0, HashSet::new());
		assert_eq!(checker.check_function(&bar), Err(Error { message: "Function definition for function foo with 0 argument(s) not found.".to_string() }));
	}

	#[test]
	fn undefined_variable_in_multireturn_call() {
		// def foo(x):
		// 	return 1, 2
		// def main():
		// 	a, b = foo(x)
		// 	return 1
		// should fail

		let foo_statements: Vec<Statement<FieldPrime>> = vec![Statement::Return(
			ExpressionList {
				expressions: vec![
					Expression::Number(FieldPrime::from(1)),
					Expression::Number(FieldPrime::from(2))
				]
			}
		)];

		let foo = Function {
			id: "foo".to_string(),
			arguments: vec![Parameter { id: "x".to_string(), private: false}],
			statements: foo_statements,
			return_count: 2
		};

		let main_statements: Vec<Statement<FieldPrime>> = vec![
			Statement::MultipleDefinition(
				vec!["a".to_string(), "b".to_string()],
				Expression::FunctionCall("foo".to_string(), vec![
					Expression::Identifier("x".to_string())
				])
			),
			Statement::Return(ExpressionList { 
				expressions: vec![
					Expression::Number(FieldPrime::from(1))
				]
			})
		];

		let main = Function {
			id: "main".to_string(),
			arguments: vec![],
			statements: main_statements,
			return_count: 1
		};

		let program = Prog {
			functions: vec![foo, main]
		};

		let mut checker = new_with_args(HashSet::new(), 0, HashSet::new());
		assert_eq!(checker.check_program(program), Err("x is undefined".to_string()));
	}

	#[test]
	fn function_undefined() {
		// def bar():
		//   1 = foo()
		// should fail
		let bar_statements: Vec<Statement<FieldPrime>> = vec![Statement::Condition(
			Expression::Number(FieldPrime::from(1)),
			Expression::FunctionCall("foo".to_string(), vec![])
		)];

		let bar = Function {
			id: "bar".to_string(),
			arguments: vec![],
			statements: bar_statements,
			return_count: 1
		};

		let mut checker = new_with_args(HashSet::new(), 0, HashSet::new());
		assert_eq!(checker.check_function(&bar), Err(Error { message: "Function definition for function foo with 0 argument(s) not found.".to_string() }));
	}

	#[test]
	fn return_undefined() {
		// def bar():
		//   return a, b
		// should fail
		let bar_statements: Vec<Statement<FieldPrime>> = vec![Statement::Return(
			ExpressionList { expressions: vec![
				Expression::Identifier("a".to_string()),
				Expression::Identifier("b".to_string())
			]}
		)];

		let bar = Function {
			id: "bar".to_string(),
			arguments: vec![],
			statements: bar_statements,
			return_count: 2
		};

		let mut checker = new_with_args(HashSet::new(), 0, HashSet::new());
		assert_eq!(checker.check_function(&bar), Err(Error { message: "a is undefined".to_string() }));
	}

	#[test]
	fn multi_def() {
		// def foo():
		//   return 1, 2
		// def bar():
		//   a, b = foo()
		//   return a + b
		//
		// should pass
		let bar_statements: Vec<Statement<FieldPrime>> = vec![
			Statement::MultipleDefinition(
				vec!["a".to_string(), "b".to_string()],
				Expression::FunctionCall("foo".to_string(), vec![])
			),
			Statement::Return(
				ExpressionList { expressions: vec![
					Expression::Add(
						box Expression::Identifier("a".to_string()),
						box Expression::Identifier("b".to_string())
					)]
				}
			)
		];

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

		let mut checker = new_with_args(HashSet::new(), 0, functions);
		assert_eq!(checker.check_function(&bar), Ok(()));
	}

	#[test]
	fn duplicate_function_declaration() {
		// def foo(a, b):
		//   return 1
		// def foo(c, d):
		//   return 2
		//
		// should fail
		let foo2_statements: Vec<Statement<FieldPrime>> = vec![
			Statement::Return(
				ExpressionList {
					expressions: vec![
						Expression::Number(FieldPrime::from(1))
					]
				}
			)
		];

		let foo2_arguments = vec![
			Parameter { id: 'c'.to_string(), private: true },
			Parameter { id: 'd'.to_string(), private: true }
		];

		let foo1 = FunctionDeclaration {
			id: "foo".to_string(),
			arg_count: 2,
            return_count: 1,
		};

		let mut functions = HashSet::new();
		functions.insert(foo1);

		let foo2 = Function {
			id: "foo".to_string(),
			arguments: foo2_arguments,
			statements: foo2_statements,
			return_count: 1
		};

		let mut checker = new_with_args(HashSet::new(), 0, functions);
		assert_eq!(checker.check_function(&foo2), Err(Error { message: "Duplicate definition for function foo with 2 arguments".to_string() }));
	}

	#[test]
	fn duplicate_main_function() {
		// def main(a):
		//   return 1
		// def main():
		//   return 1
		//
		// should fail
		let main1_statements: Vec<Statement<FieldPrime>> = vec![
			Statement::Return(
				ExpressionList {
					expressions: vec![
						Expression::Number(FieldPrime::from(1))
					]
				}
			)
		];

		let main1_arguments = vec![Parameter { id: 'a'.to_string(), private: false }];

		let main2_statements: Vec<Statement<FieldPrime>> = vec![
			Statement::Return(
				ExpressionList {
					expressions: vec![
						Expression::Number(FieldPrime::from(1))
					]
				}
			)
		];

		let main2_arguments = vec![];

		let main1 = Function {
			id: "main".to_string(),
			arguments: main1_arguments,
			statements: main1_statements,
            return_count: 1,
		};

		let main2 = Function {
			id: "main".to_string(),
			arguments: main2_arguments,
			statements: main2_statements,
            return_count: 1,
		};

		let prog = Prog {
			functions: vec![main1, main2]
		};

		let mut checker = Checker::new();
		assert_eq!(checker.check_program(prog), Err(Error { message: "Only one main function allowed, found 2".to_string() }));
	}
}