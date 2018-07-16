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
use absy::signature::Signature;
use absy::variable::Variable;

use types::Type;

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
pub struct ScopedVariable {
	id: Variable,
	level: usize
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct FunctionDeclaration {
	id: String,
	signature: Signature
}

// Checker, checks the semantics of a program.
pub struct Checker {
	scope: HashSet<ScopedVariable>,
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

	pub fn check_program<T: Field>(&mut self, prog: Prog<T>) -> Result<Prog<T>, Error> {
		for func in &prog.imported_functions {
			self.functions.insert(FunctionDeclaration {
				id: func.id.clone(),
				signature: Signature { // a bit hacky
					inputs: vec![Type::FieldElement; func.arguments.len()],
					outputs: vec![Type::FieldElement; func.return_count]
				}
			});
		}

		let mut checked_functions = vec![];

		for func in prog.functions {
			let checked_func = self.check_function(&func)?;
			checked_functions.push(checked_func);
			self.functions.insert(FunctionDeclaration {
				id: func.id,
				signature: func.signature
			});
		}
		self.check_single_main()?;
		Ok(Prog {
			functions: checked_functions,
			imported_functions: prog.imported_functions,
			imports: prog.imports
		})
	}

	fn check_single_main(&mut self) -> Result<(), Error> {
		match self.functions.clone().into_iter().filter(|fun| fun.id == "main").count() {
			1 => Ok(()),
			0 => Err(Error { message: format!("No main function found") }),
			n => Err(Error { message: format!("Only one main function allowed, found {}", n) })
		}
	}

	fn check_function<T: Field>(&mut self, funct: &Function<T>) -> Result<Function<T>, Error> {
		assert_eq!(funct.arguments.len(), funct.signature.inputs.len());

		match self.find_function(&funct.id, &funct.arguments.iter().map(|a| a.clone().id._type).collect()) {
			Some(_) => {
				return Err(Error { message: format!("Duplicate definition for function {} with {} arguments", funct.id, funct.arguments.len()) })
			},
			None => {

			}
		}
		self.level += 1;

		for arg in funct.arguments.clone() {
			self.scope.insert(ScopedVariable {
				id: arg.id,
				level: self.level
			});
		}

		let mut statements_checked = vec![];

		for stat in funct.statements.clone() {
			let checked_stat = self.check_statement(stat)?;
			statements_checked.push(checked_stat);
		}

		let current_level = self.level.clone();
		let current_scope = self.scope.clone();
		let to_remove = current_scope.iter().filter(|symbol| symbol.level == current_level);
		for symbol in to_remove {
			self.scope.remove(symbol);
		}
		self.level -= 1;
		Ok(Function {
			id: funct.id.clone(),
			arguments: funct.arguments.clone(),
			statements: statements_checked,
			signature: funct.signature.clone(),
		})
	}

	fn check_statement<T: Field>(&mut self, stat: Statement<T>) -> Result<Statement<T>, Error> {
		match stat {
			Statement::Return(ref list) => {
				let expression_list_checked = self.check_expression_list(list)?;
				Ok(Statement::Return(expression_list_checked))
			}
			Statement::Definition(var, expr) => {
				let checked_expr = self.check_expression(expr)?;

				match checked_expr {
					Expression::Annotated(_, ref t) => {
						assert_eq!(t.len(), 1);
						if t[0] != var._type {
							return Err( Error { message: format!("cannot assign {:?} to {:?}", t[0], var._type) });
						}
					},
					_ => panic!("should be annotated")
				}

				self.scope.insert(ScopedVariable {
					id: var.clone(),
					level: self.level
				});
				Ok(Statement::Definition(var, checked_expr))
			}
			Statement::Condition(lhs, rhs) => {
				let checked_lhs = self.check_expression(lhs)?;
				let checked_rhs = self.check_expression(rhs)?;

				match (checked_lhs.clone(), checked_rhs.clone()) {
					(Expression::Annotated(_, ref t1), Expression::Annotated(_, ref t2)) => {
						assert_eq!(t1.len(), 1);
						assert_eq!(t2.len(), 1);
						if t1 != t2 {
							return Err( Error { message: format!("cannot compare {:?} to {:?}", t1[0], t2[0]) });
						}
					},
					_ => panic!("should be annotated")
				}

				Ok(Statement::Condition(checked_lhs, checked_rhs))

			}
			Statement::For(var, from, to, statements) => {
				self.level += 1;
				let index = ScopedVariable {
					id: var.clone(),
					level: self.level
				};
				self.scope.insert(index.clone());

				let mut checked_statements = vec![];

				for stat in statements {
					let checked_stat = self.check_statement(stat)?;
					checked_statements.push(checked_stat);
				}
				self.scope.remove(&index);
				self.level -= 1;
				Ok(Statement::For(var, from, to, checked_statements))
			},
            Statement::MultipleDefinition(vars, rhs) => {
            	let vars_types: Vec<Type> = vars.iter().map(|var| var.clone()._type).collect();

        		// All elements of the left side have to be identifiers
                match rhs {
                	// Right side has to be a function call
                    Expression::FunctionCall(ref fun_id, ref arguments) => {
                    	// check the arguments
                    	let mut arguments_checked = vec![]; 
                    	for arg in arguments {
                    		let arg_checked = self.check_expression(arg.clone())?;
                    		arguments_checked.push(arg_checked);
                    	}

                    	let arguments_types = arguments_checked.iter().map(|arg| {
                    		match arg {
                    			Expression::Annotated(_, ref t) => {
                    				t[0].clone()
                    			},
                    			_ => panic!("should be annotated")
                    		}
                    	}).collect();

                    	match self.find_function(fun_id, &arguments_types) {
                    		// the function has to be defined
                    		Some(f) => {
                    			// the return count has to match the left side
                    			if f.signature.outputs == vars_types {
                    				for var in &vars {
                        				self.scope.insert(ScopedVariable {
											id: var.clone(),
											level: self.level
										});
                    				}
                    				return Ok(Statement::MultipleDefinition(vars, Expression::FunctionCall(f.id, arguments_checked).with_annotations(f.signature.outputs)))
                    			}
                    			Err(Error { message: format!("{} returns {} values but left side is of size {}", f.id, f.signature.outputs.len(), vars.len()) })
                    		},
                    		None => Err(Error { message: format!("Function definition for function {} with {} argument(s) not found.", fun_id, arguments.len()) })
                    	}
                    },
                    _ => Err(Error { message: format!("{} should be a FunctionCall", rhs) })
                }
            },
		}
	}

	fn check_expression<T: Field>(&mut self, expr: Expression<T>) -> Result<Expression<T>, Error> {
		match expr {
			Expression::Identifier(variable) => {
				// check that `id` is defined in the scope
				match self.scope.iter().find(|v| v.id.id == variable) {
					Some(v) => Ok(Expression::Identifier(variable).with_annotation(v.clone().id._type)),
					None => Err(Error { message: format!("{} is undefined", variable.to_string()) }),
				}
			},
			Expression::Add(box e1, box e2) => {
				let e1_checked = self.check_expression(e1)?;
				let e2_checked = self.check_expression(e2)?;

				match (e1_checked.clone(), e2_checked.clone()) {
					(Expression::Annotated(_, ref t1), Expression::Annotated(_, ref t2)) => {
						assert_eq!(t1.len(), 1);
						assert_eq!(t2.len(), 1);
						match (t1[0].clone(), t2[0].clone()) {
							(Type::FieldElement, Type::FieldElement) => {
								Ok(Expression::Add(box e1_checked, box e2_checked).with_annotation(Type::FieldElement))
							}
							(t1, t2) => Err(Error { message: format!("Expected only field elements, found {}, {}", t1, t2) })
						}
					},
					_ => panic!("should be annotated")
				}
			},
			Expression::Sub(box e1, box e2) => {
				let e1_checked = self.check_expression(e1)?;
				let e2_checked = self.check_expression(e2)?;

				match (e1_checked.clone(), e2_checked.clone()) {
					(Expression::Annotated(_, t1), Expression::Annotated(_, t2)) => {
						assert_eq!(t1.len(), 1);
						assert_eq!(t2.len(), 1);
						match (t1[0].clone(), t2[0].clone()) {
							(Type::FieldElement, Type::FieldElement) => {
								Ok(Expression::Sub(box e1_checked, box e2_checked).with_annotation(Type::FieldElement))
							}
							(t1, t2) => Err(Error { message: format!("Expected only field elements, found {}, {}", t1, t2) })
						}
					},
					_ => panic!("should be annotated")
				}
			},
			Expression::Mult(box e1, box e2) => {
				let e1_checked = self.check_expression(e1)?;
				let e2_checked = self.check_expression(e2)?;

				match (e1_checked.clone(), e2_checked.clone()) {
					(Expression::Annotated(_, t1), Expression::Annotated(_, t2)) => {
						assert_eq!(t1.len(), 1);
						assert_eq!(t2.len(), 1);
						match (t1[0].clone(), t2[0].clone()) {							
						(Type::FieldElement, Type::FieldElement) => {
								Ok(Expression::Mult(box e1_checked, box e2_checked).with_annotation(Type::FieldElement))
							}
							(t1, t2) => Err(Error { message: format!("Expected only field elements, found {}, {}", t1, t2) })
						}
					},
					_ => panic!("should be annotated")
				}
			},
			Expression::Div(box e1, box e2) => {
				let e1_checked = self.check_expression(e1)?;
				let e2_checked = self.check_expression(e2)?;

				match (e1_checked.clone(), e2_checked.clone()) {
					(Expression::Annotated(_, t1), Expression::Annotated(_, t2)) => {
						assert_eq!(t1.len(), 1);
						assert_eq!(t2.len(), 1);
						match (t1[0].clone(), t2[0].clone()) {							
							(Type::FieldElement, Type::FieldElement) => {
								Ok(Expression::Div(box e1_checked, box e2_checked).with_annotation(Type::FieldElement))
							}
							(t1, t2) => Err(Error { message: format!("Expected only field elements, found {:?}, {:?}", t1, t2) })
						}
					},
					_ => panic!("should be annotated")
				}
			},
			Expression::Pow(box e1, box e2) => {
				let e1_checked = self.check_expression(e1)?;
				let e2_checked = self.check_expression(e2)?;

				match (e1_checked.clone(), e2_checked.clone()) {
					(Expression::Annotated(_, t1), Expression::Annotated(_, t2)) => {
						assert_eq!(t1.len(), 1);
						assert_eq!(t2.len(), 1);
						match (t1[0].clone(), t2[0].clone()) {							
							(Type::FieldElement, Type::FieldElement) => {
								Ok(Expression::Pow(box e1_checked, box e2_checked).with_annotation(Type::FieldElement))
							}
							(t1, t2) => Err(Error { message: format!("Expected only field elements, found {:?}, {:?}", t1, t2) })
						}
					},
					_ => panic!("should be annotated")
				}
			},
			Expression::IfElse(box condition, box consequence, box alternative) => {
				self.check_condition(&condition)?;
				let consequence_checked = self.check_expression(consequence)?;
				let alternative_checked = self.check_expression(alternative)?;
				
				match (consequence_checked.clone(), alternative_checked.clone()) {
					(Expression::Annotated(_, t1), Expression::Annotated(_, t2)) => {
						assert_eq!(t1.len(), 1);
						assert_eq!(t2.len(), 1);
						if t1 != t2 {
							return Err(Error { message: format!("") });
						}

						Ok(Expression::IfElse(box condition, box consequence_checked, box alternative_checked).with_annotations(t1))
					},
					_ => panic!("should be annotated")
				}
			}
			Expression::FunctionCall(ref fun_id, ref arguments) => {
            	// check the arguments
            	let mut arguments_checked = vec![];

            	for arg in arguments {
            		let arg_checked = self.check_expression(arg.clone())?;
            		arguments_checked.push(arg_checked);
            	}

            	let arguments_types = arguments_checked.iter().map(|arg| {
            		match arg.clone() {
            			Expression::Annotated(_, ref t) => {
            				t[0].clone()
            			},
            			_ => panic!("should be annotated")
            		}
            	}).collect();

				match self.find_function(fun_id, &arguments_types) {
					// the function has to be defined
					Some(f) => {
						if f.signature.outputs.len() != 1 { // Functions must return a single value when not in a MultipleDefinition
							return Err(Error { message: format!("{} returns {} values but is called outside of a definition", fun_id, f.signature.outputs.len()) })
						}
						let return_types = f.signature.outputs.clone();
						Ok(Expression::FunctionCall(f.id, arguments_checked).with_annotations(return_types))
					},
                   	None => Err(Error { message: format!("Function definition for function {} with arguments {:?} not found.", fun_id, arguments_types) })
				}
			}
			Expression::Number(n) => Ok(Expression::Number(n).with_annotation(Type::FieldElement)),
			Expression::Annotated(_, _) => panic!("This node should not be annotated yet")
		}
	}

	fn check_expression_list<T: Field>(&mut self, list: &ExpressionList<T>) -> Result<ExpressionList<T>, Error> {
		let mut expressions_checked = vec![];

		for expr in list.expressions.clone() { // implement Iterator trait?
			let expr_checked = self.check_expression(expr)?;
			expressions_checked.push(expr_checked);
		}
		Ok(ExpressionList {
			expressions: expressions_checked
		})
	}

	fn check_condition<T: Field>(&mut self, cond: &Condition<T>) -> Result<(), Error> {
		match cond.clone() {
			Condition::Lt(e1, e2) |
			Condition::Le(e1, e2) |
			Condition::Eq(e1, e2) |
			Condition::Ge(e1, e2) |
			Condition::Gt(e1, e2) => {
				let e1_checked = self.check_expression(e1)?;
				let e2_checked = self.check_expression(e2)?;
				match (e1_checked.clone(), e2_checked.clone()) {
					(Expression::Annotated(_, t1), Expression::Annotated(_, t2)) => {
						assert_eq!(t1.len(), 1);
						assert_eq!(t2.len(), 1);
						match (t1[0].clone(), t2[0].clone()) {
							(Type::FieldElement, Type::FieldElement) => {
								Ok(())
							},
							_ => Err(Error { message: format!("cannot compare {} to {}", t1[0], t2[0]) })
						}
					},
					_ => panic!("should be annotated")
				}
			}
		}
	}

	fn find_function(&mut self, id: &str, arg_types: &Vec<Type>) -> Option<FunctionDeclaration> {
		self.functions.clone().into_iter().find(|fun| {
			fun.id == id && fun.signature.inputs.len() == arg_types.len()
		})
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use field::FieldPrime;
	use absy::parameter::Parameter;

	pub fn new_with_args(scope: HashSet<ScopedVariable>, level: usize, functions: HashSet<FunctionDeclaration>) -> Checker {
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
			Variable::from("a"),
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
			Variable::from("a"),
			Expression::Identifier(String::from("b"))
		);
		let mut scope = HashSet::new();
		scope.insert(ScopedVariable {
			id: Variable::from("b"),
			level: 0
		});
		let mut checker = new_with_args(scope, 1, HashSet::new());
		assert_eq!(checker.check_statement(statement), 
			Ok(
				Statement::Definition(
					Variable::from("a"),
					Expression::Identifier(String::from("b")).with_annotation(Type::FieldElement)
				)
			)
		);
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
			Variable::from("a"),
			Expression::Number(FieldPrime::from(1)))
		);
		let foo = Function {
            id: "foo".to_string(),
            arguments: foo_args,
            statements: foo_statements,
            signature: Signature {
            	inputs: vec![],
            	outputs: vec![Type::FieldElement]
            }
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
            signature: Signature {
            	inputs: vec![],
            	outputs: vec![Type::FieldElement]
            }
        };

        let mut funcs = Vec::<Function<FieldPrime>>::new();
        funcs.push(foo);
        funcs.push(bar);
        let prog = Prog {
			functions: funcs,
			imports: vec![],
			imported_functions: vec![]
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
			Variable::from("a"),
			Expression::Number(FieldPrime::from(1)))
		);
		let foo = Function {
            id: "foo".to_string(),
            arguments: foo_args,
            statements: foo_statements,
            signature: Signature {
            	inputs: vec![],
            	outputs: vec![Type::FieldElement]
            }
        };

        let bar_args = Vec::<Parameter>::new();
		let mut bar_statements = Vec::<Statement<FieldPrime>>::new();
		bar_statements.push(Statement::Definition(
			Variable::from("a"),
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
            signature: Signature {
            	inputs: vec![],
            	outputs: vec![Type::FieldElement]
            }
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
            signature: Signature {
            	inputs: vec![],
            	outputs: vec![Type::FieldElement]
            }
        };

        let mut funcs = Vec::<Function<FieldPrime>>::new();
        funcs.push(foo);
        funcs.push(bar);
        funcs.push(main);
        let prog = Prog {
			functions: funcs,
			imports: vec![],
			imported_functions: vec![]
        };

		let mut checker = Checker::new();
		//assert_eq!(checker.check_program(prog), Ok(()));
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
			Variable::from("i"),
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
            signature: Signature {
            	inputs: vec![],
            	outputs: vec![Type::FieldElement]
            }
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
			Variable::from("a"),
			Expression::Identifier(String::from("i"))
		));
		foo_statements.push(Statement::For(
			Variable::from("i"),
			FieldPrime::from(0),
			FieldPrime::from(10),
			for_statements
		));

		let mut foo_statements_checked = Vec::<Statement<FieldPrime>>::new();
		let mut for_statements_checked = Vec::<Statement<FieldPrime>>::new();
		for_statements_checked.push(Statement::Definition(
			Variable::from("a"),
			Expression::Identifier(String::from("i")).with_annotation(Type::FieldElement)
		));
		foo_statements_checked.push(Statement::For(
			Variable::from("i"),
			FieldPrime::from(0),
			FieldPrime::from(10),
			for_statements_checked
		));


		let foo = Function {
			id: "foo".to_string(),
			arguments: Vec::<Parameter>::new(),
			statements: foo_statements,
            signature: Signature {
            	inputs: vec![],
            	outputs: vec![Type::FieldElement]
            }
		};

		let foo_checked = Function {
			id: "foo".to_string(),
			arguments: Vec::<Parameter>::new(),
			statements: foo_statements_checked,
            signature: Signature {
            	inputs: vec![],
            	outputs: vec![Type::FieldElement]
            }
		};

		let mut checker = Checker::new();
		assert_eq!(checker.check_function(&foo), Ok(foo_checked));
	}

	#[test]
	fn arity_mismatch() {
		// def foo():
		//   return 1, 2
		// def bar():
		//   c = foo()
		// should fail
		let bar_statements: Vec<Statement<FieldPrime>> = vec![Statement::MultipleDefinition(
			vec![Variable::from("a")],
			Expression::FunctionCall("foo".to_string(), vec![])
		)];

		let foo = FunctionDeclaration {
			id: "foo".to_string(),
            signature: Signature {
            	inputs: vec![],
            	outputs: vec![Type::FieldElement, Type::FieldElement]
            }
		};

		let mut functions = HashSet::new();
		functions.insert(foo);

		let bar = Function {
			id: "bar".to_string(),
			arguments: vec![],
			statements: bar_statements,
            signature: Signature {
            	inputs: vec![],
            	outputs: vec![Type::FieldElement]
            }		
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
			signature: Signature {
				inputs: vec![],
				outputs: vec![Type::FieldElement, Type::FieldElement]
			}
		};

		let mut functions = HashSet::new();
		functions.insert(foo);

		let bar = Function {
			id: "bar".to_string(),
			arguments: vec![],
			statements: bar_statements,
			signature: Signature {
				inputs: vec![],
				outputs: vec![Type::FieldElement]
			}
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
			vec![Variable::from("a")],
			Expression::FunctionCall("foo".to_string(), vec![])
		)];

		let bar = Function {
			id: "bar".to_string(),
			arguments: vec![],
			statements: bar_statements,
			signature: Signature {
				inputs: vec![],
				outputs: vec![Type::FieldElement]
			}
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
			arguments: vec![Parameter { id: Variable::from("x"), private: false}],
			statements: foo_statements,
			signature: Signature {
				inputs: vec![Type::FieldElement],
				outputs: vec![Type::FieldElement, Type::FieldElement]
			}
		};

		let main_statements: Vec<Statement<FieldPrime>> = vec![
			Statement::MultipleDefinition(
				vec![Variable::from("a"), Variable::from("b")],
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
			signature: Signature {
				inputs: vec![],
				outputs: vec![Type::FieldElement, Type::FieldElement]
			}
		};

		let program = Prog {
			functions: vec![foo, main],
			imports: vec![],
			imported_functions: vec![]
		};

		let mut checker = new_with_args(HashSet::new(), 0, HashSet::new());
		assert_eq!(checker.check_program(program), Err(Error { message: "x is undefined".to_string() }));
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
			signature: Signature {
				inputs: vec![],
				outputs: vec![Type::FieldElement]
			}
		};

		let mut checker = new_with_args(HashSet::new(), 0, HashSet::new());
		assert_eq!(checker.check_function(&bar), Err(Error { message: "Function definition for function foo with arguments [] not found.".to_string() }));
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
			signature: Signature {
				inputs: vec![],
				outputs: vec![Type::FieldElement, Type::FieldElement]
			}
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
				vec![Variable::from("a"), Variable::from("b")],
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

		let bar_statements_checked: Vec<Statement<FieldPrime>> = vec![
			Statement::MultipleDefinition(
				vec![Variable::from("a"), Variable::from("b")],
				Expression::FunctionCall("foo".to_string(), vec![]).with_annotations(vec![Type::FieldElement, Type::FieldElement])
			),
			Statement::Return(
				ExpressionList { expressions: vec![
					Expression::Add(
						box Expression::Identifier("a".to_string()).with_annotation(Type::FieldElement),
						box Expression::Identifier("b".to_string()).with_annotation(Type::FieldElement)
					).with_annotation(Type::FieldElement)]
				}
			)
		];

		let foo = FunctionDeclaration {
			id: "foo".to_string(),
			signature: Signature {
				inputs: vec![],
				outputs: vec![Type::FieldElement, Type::FieldElement]
			}
		};

		let mut functions = HashSet::new();
		functions.insert(foo);

		let bar = Function {
			id: "bar".to_string(),
			arguments: vec![],
			statements: bar_statements,
			signature: Signature {
				inputs: vec![],
				outputs: vec![Type::FieldElement]
			}
		};

		let bar_checked = Function {
			id: "bar".to_string(),
			arguments: vec![],
			statements: bar_statements_checked,
			signature: Signature {
				inputs: vec![],
				outputs: vec![Type::FieldElement]
			}
		};

		let mut checker = new_with_args(HashSet::new(), 0, functions);
		assert_eq!(checker.check_function(&bar), Ok(bar_checked));
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
			Parameter { id: Variable::from("a"), private: true },
			Parameter { id: Variable::from("b"), private: true }
		];

		let foo1 = FunctionDeclaration {
			id: "foo".to_string(),
			signature: Signature {
            	inputs: vec![Type::FieldElement, Type::FieldElement],
            	outputs: vec![Type::FieldElement]
            }
		};

		let mut functions = HashSet::new();
		functions.insert(foo1);

		let foo2 = Function {
			id: "foo".to_string(),
			arguments: foo2_arguments,
			statements: foo2_statements,
			signature: Signature {
            	inputs: vec![Type::FieldElement, Type::FieldElement],
            	outputs: vec![Type::FieldElement]
            }
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

		let main1_arguments = vec![Parameter { id: Variable::from("a"), private: false }];

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
			signature: Signature {
            	inputs: vec![Type::FieldElement],
            	outputs: vec![Type::FieldElement]
            }
		};

		let main2 = Function {
			id: "main".to_string(),
			arguments: main2_arguments,
			statements: main2_statements,
			signature: Signature {
            	inputs: vec![],
            	outputs: vec![Type::FieldElement]
            }
		};

		let prog = Prog {
			functions: vec![main1, main2],
			imports: vec![],
			imported_functions: vec![]
		};

		let mut checker = Checker::new();
		assert_eq!(checker.check_program(prog), Err(Error { message: "Only one main function allowed, found 2".to_string() }));
	}
}