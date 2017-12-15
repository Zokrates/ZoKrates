//! Module containing semantic analysis tools to run at compile time
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

// Checker, checks the semantics of a program.
pub struct Checker {
	scope: HashSet<Symbol>,
	level: usize
}

impl Checker {
	pub fn new() -> Checker {
		Checker {
			scope: HashSet::new(),
			level: 0
		}
	}

	pub fn new_with_args(scope: HashSet<Symbol>, level: usize) -> Checker {
		Checker {
			scope: scope,
			level: level
		}
	}

	pub fn check_program<T: Field>(&mut self, prog: Prog<T>) -> Result<(), String> {
		for func in prog.functions {
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
			Statement::Definition(id, expr) => {
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
			}
			_ => Ok(()),
		}
	}

	fn check_expression<T: Field>(&mut self, expr: Expression<T>) -> Result<(), String> {
		match expr {
			Expression::Identifier(id) => {
				// check that `id` is defined in the scope
				match self.scope.iter().filter(|symbol| symbol.id == id.to_string()).count() {
					0 => Err(format!("{:?} is undefined", id.to_string())),
					_ => Ok(()),
				}
			}
			Expression::Add(box e1, box e2) | Expression::Sub(box e1, box e2) | Expression::Mult(box e1, box e2) |
			Expression::Div(box e1, box e2) | Expression::Pow(box e1, box e2) => {
				self.check_expression(e1)?;
				self.check_expression(e2)?;
				Ok(())
			}
			Expression::IfElse(box condition, box consequent, box alternative) => {
				self.check_condition(condition)?; 
				self.check_expression(consequent)?;
				self.check_expression(alternative)?;
				Ok(())
			}
			Expression::FunctionCall(_, param_expressions) => {
				for expr in param_expressions {
					self.check_expression(expr)?;
				}
				Ok(())
			}
			Expression::Number(_) => Ok(())
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
		let mut checker = Checker::new_with_args(scope, 1);
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
			statements: foo_statements
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
			String::from("a"),q
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
			statements: foo_statements
		};

		let mut checker = Checker::new();
		assert_eq!(checker.check_function(foo), Ok(()));
	}
}