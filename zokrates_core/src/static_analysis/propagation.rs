//! Module containing constant propagation
//!
//! @file propagation.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use absy::variable::Variable;
use std::collections::HashMap;
use field::Field;
use typed_absy::*;

pub trait Propagate<T: Field> {
	fn propagate(self, functions: &Vec<TypedFunction<T>>) -> Self;
}

pub trait PropagateWithContext<T: Field> {
	fn propagate(self, constants: &mut HashMap<Variable, TypedExpression<T>>, functions: &Vec<TypedFunction<T>>) -> Self;
}

impl<T: Field> PropagateWithContext<T> for TypedExpression<T> {
	fn propagate(self, constants: &mut HashMap<Variable, TypedExpression<T>>, functions: &Vec<TypedFunction<T>>) -> TypedExpression<T> {
		match self {
			TypedExpression::FieldElement(e) => e.propagate(constants, functions).into(),
			TypedExpression::Boolean(e) => e.propagate(constants, functions).into(),
		}
	}
}

impl<T: Field> PropagateWithContext<T> for FieldElementExpression<T> {
	fn propagate(self, constants: &mut HashMap<Variable, TypedExpression<T>>, functions: &Vec<TypedFunction<T>>) -> FieldElementExpression<T> {
		match self {
			FieldElementExpression::Identifier(id) => {
				match constants.get(&Variable::field_element(id.clone())) {
					Some(e) => match e {
						TypedExpression::FieldElement(e) => e.clone(),
						_ => panic!("")
					},
					None => FieldElementExpression::Identifier(id)
				}
			},
			FieldElementExpression::Add(box e1, box e2) => {
				match (e1.propagate(constants, functions), e2.propagate(constants, functions)) {
					(FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => FieldElementExpression::Number(n1 + n2),
					(e1, e2) => FieldElementExpression::Add(box e1, box e2),
				}
			},
			FieldElementExpression::Sub(box e1, box e2) => {
				match (e1.propagate(constants, functions), e2.propagate(constants, functions)) {
					(FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => FieldElementExpression::Number(n1 - n2),
					(e1, e2) => FieldElementExpression::Sub(box e1, box e2),
				}
			},
			FieldElementExpression::Mult(box e1, box e2) => {
				match (e1.propagate(constants, functions), e2.propagate(constants, functions)) {
					(FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => FieldElementExpression::Number(n1 * n2),
					(e1, e2) => FieldElementExpression::Mult(box e1, box e2),
				}
			},
			FieldElementExpression::Div(box e1, box e2) => {
				match (e1.propagate(constants, functions), e2.propagate(constants, functions)) {
					(FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => FieldElementExpression::Number(n1 / n2),
					(e1, e2) => FieldElementExpression::Div(box e1, box e2),
				}
			},
			FieldElementExpression::Pow(box e1, box e2) => {
				match (e1.propagate(constants, functions), e2.propagate(constants, functions)) {
					(FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => FieldElementExpression::Number(n1.pow(n2)),
					(e1, e2) => FieldElementExpression::Pow(box e1, box e2),
				}
			},
			FieldElementExpression::IfElse(box condition, box consequence, box alternative) => {
				let consequence = consequence.propagate(constants, functions);
				let alternative = alternative.propagate(constants, functions);
				match condition.propagate(constants, functions) {
					BooleanExpression::Value(true) => consequence,
					BooleanExpression::Value(false) => alternative,
					c => FieldElementExpression::IfElse(box c, box consequence, box alternative) 
				}
			},
			FieldElementExpression::FunctionCall(id, arguments) => {
				// We only cover the case where all arguments are constants, therefore the call is guaranteed to be constant
				// Propagate the arguments, then return Ok if they're constant, Err otherwise

				let arguments = arguments.into_iter().map(|a| a.propagate(constants, functions)).collect();

				// let f = functions[0]; // TODO find functon based on id
				// match f.execute(arguments) {
				// 	Ok(expressions) => expressions,
				// 	_ => FieldElementExpression::FunctionCall(id, arguments),
				// }

				FieldElementExpression::FunctionCall(id, arguments)

				// let each_argument_constant = arguments.into_iter().map(|a| a.propagate(constants, functions)).map(|a| match a {
				// 	a @ TypedExpression::FieldElement(FieldElementExpression::Number(..)) => Ok(a),
				// 	a @ TypedExpression::Boolean(BooleanExpression::Value(..)) => Ok(a),
				// 	a => Err(a)
				// });

				// let all_arguments_constant = each_argument_constant.collect::<Result<Vec<_>, _>>();

				// match all_arguments_constant {
				// 	Ok(arguments) => {
				// 		// all arguments are constant, we can execute the function now
				// 		unimplemented!()
				// 	},
				// 	Err(_) => {
				// 		// not all arguments are constant, keep the function call
				// 		let arguments = each_argument_constant.into_iter().map(|a| match a {
				// 			Ok(a) => a,
				// 			Err(a) => a
				// 		}).collect();

				// 		
				// 	}
				// }
			}
			_ => self
		}
	}
}

impl<T: Field> PropagateWithContext<T> for BooleanExpression<T> {
	fn propagate(self, constants: &mut HashMap<Variable, TypedExpression<T>>, functions: &Vec<TypedFunction<T>>) -> BooleanExpression<T> {
		match self {
			BooleanExpression::Identifier(id) => {
				match constants.get(&Variable::boolean(id.clone())) {
					Some(e) => match e {
						TypedExpression::Boolean(e) => e.clone(),
						_ => panic!("")
					},
					None => BooleanExpression::Identifier(id)
				}
			},
			BooleanExpression::Eq(box e1, box e2) => {
				let e1 = e1.propagate(constants, functions);
				let e2 = e2.propagate(constants, functions);

				match (e1, e2) {
					(FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
						BooleanExpression::Value(n1 == n2)
					}
					(e1, e2) => BooleanExpression::Eq(box e1, box e2)
				}
			}
			BooleanExpression::Lt(box e1, box e2) => {
				let e1 = e1.propagate(constants, functions);
				let e2 = e2.propagate(constants, functions);

				match (e1, e2) {
					(FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
						BooleanExpression::Value(n1 < n2)
					}
					(e1, e2) => BooleanExpression::Lt(box e1, box e2)
				}
			}
			BooleanExpression::Le(box e1, box e2) => {
				let e1 = e1.propagate(constants, functions);
				let e2 = e2.propagate(constants, functions);

				match (e1, e2) {
					(FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
						BooleanExpression::Value(n1 <= n2)
					}
					(e1, e2) => BooleanExpression::Le(box e1, box e2)
				}
			}
			BooleanExpression::Gt(box e1, box e2) => {
				let e1 = e1.propagate(constants, functions);
				let e2 = e2.propagate(constants, functions);

				match (e1, e2) {
					(FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
						BooleanExpression::Value(n1 > n2)
					}
					(e1, e2) => BooleanExpression::Gt(box e1, box e2)
				}
			}
			BooleanExpression::Ge(box e1, box e2) => {
				let e1 = e1.propagate(constants, functions);
				let e2 = e2.propagate(constants, functions);

				match (e1, e2) {
					(FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
						BooleanExpression::Value(n1 >= n2)
					}
					(e1, e2) => BooleanExpression::Ge(box e1, box e2)
				}
			}
			_ => self
		}
	}
}

impl<T: Field> TypedExpressionList<T> {
	fn propagate(self, constants: &mut HashMap<Variable, TypedExpression<T>>, functions: &Vec<TypedFunction<T>>) -> TypedExpressionList<T> {
		match self {
			TypedExpressionList::FunctionCall(id, arguments, types) => {
				TypedExpressionList::FunctionCall(id, arguments.into_iter().map(|e| e.propagate(constants, functions)).collect(), types)
			}
		}
	}
}

impl<T: Field> TypedStatement<T> {
	fn propagate(self, constants: &mut HashMap<Variable, TypedExpression<T>>, functions: &Vec<TypedFunction<T>>) -> Option<TypedStatement<T>> {
		match self {
			TypedStatement::Return(expressions) => Some(TypedStatement::Return(expressions.into_iter().map(|e| e.propagate(constants, functions)).collect())),
			TypedStatement::Definition(var, expr) => {
				match expr.propagate(constants, functions) {
					e @ TypedExpression::Boolean(BooleanExpression::Value(..)) | e @ TypedExpression::FieldElement(FieldElementExpression::Number(..)) => {
						constants.insert(var, e);
						None
					},
					e => {
						Some(TypedStatement::Definition(var, e))
					}
				}
			},
			TypedStatement::Condition(e1, e2) => {
				// could stop execution here if condition is known to fail...
				Some(TypedStatement::Condition(e1.propagate(constants, functions), e2.propagate(constants, functions)))
			},
			TypedStatement::For(..) => panic!("no for expected"),
			TypedStatement::MultipleDefinition(variables, expression_list) => {
				let expression_list = expression_list.propagate(constants, functions);
				Some(TypedStatement::MultipleDefinition(variables, expression_list))
			}
			_ => Some(self)
		}
	}
}

impl<T: Field> Propagate<T> for TypedFunction<T> {
	fn propagate(self, functions: &Vec<TypedFunction<T>>) -> TypedFunction<T> {

		let mut constants = HashMap::new();

		TypedFunction {
			statements: self.statements.into_iter().filter_map(|s| s.propagate(&mut constants, functions)).collect(),
			..self
		}
	}
}

impl<T: Field> TypedProg<T> {
	pub fn propagate(self) -> TypedProg<T> {

		let mut functions = vec![];

		for f in self.functions {
			let fun = f.propagate(&mut functions);
			functions.push(fun);
		}

		TypedProg {
			functions,
			..self
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use field::FieldPrime;
	
	#[cfg(test)]
	mod expression {
		use super::*;

		#[cfg(test)]
		mod field {
			use super::*;

			#[test]
			fn add() {
				let e = FieldElementExpression::Add(
					box FieldElementExpression::Number(FieldPrime::from(2)),
					box FieldElementExpression::Number(FieldPrime::from(3))
				);

				assert_eq!(e.propagate(&mut HashMap::new(), &mut vec![]), FieldElementExpression::Number(FieldPrime::from(5)));
			}

			#[test]
			fn sub() {
				let e = FieldElementExpression::Sub(
					box FieldElementExpression::Number(FieldPrime::from(3)),
					box FieldElementExpression::Number(FieldPrime::from(2))
				);

				assert_eq!(e.propagate(&mut HashMap::new(), &mut vec![]), FieldElementExpression::Number(FieldPrime::from(1)));
			}

			#[test]
			fn mult() {
				let e = FieldElementExpression::Mult(
					box FieldElementExpression::Number(FieldPrime::from(3)),
					box FieldElementExpression::Number(FieldPrime::from(2))
				);

				assert_eq!(e.propagate(&mut HashMap::new(), &mut vec![]), FieldElementExpression::Number(FieldPrime::from(6)));
			}

			#[test]
			fn div() {
				let e = FieldElementExpression::Div(
					box FieldElementExpression::Number(FieldPrime::from(6)),
					box FieldElementExpression::Number(FieldPrime::from(2))
				);

				assert_eq!(e.propagate(&mut HashMap::new(), &mut vec![]), FieldElementExpression::Number(FieldPrime::from(3)));
			}

			#[test]
			fn pow() {
				let e = FieldElementExpression::Pow(
					box FieldElementExpression::Number(FieldPrime::from(2)),
					box FieldElementExpression::Number(FieldPrime::from(3))
				);

				assert_eq!(e.propagate(&mut HashMap::new(), &mut vec![]), FieldElementExpression::Number(FieldPrime::from(8)));
			}

			#[test]
			fn if_else_true() {
				let e = FieldElementExpression::IfElse(
					box BooleanExpression::Value(true),
					box FieldElementExpression::Number(FieldPrime::from(2)),
					box FieldElementExpression::Number(FieldPrime::from(3))
				);

				assert_eq!(e.propagate(&mut HashMap::new(), &mut vec![]), FieldElementExpression::Number(FieldPrime::from(2)));
			}

			#[test]
			fn if_else_false() {
				let e = FieldElementExpression::IfElse(
					box BooleanExpression::Value(false),
					box FieldElementExpression::Number(FieldPrime::from(2)),
					box FieldElementExpression::Number(FieldPrime::from(3))
				);

				assert_eq!(e.propagate(&mut HashMap::new(), &mut vec![]), FieldElementExpression::Number(FieldPrime::from(3)));
			}
		}

		#[cfg(test)]
		mod boolean {
			use super::*;

			#[test]
			fn eq() {
				let e_true = BooleanExpression::Eq(
					box FieldElementExpression::Number(FieldPrime::from(2)),
					box FieldElementExpression::Number(FieldPrime::from(2))
				);

				let e_false = BooleanExpression::Eq(
					box FieldElementExpression::Number(FieldPrime::from(4)),
					box FieldElementExpression::Number(FieldPrime::from(2))
				);

				assert_eq!(e_true.propagate(&mut HashMap::new(), &mut vec![]), BooleanExpression::Value(true));
				assert_eq!(e_false.propagate(&mut HashMap::new(), &mut vec![]), BooleanExpression::Value(false));
			}

			#[test]
			fn lt() {
				let e_true = BooleanExpression::Lt(
					box FieldElementExpression::Number(FieldPrime::from(2)),
					box FieldElementExpression::Number(FieldPrime::from(4))
				);

				let e_false = BooleanExpression::Lt(
					box FieldElementExpression::Number(FieldPrime::from(4)),
					box FieldElementExpression::Number(FieldPrime::from(2))
				);

				assert_eq!(e_true.propagate(&mut HashMap::new(), &mut vec![]), BooleanExpression::Value(true));
				assert_eq!(e_false.propagate(&mut HashMap::new(), &mut vec![]), BooleanExpression::Value(false));
			}

			#[test]
			fn le() {
				let e_true = BooleanExpression::Le(
					box FieldElementExpression::Number(FieldPrime::from(2)),
					box FieldElementExpression::Number(FieldPrime::from(2))
				);

				let e_false = BooleanExpression::Le(
					box FieldElementExpression::Number(FieldPrime::from(4)),
					box FieldElementExpression::Number(FieldPrime::from(2))
				);

				assert_eq!(e_true.propagate(&mut HashMap::new(), &mut vec![]), BooleanExpression::Value(true));
				assert_eq!(e_false.propagate(&mut HashMap::new(), &mut vec![]), BooleanExpression::Value(false));
			}

			#[test]
			fn gt() {
				let e_true = BooleanExpression::Gt(
					box FieldElementExpression::Number(FieldPrime::from(5)),
					box FieldElementExpression::Number(FieldPrime::from(4))
				);

				let e_false = BooleanExpression::Gt(
					box FieldElementExpression::Number(FieldPrime::from(4)),
					box FieldElementExpression::Number(FieldPrime::from(5))
				);

				assert_eq!(e_true.propagate(&mut HashMap::new(), &mut vec![]), BooleanExpression::Value(true));
				assert_eq!(e_false.propagate(&mut HashMap::new(), &mut vec![]), BooleanExpression::Value(false));
			}

			#[test]
			fn ge() {
				let e_true = BooleanExpression::Ge(
					box FieldElementExpression::Number(FieldPrime::from(5)),
					box FieldElementExpression::Number(FieldPrime::from(5))
				);

				let e_false = BooleanExpression::Ge(
					box FieldElementExpression::Number(FieldPrime::from(4)),
					box FieldElementExpression::Number(FieldPrime::from(5))
				);

				assert_eq!(e_true.propagate(&mut HashMap::new(), &mut vec![]), BooleanExpression::Value(true));
				assert_eq!(e_false.propagate(&mut HashMap::new(), &mut vec![]), BooleanExpression::Value(false));
			}
		}
	}
}