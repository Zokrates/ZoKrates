//! Module containing SSA reduction, including for-loop unrolling
//!
//! @file unroll.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use absy::parameter::Parameter;
use absy::variable::Variable;
use std::collections::HashMap;
use field::Field;
use typed_absy::*;

pub trait Unroll {
	fn unroll(self) -> Self;
}

pub trait UnrollWithContext<T: Field> {
	fn unroll(self, substitution: &mut HashMap<String, usize>) -> Self;
}

impl<T: Field> TypedExpression<T> {
	fn unroll(self, substitution: &HashMap<String, usize>) -> TypedExpression<T> {
		match self {
			TypedExpression::FieldElement(e) => e.unroll(substitution).into(),
			TypedExpression::Boolean(e) => e.unroll(substitution).into(),
		}
	}
}

impl<T: Field> FieldElementExpression<T> {
	fn unroll(self, substitution: &HashMap<String, usize>) -> FieldElementExpression<T> {
		match self {
			FieldElementExpression::Identifier(id) => FieldElementExpression::Identifier(format!("{}_{}", id, substitution.get(&id).unwrap().clone())),
			FieldElementExpression::Number(n) => FieldElementExpression::Number(n),
			FieldElementExpression::Add(box e1, box e2) => FieldElementExpression::Add(box e1.unroll(substitution), box e2.unroll(substitution)),
			FieldElementExpression::Sub(box e1, box e2) => FieldElementExpression::Sub(box e1.unroll(substitution), box e2.unroll(substitution)),
			FieldElementExpression::Mult(box e1, box e2) => FieldElementExpression::Mult(box e1.unroll(substitution), box e2.unroll(substitution)),
			FieldElementExpression::Div(box e1, box e2) => FieldElementExpression::Div(box e1.unroll(substitution), box e2.unroll(substitution)),
			FieldElementExpression::Pow(box e1, box e2) => FieldElementExpression::Div(box e1.unroll(substitution), box e2.unroll(substitution)),
			FieldElementExpression::IfElse(box cond, box cons, box alt) => FieldElementExpression::IfElse(box cond.unroll(substitution), box cons.unroll(substitution), box alt.unroll(substitution)),
			FieldElementExpression::FunctionCall(id, args) => FieldElementExpression::FunctionCall(id, args.into_iter().map(|a| a.unroll(substitution)).collect()),
		}
	}
}

impl<T: Field> BooleanExpression<T> {
	fn unroll(self, substitution: &HashMap<String, usize>) -> BooleanExpression<T> {
		match self {
			BooleanExpression::Identifier(id) => BooleanExpression::Identifier(format!("{}_{}", id, substitution.get(&id).unwrap().clone())),
			BooleanExpression::Value(v) => BooleanExpression::Value(v),
			BooleanExpression::Eq(box e1, box e2) => BooleanExpression::Eq(box e1.unroll(substitution), box e2.unroll(substitution)),
			BooleanExpression::Lt(box e1, box e2) => BooleanExpression::Lt(box e1.unroll(substitution), box e2.unroll(substitution)),
			BooleanExpression::Le(box e1, box e2) => BooleanExpression::Le(box e1.unroll(substitution), box e2.unroll(substitution)),
			BooleanExpression::Gt(box e1, box e2) => BooleanExpression::Gt(box e1.unroll(substitution), box e2.unroll(substitution)),
			BooleanExpression::Ge(box e1, box e2) => BooleanExpression::Ge(box e1.unroll(substitution), box e2.unroll(substitution)),
		}
	}
}

impl<T: Field> TypedExpressionList<T> {
	fn unroll(self, substitution: &HashMap<String, usize>) -> TypedExpressionList<T> {
		match self {
			TypedExpressionList::FunctionCall(id, arguments, types) => {
				TypedExpressionList::FunctionCall(id, arguments.into_iter().map(|a| a.unroll(substitution)).collect(), types)
			}
		}
	}
}


impl<T: Field> TypedStatement<T> {
	fn unroll(self, substitution: &mut HashMap<String, usize>) -> Vec<TypedStatement<T>> {
		match self {
			TypedStatement::Declaration(_) => {
				vec![]
			},
			TypedStatement::Definition(variable, expr) => {
				let expr = expr.unroll(substitution);

				let res = match substitution.get(&variable.id) {
					Some(i) => {
						vec![TypedStatement::Definition(Variable { id: format!("{}_{}", variable.id, i + 1), ..variable}, expr)]
					},
					None => {
						vec![TypedStatement::Definition(Variable { id: format!("{}_{}", variable.id, 0), ..variable}, expr)]
					}
				};
				substitution.entry(variable.id)
				   .and_modify(|e| { *e += 1 })
				   .or_insert(0);
				res
			},
			TypedStatement::MultipleDefinition(variables, exprs) => {
				let exprs = exprs.unroll(substitution);
				let variables = variables.into_iter().map(|v| {
					let res = match substitution.get(&v.id) {
						Some(i) => {
							Variable { id: format!("{}_{}", v.id, i + 1), ..v}
						},
						None => {
							Variable { id: format!("{}_{}", v.id, 0), ..v}
						}
					};
					substitution.entry(v.id)
					   .and_modify(|e| { *e += 1 })
					   .or_insert(0);
					 res
				}).collect();

				vec![TypedStatement::MultipleDefinition(variables, exprs)]
			},
			TypedStatement::Condition(e1, e2) => vec![TypedStatement::Condition(e1.unroll(substitution), e2.unroll(substitution))],
			TypedStatement::For(v, from, to, stats) => {
				let mut values: Vec<T> = vec![];
				let mut current = from;
                while current < to {
                	values.push(current.clone());
                    current = T::one() + &current;
                }

				let res = values.into_iter().map(|index| {
					vec![
						vec![
							TypedStatement::Declaration(v.clone()),
							TypedStatement::Definition(v.clone(), FieldElementExpression::Number(index).into()),
						],
						stats.clone()
					].into_iter().flat_map(|x| x)
				}).flat_map(|x| x).flat_map(|x| x.unroll(substitution)).collect();

				res
			}
			TypedStatement::Return(exprs) => {
				vec![TypedStatement::Return(exprs.into_iter().map(|e| e.unroll(substitution)).collect())]
			}
		}
	}
}

impl<T: Field> Unroll for TypedFunction<T> {
	fn unroll(self) -> TypedFunction<T> {

		let mut substitution = HashMap::new();

		let arguments = self.arguments.into_iter().map(|p|
			Parameter {
				id: Variable {
					id: format!("{}_{}", p.id.id.clone(), substitution.entry(p.id.id)
			   			.and_modify(|e| { *e += 1 })
			   			.or_insert(0)),
			   		..p.id
			   	},
			   ..p
			}
		).collect();

		TypedFunction {
			arguments: arguments,
			statements: self.statements.into_iter().flat_map(|s| s.unroll(&mut substitution)).collect(),
			..self
		}
	}
}

impl<T: Field> Unroll for TypedProg<T> {
	fn unroll(self) -> TypedProg<T> {
		TypedProg {
			functions: self.functions.into_iter().map(|f| f.unroll()).collect(),
			..self
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use field::FieldPrime;

	#[cfg(test)]
	mod statement {
		use super::*;

		#[test]
		fn for_loop() {
			let s = TypedStatement::For(Variable::field_element("i"), FieldPrime::from(2), FieldPrime::from(5), vec![
						TypedStatement::Declaration(Variable::field_element("foo")),
						TypedStatement::Definition(Variable::field_element("foo"), FieldElementExpression::Identifier(String::from("i")).into())]
					);

			let expected =  vec![
					TypedStatement::Definition(Variable::field_element("i_0"), FieldElementExpression::Number(FieldPrime::from(2)).into()),
					TypedStatement::Definition(Variable::field_element("foo_0"), FieldElementExpression::Identifier(String::from("i_0")).into()),

					TypedStatement::Definition(Variable::field_element("i_1"), FieldElementExpression::Number(FieldPrime::from(3)).into()),
					TypedStatement::Definition(Variable::field_element("foo_1"), FieldElementExpression::Identifier(String::from("i_1")).into()),

					TypedStatement::Definition(Variable::field_element("i_2"), FieldElementExpression::Number(FieldPrime::from(4)).into()),
					TypedStatement::Definition(Variable::field_element("foo_2"), FieldElementExpression::Identifier(String::from("i_2")).into()),
				];

			assert_eq!(s.unroll(&mut HashMap::new()), expected);
		}

		#[test]
		fn definition() {

			// field a
			// a = 5
			// a = 6
			// a

			// should be turned into
			// a_0 = 5
			// a_1 = 6
			// a_1

			let mut substitution = HashMap::new();

			let s: TypedStatement<FieldPrime> = TypedStatement::Declaration(Variable::field_element("a"));
			assert_eq!(s.unroll(&mut substitution), vec![]);

			let s = TypedStatement::Definition(Variable::field_element("a"), FieldElementExpression::Number(FieldPrime::from(5)).into());
			assert_eq!(s.unroll(&mut substitution), vec![TypedStatement::Definition(Variable::field_element("a_0"), FieldElementExpression::Number(FieldPrime::from(5)).into())]);
			
			let s = TypedStatement::Definition(Variable::field_element("a"), FieldElementExpression::Number(FieldPrime::from(6)).into());
			assert_eq!(s.unroll(&mut substitution), vec![TypedStatement::Definition(Variable::field_element("a_1"), FieldElementExpression::Number(FieldPrime::from(6)).into())]);
			
			let e: FieldElementExpression<FieldPrime> = FieldElementExpression::Identifier(String::from("a"));
			assert_eq!(e.unroll(&mut substitution), FieldElementExpression::Identifier(String::from("a_1")));
		}

		#[test]
		fn incremental_definition() {

			// field a
			// a = 5
			// a = a + 1

			// should be turned into
			// a_0 = 5
			// a_1 = a_0 + 1

			let mut substitution = HashMap::new();

			let s: TypedStatement<FieldPrime> = TypedStatement::Declaration(Variable::field_element("a"));
			assert_eq!(s.unroll(&mut substitution), vec![]);

			let s = TypedStatement::Definition(Variable::field_element("a"), FieldElementExpression::Number(FieldPrime::from(5)).into());
			assert_eq!(s.unroll(&mut substitution), vec![TypedStatement::Definition(Variable::field_element("a_0"), FieldElementExpression::Number(FieldPrime::from(5)).into())]);
			
			let s = TypedStatement::Definition(
				Variable::field_element("a"),
				FieldElementExpression::Add(
					box FieldElementExpression::Identifier(String::from("a")),
					box FieldElementExpression::Number(FieldPrime::from(1))
				).into()
			);
			assert_eq!(
				s.unroll(&mut substitution),
				vec![
					TypedStatement::Definition(
						Variable::field_element("a_1"),
						FieldElementExpression::Add(
							box FieldElementExpression::Identifier(String::from("a_0")),
							box FieldElementExpression::Number(FieldPrime::from(1))
						).into()
					)
				]
			);
		}

		#[test]
		fn incremental_multiple_definition() {

			use types::Type;

			// field a
			// a = 2
			// a = foo(a)

			// should be turned into
			// a_0 = 2
			// a_1 = foo(a_0)

			let mut substitution = HashMap::new();

			let s: TypedStatement<FieldPrime> = TypedStatement::Declaration(Variable::field_element("a"));
			assert_eq!(s.unroll(&mut substitution), vec![]);

			let s = TypedStatement::Definition(Variable::field_element("a"), FieldElementExpression::Number(FieldPrime::from(2)).into());
			assert_eq!(s.unroll(&mut substitution), vec![TypedStatement::Definition(Variable::field_element("a_0"), FieldElementExpression::Number(FieldPrime::from(2)).into())]);
			
			let s: TypedStatement<FieldPrime> = TypedStatement::MultipleDefinition(
				vec![Variable::field_element("a")],
				TypedExpressionList::FunctionCall(
					String::from("foo"),
					vec![FieldElementExpression::Identifier(String::from("a")).into()],
					vec![Type::FieldElement],
				)
			);
			assert_eq!(
				s.unroll(&mut substitution),
				vec![
					TypedStatement::MultipleDefinition(
						vec![Variable::field_element("a_1")],
						TypedExpressionList::FunctionCall(
							String::from("foo"),
							vec![FieldElementExpression::Identifier(String::from("a_0")).into()],
							vec![Type::FieldElement],
						)
					)
				]
			);
		}
	}
}