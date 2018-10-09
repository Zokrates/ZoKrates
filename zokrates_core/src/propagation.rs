use field::Field;
use typed_absy::*;

pub trait Propagate {
	fn propagate(self) -> Self;
}

impl<T: Field> Propagate for TypedExpression<T> {
	fn propagate(self) -> TypedExpression<T> {
		match self {
			TypedExpression::FieldElement(e) => e.propagate().into(),
			TypedExpression::Boolean(e) => e.propagate().into(),
		}
	}
}

impl<T: Field> Propagate for FieldElementExpression<T> {
	fn propagate(self) -> FieldElementExpression<T> {
		println!("{:?}", self);
		match self {
			FieldElementExpression::Add(box FieldElementExpression::Number(n1), box FieldElementExpression::Number(n2)) => {
				FieldElementExpression::Number(n1 + n2)
			},
			FieldElementExpression::Sub(box FieldElementExpression::Number(n1), box FieldElementExpression::Number(n2)) => {
				FieldElementExpression::Number(n1 - n2)
			},
			FieldElementExpression::Mult(box FieldElementExpression::Number(n1), box FieldElementExpression::Number(n2)) => {
				FieldElementExpression::Number(n1 * n2)
			},
			FieldElementExpression::Div(box FieldElementExpression::Number(n1), box FieldElementExpression::Number(n2)) => {
				FieldElementExpression::Number(n1.div(n2))
			},
			FieldElementExpression::Pow(box FieldElementExpression::Number(n1), box FieldElementExpression::Number(n2)) => {
				FieldElementExpression::Number(n1.pow(n2))
			},
			FieldElementExpression::IfElse(box BooleanExpression::Value(true), box cons, _) => cons,
			FieldElementExpression::IfElse(box BooleanExpression::Value(false), _, box alt) => alt,
			FieldElementExpression::Add(box e1, box e2) => FieldElementExpression::Add(box e1.propagate(), box e2.propagate()).propagate(),
			FieldElementExpression::Sub(box e1, box e2) => FieldElementExpression::Sub(box e1.propagate(), box e2.propagate()).propagate(),
			FieldElementExpression::Mult(box e1, box e2) => FieldElementExpression::Mult(box e1.propagate(), box e2.propagate()).propagate(),
			FieldElementExpression::Div(box e1, box e2) => FieldElementExpression::Div(box e1.propagate(), box e2.propagate()).propagate(),
			FieldElementExpression::Pow(box e1, box e2) => FieldElementExpression::Pow(box e1.propagate(), box e2.propagate()).propagate(),
			FieldElementExpression::IfElse(box condition, box cons, box alt) => FieldElementExpression::IfElse(box condition.propagate(), box cons.propagate(), box alt.propagate()).propagate(),
			_ => self
		}
	}
}

impl<T: Field> Propagate for BooleanExpression<T> {
	fn propagate(self) -> BooleanExpression<T> {
		match self {
			BooleanExpression::Eq(box FieldElementExpression::Number(n1), box FieldElementExpression::Number(n2)) => {
				BooleanExpression::Value(n1 == n2)
			},
			BooleanExpression::Lt(box FieldElementExpression::Number(n1), box FieldElementExpression::Number(n2)) => {
				BooleanExpression::Value(n1 < n2)
			},
			BooleanExpression::Le(box FieldElementExpression::Number(n1), box FieldElementExpression::Number(n2)) => {
				BooleanExpression::Value(n1 <= n2)
			}
			BooleanExpression::Gt(box FieldElementExpression::Number(n1), box FieldElementExpression::Number(n2)) => {
				BooleanExpression::Value(n1 > n2)
			},
			BooleanExpression::Ge(box FieldElementExpression::Number(n1), box FieldElementExpression::Number(n2)) => {
				BooleanExpression::Value(n1 >= n2)
			}
			BooleanExpression::Eq(box e1, box e2) => {
				BooleanExpression::Eq(box e1.propagate(), box e2.propagate()).propagate()
			}
			BooleanExpression::Lt(box e1, box e2) => {
				BooleanExpression::Eq(box e1.propagate(), box e2.propagate()).propagate()
			}
			BooleanExpression::Le(box e1, box e2) => {
				BooleanExpression::Eq(box e1.propagate(), box e2.propagate()).propagate()
			}
			BooleanExpression::Gt(box e1, box e2) => {
				BooleanExpression::Eq(box e1.propagate(), box e2.propagate()).propagate()
			}
			BooleanExpression::Ge(box e1, box e2) => {
				BooleanExpression::Eq(box e1.propagate(), box e2.propagate()).propagate()
			}
			_ => self
		}
	}
}

impl<T: Field> Propagate for TypedStatement<T> {
	fn propagate(self) -> TypedStatement<T> {
		match self {
			TypedStatement::Return(expressions) => TypedStatement::Return(expressions.into_iter().map(|e| e.propagate()).collect()),
			TypedStatement::Definition(var, expr) => TypedStatement::Definition(var, expr.propagate()),
			TypedStatement::Condition(e1, e2) => TypedStatement::Condition(e1.propagate(), e2.propagate()),
			TypedStatement::For(v, from, to, stats) => TypedStatement::For(v, from, to, stats.into_iter().map(|s| s.propagate()).collect()),
			_ => self
		}
	}
}

impl<T: Field> Propagate for TypedFunction<T> {
	fn propagate(self) -> TypedFunction<T> {
		TypedFunction {
			statements: self.statements.into_iter().map(|s| s.propagate()).collect(),
			..self
		}
	}
}

impl<T: Field> Propagate for TypedProg<T> {
	fn propagate(self) -> TypedProg<T> {
		TypedProg {
			functions: self.functions.into_iter().map(|f| f.propagate()).collect(),
			..self
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use field::FieldPrime;

	#[cfg(test)]
	mod field {
		use super::*;

		#[test]
		fn add() {
			let e = FieldElementExpression::Add(
				box FieldElementExpression::Number(FieldPrime::from(2)),
				box FieldElementExpression::Number(FieldPrime::from(3))
			);

			assert_eq!(e.propagate(), FieldElementExpression::Number(FieldPrime::from(5)));
		}

		#[test]
		fn sub() {
			let e = FieldElementExpression::Sub(
				box FieldElementExpression::Number(FieldPrime::from(3)),
				box FieldElementExpression::Number(FieldPrime::from(2))
			);

			assert_eq!(e.propagate(), FieldElementExpression::Number(FieldPrime::from(1)));
		}

		#[test]
		fn mult() {
			let e = FieldElementExpression::Mult(
				box FieldElementExpression::Number(FieldPrime::from(3)),
				box FieldElementExpression::Number(FieldPrime::from(2))
			);

			assert_eq!(e.propagate(), FieldElementExpression::Number(FieldPrime::from(6)));
		}

		#[test]
		fn div() {
			let e = FieldElementExpression::Div(
				box FieldElementExpression::Number(FieldPrime::from(6)),
				box FieldElementExpression::Number(FieldPrime::from(2))
			);

			assert_eq!(e.propagate(), FieldElementExpression::Number(FieldPrime::from(3)));
		}

		#[test]
		fn pow() {
			let e = FieldElementExpression::Pow(
				box FieldElementExpression::Number(FieldPrime::from(2)),
				box FieldElementExpression::Number(FieldPrime::from(3))
			);

			assert_eq!(e.propagate(), FieldElementExpression::Number(FieldPrime::from(8)));
		}

		#[test]
		fn if_else_true() {
			let e = FieldElementExpression::IfElse(
				box BooleanExpression::Value(true),
				box FieldElementExpression::Number(FieldPrime::from(2)),
				box FieldElementExpression::Number(FieldPrime::from(3))
			);

			assert_eq!(e.propagate(), FieldElementExpression::Number(FieldPrime::from(2)));
		}

		#[test]
		fn if_else_false() {
			let e = FieldElementExpression::IfElse(
				box BooleanExpression::Value(false),
				box FieldElementExpression::Number(FieldPrime::from(2)),
				box FieldElementExpression::Number(FieldPrime::from(3))
			);

			assert_eq!(e.propagate(), FieldElementExpression::Number(FieldPrime::from(3)));
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

			assert_eq!(e_true.propagate(), BooleanExpression::Value(true));
			assert_eq!(e_false.propagate(), BooleanExpression::Value(false));
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

			assert_eq!(e_true.propagate(), BooleanExpression::Value(true));
			assert_eq!(e_false.propagate(), BooleanExpression::Value(false));
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

			assert_eq!(e_true.propagate(), BooleanExpression::Value(true));
			assert_eq!(e_false.propagate(), BooleanExpression::Value(false));
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

			assert_eq!(e_true.propagate(), BooleanExpression::Value(true));
			assert_eq!(e_false.propagate(), BooleanExpression::Value(false));
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

			assert_eq!(e_true.propagate(), BooleanExpression::Value(true));
			assert_eq!(e_false.propagate(), BooleanExpression::Value(false));
		}
	}
}