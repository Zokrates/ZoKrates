use flat_absy::*;
use field::Field;
use absy::variable::Variable;
use types::Type;
use types::signature::Signature;
use flat_absy::flat_parameter::FlatParameter;
use helpers::{Helper, RustHelper, DirectiveStatement};
use reduce::Reduce;
use types::constraints::Constraint;


pub fn cast<T: Field>(from: &Type, to: &Type) -> FlatFunction<T> {

	let arguments = (0..from.get_primitive_count()).enumerate().map(|(index, _)| FlatParameter {
		id: format!("i{}", index),
		private: true
	}).collect();

	let directive_inputs = (0..from.get_primitive_count()).enumerate().map(|(index, _)| format!("i{}", index)).collect();
	let directive_outputs: Vec<String> = (0..to.get_primitive_count()).enumerate().map(|(index, _)| format!("inter{}", index)).collect();

	let conditions: Vec<FlatStatement<T>> = to.get_constraints().constraints.iter().map(|constraint: &Constraint<T>| {
		let rhs_a = match constraint.a.iter()
			.enumerate()
			.map(|(key, val)| FlatExpression::Mult(box FlatExpression::Number(val.clone()), box FlatExpression::Identifier(format!("inter{}",key.clone()))))
			.reduce(|acc, e| FlatExpression::Add(box acc, box e)) {
	            Some(e @ FlatExpression::Mult(..)) => FlatExpression::Add(box FlatExpression::Number(T::zero()), box e), // the R1CS serializer only recognizes Add
	            Some(e) => e,
	            None => FlatExpression::Number(T::zero())
	        };
		
		let rhs_b = match constraint.b.iter()
			.enumerate()
			.map(|(key, val)| FlatExpression::Mult(box FlatExpression::Number(val.clone()), box FlatExpression::Identifier(format!("inter{}",key.clone()))))
			.reduce(|acc, e| FlatExpression::Add(box acc, box e)) {
	            Some(e @ FlatExpression::Mult(..)) => FlatExpression::Add(box FlatExpression::Number(T::zero()), box e), // the R1CS serializer only recognizes Add
	            Some(e) => e,
	            None => FlatExpression::Number(T::zero())
	        };
		
		let lhs = match constraint.c.iter()
			.enumerate()
			.map(|(key, val)| FlatExpression::Mult(box FlatExpression::Number(val.clone()), box FlatExpression::Identifier(format!("inter{}",key.clone()))))
			.reduce(|acc, e| FlatExpression::Add(box acc, box e)) {
	            Some(e @ FlatExpression::Mult(..)) => FlatExpression::Add(box FlatExpression::Number(T::zero()), box e), // the R1CS serializer only recognizes Add
	            Some(e) => e,
	            None => FlatExpression::Number(T::zero())
	        };

		FlatStatement::Condition(lhs, FlatExpression::Mult(box rhs_a, box rhs_b))
	}).collect();

	let helper = match (from, to) {
		(Type::Boolean, Type::FieldElement) => {
			Helper::Rust(RustHelper::Identity)
		},
		(Type::FieldElement, Type::Boolean) => {
			Helper::Rust(RustHelper::Identity)
		}
		_ => panic!(format!("can't cast {} to {}", from, to))
	};

	let return_count = to.get_primitive_count();

	let outputs = directive_outputs.iter().map(|o| FlatExpression::Identifier(o.to_string())).collect();

	let mut statements = conditions;

	statements.insert(0, FlatStatement::Directive(
		DirectiveStatement {
			inputs: directive_inputs,
			outputs: directive_outputs,
			helper: helper
		}
	));

	statements.push(FlatStatement::Return(
		FlatExpressionList {
			expressions: outputs		
		}
	));

	FlatFunction {
		id: format!("_{}_to_{}", from, to),
		arguments: arguments,
		statements: statements,
		return_count: return_count
	}
}