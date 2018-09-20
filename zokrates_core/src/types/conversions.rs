use flat_absy::*;
use flat_absy::flat_variable::FlatVariable;
use field::Field;
use types::Type;
use flat_absy::flat_parameter::FlatParameter;
use helpers::{Helper, RustHelper, DirectiveStatement};
use reduce::Reduce;
use types::constraints::Constraint;
use bimap::BiMap;

fn use_variable(bijection: &mut BiMap<String, FlatVariable>, name: String, mut index: usize) -> FlatVariable {
	let var = FlatVariable::new(index);
	index = index + 1;
	var
}

pub fn cast<T: Field>(from: &Type, to: &Type) -> FlatFunction<T> {

	let mut counter = 0;

	let mut bijection = BiMap::new();

	let arguments = (0..from.get_primitive_count()).enumerate().map(|(index, _)| FlatParameter {
		id: FlatVariable::new(index),
		private: true
	}).collect();

	let directive_inputs = (0..from.get_primitive_count()).map(|index| use_variable(&mut bijection, format!("i{}", index), counter)).collect();
	let directive_outputs: Vec<FlatVariable> = (0..to.get_primitive_count()).map(|index| use_variable(&mut bijection, format!("o{}", index), counter)).collect();

	let constraints = to.get_constraints::<T>().constraints;

	let intermediate_variables = match constraints.len() {
		0 => vec![],
		_ => constraints[0].a.iter().enumerate().map(|(_, index)| use_variable(&mut bijection, format!("inter{}", index), counter)).collect()
	};

	let conditions: Vec<FlatStatement<T>> = to.get_constraints().constraints.iter().map(|constraint: &Constraint<T>| {
		let rhs_a = match constraint.a.iter()
			.enumerate()
			.map(|(key, val)| FlatExpression::Mult(box FlatExpression::Number(val.clone()), box FlatExpression::Identifier(intermediate_variables[key])))
			.reduce(|acc, e| FlatExpression::Add(box acc, box e)) {
	            Some(e @ FlatExpression::Mult(..)) => FlatExpression::Add(box FlatExpression::Number(T::zero()), box e), // the R1CS serializer only recognizes Add
	            Some(e) => e,
	            None => FlatExpression::Number(T::zero())
	        };
		
		let rhs_b = match constraint.b.iter()
			.enumerate()
			.map(|(key, val)| FlatExpression::Mult(box FlatExpression::Number(val.clone()), box FlatExpression::Identifier(intermediate_variables[key])))
			.reduce(|acc, e| FlatExpression::Add(box acc, box e)) {
	            Some(e @ FlatExpression::Mult(..)) => FlatExpression::Add(box FlatExpression::Number(T::zero()), box e), // the R1CS serializer only recognizes Add
	            Some(e) => e,
	            None => FlatExpression::Number(T::zero())
	        };
		
		let lhs = match constraint.c.iter()
			.enumerate()
			.map(|(key, val)| FlatExpression::Mult(box FlatExpression::Number(val.clone()), box FlatExpression::Identifier(intermediate_variables[key])))
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

	let outputs = directive_outputs.iter().map(|o| FlatExpression::Identifier(o.clone())).collect();

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
		arguments,
		statements,
		return_count,
	}
}