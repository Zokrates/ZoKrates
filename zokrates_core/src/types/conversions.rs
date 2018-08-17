use types::signature::Signature;
use flat_absy::*;
use field::Field;
use types::Type;
use flat_absy::flat_parameter::FlatParameter;
use helpers::{Helper, RustHelper, DirectiveStatement};
use reduce::Reduce;
use types::constraints::Constraint;


pub fn cast<T: Field>(from: &Type, to: &Type) -> FlatFunction<T> {

	let arguments = (0..from.get_primitive_count()).enumerate().map(|(index, _)| FlatParameter {
		id: format!("i{}", index),
		private: true
	}).collect();

	let directive_inputs: Vec<String> = (0..from.get_primitive_count()).enumerate().map(|(index, _)| format!("i{}", index)).collect();
	let directive_outputs: Vec<String> = (0..to.get_primitive_count()).enumerate().map(|(index, _)| format!("inter{}", index)).collect();

	let conditions: Vec<FlatStatement<T>> = to.get_constraints().constraints.iter().map(|constraint: &Constraint<T>| {
		let rhs_a = match constraint.a.iter()
			.enumerate()
			.filter_map(|(key, val)| {
				if *val == T::from(0) { return None };
				Some(FlatExpression::Mult(box FlatExpression::Number(val.clone()), box FlatExpression::Identifier(format!("inter{}",key.clone()))))
			})
			.reduce(|acc, e| FlatExpression::Add(box acc, box e)) {
	            Some(e @ FlatExpression::Mult(..)) => FlatExpression::Add(box FlatExpression::Number(T::zero()), box e), // the R1CS serializer only recognizes Add
	            Some(e) => e,
	            None => FlatExpression::Number(T::zero())
	        };
		
		let rhs_b = match constraint.b.iter()
			.enumerate()
			.filter_map(|(key, val)| {
				if *val == T::from(0) { return None };
				Some(FlatExpression::Mult(box FlatExpression::Number(val.clone()), box FlatExpression::Identifier(format!("inter{}",key.clone()))))
			})
			.reduce(|acc, e| FlatExpression::Add(box acc, box e)) {
	            Some(e @ FlatExpression::Mult(..)) => FlatExpression::Add(box FlatExpression::Number(T::zero()), box e), // the R1CS serializer only recognizes Add
	            Some(e) => e,
	            None => FlatExpression::Number(T::zero())
	        };
		
		let lhs = match constraint.c.iter()
			.enumerate()
			.filter_map(|(key, val)| {
				if *val == T::from(0) { return None };
				Some(FlatExpression::Mult(box FlatExpression::Number(val.clone()), box FlatExpression::Identifier(format!("inter{}",key.clone()))))
			})
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
		},
		(Type::Unsigned8, Type::FieldElement) => {
			Helper::Rust(RustHelper::FromBits)
		},
		(Type::FieldElement, Type::Unsigned8) => {
			Helper::Rust(RustHelper::ToBits)
		}
		_ => panic!(format!("can't cast {} to {}", from, to))
	};

	let mut conversion_constraints: Vec<FlatStatement<T>> = match (from, to) {
		(Type::Boolean, Type::FieldElement) => {
			vec![]
		},
		(Type::FieldElement, Type::Boolean) => {
			vec![]
		},
		(Type::Unsigned8, Type::FieldElement) => {
			let lhs: FlatExpression<T> = match directive_inputs
				.iter()
				.rev()
				.enumerate()
				.map(|(i, input)| 
					FlatExpression::Mult(
						box FlatExpression::Number(T::from(2u32.pow(i as u32))), 
						box FlatExpression::Identifier(input.to_string())
					)
				)
				.reduce(|acc, e| FlatExpression::Add(box acc, box e)) {
	            Some(e @ FlatExpression::Mult(..)) => FlatExpression::Add(box FlatExpression::Number(T::zero()), box e), // the R1CS serializer only recognizes Add
	            Some(e) => e,
	            None => FlatExpression::Number(T::zero())
	        };

	        let rhs = FlatExpression::Identifier(directive_outputs[0].clone());

			vec![
				FlatStatement::Condition(lhs, rhs),
			]
		},
		(Type::FieldElement, Type::Unsigned8) => {			
			let lhs: FlatExpression<T> = match directive_outputs
				.iter()
				.rev()
				.enumerate()
				.map(|(i, output)| 
					FlatExpression::Mult(
						box FlatExpression::Number(T::from(2u32.pow(i as u32))), 
						box FlatExpression::Identifier(output.to_string())
					)
				)
				.reduce(|acc, e| FlatExpression::Add(box acc, box e)) {
	            Some(e @ FlatExpression::Mult(..)) => FlatExpression::Add(box FlatExpression::Number(T::zero()), box e), // the R1CS serializer only recognizes Add
	            Some(e) => e,
	            None => FlatExpression::Number(T::zero())
	        };

	        let rhs = FlatExpression::Identifier(directive_inputs[0].clone());

			vec![
				FlatStatement::Condition(lhs, rhs),
			]
		}
		_ => panic!(format!("can't cast {} to {}", from, to))
	};

	let outputs = directive_outputs.iter().map(|o| FlatExpression::Identifier(o.to_string())).collect();

	let mut statements = conditions;

	statements.append(&mut conversion_constraints);

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

	let res = FlatFunction {
		id: format!("_{}_to_{}", from, to),
		arguments: arguments,
		statements: statements,
		signature: Signature {
			inputs: vec![from.clone()],
			outputs: vec![to.clone()],
		}
	};

	res
}