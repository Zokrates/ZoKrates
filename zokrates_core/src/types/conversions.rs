use types::signature::Signature;
use flat_absy::*;
use flat_absy::flat_variable::FlatVariable;
use field::Field;
use types::Type;
use flat_absy::flat_parameter::FlatParameter;
use helpers::{Helper, RustHelper, DirectiveStatement};
use reduce::Reduce;
use types::constraints::Constraint;
use bimap::BiMap;

fn use_variable(bijection: &mut BiMap<String, FlatVariable>, name: String, index: &mut usize) -> FlatVariable {
	let var = FlatVariable::new(*index);
	bijection.insert(name, var);
	*index = *index + 1;
	var
}

pub fn cast<T: Field>(from: &Type, to: &Type) -> FlatFunction<T> {

	let mut counter = 0;

	let mut bijection = BiMap::new();

	let arguments = (0..from.get_primitive_count()).enumerate().map(|(index, _)| FlatParameter {
		id: FlatVariable::new(index),
		private: true
	}).collect();

	let directive_inputs = (0..from.get_primitive_count()).map(|index| use_variable(&mut bijection, format!("i{}", index), &mut counter)).collect();
	let directive_outputs: Vec<FlatVariable> = (0..to.get_primitive_count()).map(|index| use_variable(&mut bijection, format!("o{}", index), &mut counter)).collect();

	let constraints = to.get_constraints::<T>().constraints;

	let intermediate_variables = match constraints.len() {
		0 => vec![],
		_ => constraints[0].a.iter().enumerate().map(|(_, index)| use_variable(&mut bijection, format!("inter{}", index), &mut counter)).collect()
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

	let signature = Signature {
			inputs: vec![from.clone()],
			outputs: vec![to.clone()],
		};

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
		signature
	}
}

#[cfg(test)]
mod tests {
	use field::FieldPrime;
	use super::*;

	#[test]
	fn field_to_bool() {
		let f2b: FlatFunction<FieldPrime> = cast(&Type::FieldElement, &Type::Boolean);
		assert_eq!(f2b.id, String::from("_field_to_bool"));
		assert_eq!(f2b.arguments, vec![FlatParameter::private(FlatVariable::new(0))]);
		assert_eq!(f2b.statements.len(), 3); // 1 directive, 1 constraint, 1 return
		assert_eq!(
			f2b.statements[0], 
			FlatStatement::Directive(
				DirectiveStatement::new(
					vec![FlatVariable::new(1)],
					Helper::Rust(RustHelper::Identity),
					vec![FlatVariable::new(0)]
				)
			)
		);
		assert_eq!(
			f2b.statements[2], 
			FlatStatement::Return(
				FlatExpressionList {
					expressions: vec![FlatExpression::Identifier(FlatVariable::new(1))]
				}
			)
		);
		assert_eq!(f2b.signature.outputs.len(), 1);
	}

	#[test]
	fn bool_to_field() {
		let b2f: FlatFunction<FieldPrime> = cast(&Type::Boolean, &Type::FieldElement);
		assert_eq!(b2f.id, String::from("_bool_to_field"));
		assert_eq!(b2f.arguments, vec![FlatParameter::private(FlatVariable::new(0))]);
		assert_eq!(b2f.statements.len(), 2); // 1 directive, 1 return
		assert_eq!(
			b2f.statements[0], 
			FlatStatement::Directive(
				DirectiveStatement::new(
					vec![FlatVariable::new(1)],
					Helper::Rust(RustHelper::Identity),
					vec![FlatVariable::new(0)]
				)
			)
		);
		assert_eq!(
			b2f.statements[1], 
			FlatStatement::Return(
				FlatExpressionList {
					expressions: vec![FlatExpression::Identifier(FlatVariable::new(1))]
				}
			)
		);
		assert_eq!(b2f.signature.outputs.len(), 1);
	}
}