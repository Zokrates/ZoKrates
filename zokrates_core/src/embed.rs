use crate::flat_absy::{
    FlatDirective, FlatExpression, FlatExpressionList, FlatFunction, FlatParameter, FlatStatement,
    FlatVariable,
};
use crate::solvers::Solver;
use crate::typed_absy::types::{ConcreteFunctionKey, ConcreteSignature, ConcreteType};
use crate::typed_absy::TypedModuleId;
use std::collections::HashMap;
use zokrates_field::Field;

/// A low level function that contains non-deterministic introduction of variables. It is carried out as is until
/// the flattening step when it can be inlined.
#[derive(Debug, Clone, PartialEq, Hash)]
pub enum FlatEmbed {
    U32ToField,
    Unpack(usize),
    U8ToBits,
    U16ToBits,
    U32ToBits,
    U8FromBits,
    U16FromBits,
    U32FromBits,
}

impl FlatEmbed {
    pub fn signature(&self) -> ConcreteSignature {
        match self {
            FlatEmbed::U32ToField => ConcreteSignature::new()
                .inputs(vec![ConcreteType::uint(32)])
                .outputs(vec![ConcreteType::FieldElement]),
            FlatEmbed::Unpack(bitwidth) => ConcreteSignature::new()
                .inputs(vec![ConcreteType::FieldElement])
                .outputs(vec![ConcreteType::array(ConcreteType::Boolean, *bitwidth)]),
            FlatEmbed::U8ToBits => ConcreteSignature::new()
                .inputs(vec![ConcreteType::uint(8)])
                .outputs(vec![ConcreteType::array(ConcreteType::Boolean, 8usize)]),
            FlatEmbed::U16ToBits => ConcreteSignature::new()
                .inputs(vec![ConcreteType::uint(16)])
                .outputs(vec![ConcreteType::array(ConcreteType::Boolean, 16usize)]),
            FlatEmbed::U32ToBits => ConcreteSignature::new()
                .inputs(vec![ConcreteType::uint(32)])
                .outputs(vec![ConcreteType::array(ConcreteType::Boolean, 32usize)]),
            FlatEmbed::U8FromBits => ConcreteSignature::new()
                .outputs(vec![ConcreteType::uint(8)])
                .inputs(vec![ConcreteType::array(ConcreteType::Boolean, 8usize)]),
            FlatEmbed::U16FromBits => ConcreteSignature::new()
                .outputs(vec![ConcreteType::uint(16)])
                .inputs(vec![ConcreteType::array(ConcreteType::Boolean, 16usize)]),
            FlatEmbed::U32FromBits => ConcreteSignature::new()
                .outputs(vec![ConcreteType::uint(32)])
                .inputs(vec![ConcreteType::array(ConcreteType::Boolean, 32usize)]),
        }
    }

    pub fn key_in_module<T: Field>(
        &self,
        module_id: &TypedModuleId,
    ) -> ConcreteFunctionKey<'static> {
        ConcreteFunctionKey::with_location(module_id.clone(), self.id()).signature(self.signature())
    }

    pub fn id(&self) -> &'static str {
        match self {
            FlatEmbed::U32ToField => "_U32_TO_FIELD",
            FlatEmbed::Unpack(_) => "_UNPACK",
            FlatEmbed::U8ToBits => "_U8_TO_BITS",
            FlatEmbed::U16ToBits => "_U16_TO_BITS",
            FlatEmbed::U32ToBits => "_U32_TO_BITS",
            FlatEmbed::U8FromBits => "_U8_FROM_BITS",
            FlatEmbed::U16FromBits => "_U16_FROM_BITS",
            FlatEmbed::U32FromBits => "_U32_FROM_BITS",
        }
    }

    /// Actually get the `FlatFunction` that this `FlatEmbed` represents
    pub fn synthetize<T: Field>(&self) -> FlatFunction<T> {
        match self {
            FlatEmbed::Unpack(bitwidth) => unpack_to_bitwidth(*bitwidth),
            _ => unreachable!(),
        }
    }
}

fn use_variable(
    layout: &mut HashMap<String, FlatVariable>,
    name: String,
    index: &mut usize,
) -> FlatVariable {
    let var = FlatVariable::new(*index);
    layout.insert(name, var);
    *index += 1;
    var
}

/// A `FlatFunction` which returns a bit decomposition of a field element
///
/// # Inputs
/// * bit_width the number of bits we want to decompose to
///
/// # Remarks
/// * the return value of the `FlatFunction` is not deterministic if `bit_width == T::get_required_bits()`
///   as we decompose over `log_2(p) + 1 bits, some
///   elements can have multiple representations: For example, `unpack(0)` is `[0, ..., 0]` but also `unpack(p)`
pub fn unpack_to_bitwidth<T: Field>(bit_width: usize) -> FlatFunction<T> {
    let nbits = T::get_required_bits();

    assert!(bit_width <= nbits);

    let mut counter = 0;

    let mut layout = HashMap::new();

    let arguments = vec![FlatParameter {
        id: FlatVariable::new(0),
        private: true,
    }];

    // o0, ..., o253 = ToBits(i0)

    let directive_inputs = vec![FlatExpression::Identifier(use_variable(
        &mut layout,
        "i0".into(),
        &mut counter,
    ))];

    let directive_outputs: Vec<FlatVariable> = (0..bit_width)
        .map(|index| use_variable(&mut layout, format!("o{}", index), &mut counter))
        .collect();

    let solver = Solver::bits(bit_width);

    let outputs = directive_outputs
        .iter()
        .enumerate()
        .map(|(_, o)| FlatExpression::Identifier(*o))
        .collect::<Vec<_>>();

    // o253, o252, ... o{253 - (bit_width - 1)} are bits
    let mut statements: Vec<FlatStatement<T>> = (0..bit_width)
        .map(|index| {
            let bit = FlatExpression::Identifier(FlatVariable::new(bit_width - index));
            FlatStatement::Condition(
                bit.clone(),
                FlatExpression::Mult(box bit.clone(), box bit.clone()),
            )
        })
        .collect();

    // sum check: o253 + o252 * 2 + ... + o{253 - (bit_width - 1)} * 2**(bit_width - 1)
    let mut lhs_sum = FlatExpression::Number(T::from(0));

    for i in 0..bit_width {
        lhs_sum = FlatExpression::Add(
            box lhs_sum,
            box FlatExpression::Mult(
                box FlatExpression::Identifier(FlatVariable::new(bit_width - i)),
                box FlatExpression::Number(T::from(2).pow(i)),
            ),
        );
    }

    statements.push(FlatStatement::Condition(
        lhs_sum,
        FlatExpression::Mult(
            box FlatExpression::Identifier(FlatVariable::new(0)),
            box FlatExpression::Number(T::from(1)),
        ),
    ));

    statements.insert(
        0,
        FlatStatement::Directive(FlatDirective {
            inputs: directive_inputs,
            outputs: directive_outputs,
            solver,
        }),
    );

    statements.push(FlatStatement::Return(FlatExpressionList {
        expressions: outputs,
    }));

    FlatFunction {
        arguments,
        statements,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::Bn128Field;

    #[cfg(test)]
    mod split {
        use super::*;

        #[test]
        fn split254() {
            let unpack: FlatFunction<Bn128Field> =
                unpack_to_bitwidth(Bn128Field::get_required_bits());

            assert_eq!(
                unpack.arguments,
                vec![FlatParameter::private(FlatVariable::new(0))]
            );
            assert_eq!(
                unpack.statements.len(),
                Bn128Field::get_required_bits() + 1 + 1 + 1
            ); // 128 bit checks, 1 directive, 1 sum check, 1 return
            assert_eq!(
                unpack.statements[0],
                FlatStatement::Directive(FlatDirective::new(
                    (0..Bn128Field::get_required_bits())
                        .map(|i| FlatVariable::new(i + 1))
                        .collect(),
                    Solver::bits(Bn128Field::get_required_bits()),
                    vec![FlatVariable::new(0)]
                ))
            );
            assert_eq!(
                *unpack.statements.last().unwrap(),
                FlatStatement::Return(FlatExpressionList {
                    expressions: (0..Bn128Field::get_required_bits())
                        .map(|i| FlatExpression::Identifier(FlatVariable::new(i + 1)))
                        .collect()
                })
            );
        }
    }
}
