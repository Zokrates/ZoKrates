use crate::absy::{
    types::{UnresolvedSignature, UnresolvedType},
    ConstantGenericNode, Expression,
};
use crate::flat_absy::{
    FlatDirective, FlatExpression, FlatFunctionIterator, FlatParameter, FlatStatement,
    FlatVariable, RuntimeError,
};
use crate::solvers::Solver;
use crate::typed_absy::types::{
    ConcreteGenericsAssignment, DeclarationConstant, DeclarationSignature, DeclarationType,
    GenericIdentifier,
};
use std::collections::HashMap;
use zokrates_field::Field;

cfg_if::cfg_if! {
    if #[cfg(feature = "bellman")] {
        use pairing_ce::bn256::Bn256;
        use zokrates_embed::{bellman::{from_bellman, generate_sha256_round_constraints}};
    }
}

cfg_if::cfg_if! {
    if #[cfg(feature = "ark")] {
        use ark_bls12_377::Bls12_377;
        use zokrates_embed::ark::{from_ark, generate_verify_constraints};
    }
}

/// A low level function that contains non-deterministic introduction of variables. It is carried out as is until
/// the flattening step when it can be inlined.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy, PartialOrd, Ord)]
pub enum FlatEmbed {
    BitArrayLe,
    Unpack,
    U8ToBits,
    U16ToBits,
    U32ToBits,
    U64ToBits,
    U8FromBits,
    U16FromBits,
    U32FromBits,
    U64FromBits,
    #[cfg(feature = "bellman")]
    Sha256Round,
    #[cfg(feature = "ark")]
    SnarkVerifyBls12377,
}

impl FlatEmbed {
    pub fn signature(&self) -> UnresolvedSignature {
        match self {
            FlatEmbed::BitArrayLe => UnresolvedSignature::new()
                .generics(vec![ConstantGenericNode::mock("N")])
                .inputs(vec![
                    UnresolvedType::array(
                        UnresolvedType::Boolean.into(),
                        Expression::Identifier("N").into(),
                    )
                    .into(),
                    UnresolvedType::array(
                        UnresolvedType::Boolean.into(),
                        Expression::Identifier("N").into(),
                    )
                    .into(),
                ])
                .outputs(vec![UnresolvedType::Boolean.into()]),
            FlatEmbed::Unpack => UnresolvedSignature::new()
                .generics(vec!["N".into()])
                .inputs(vec![UnresolvedType::FieldElement.into()])
                .outputs(vec![UnresolvedType::array(
                    UnresolvedType::Boolean.into(),
                    Expression::Identifier("N").into(),
                )
                .into()]),
            FlatEmbed::U8ToBits => UnresolvedSignature::new()
                .inputs(vec![UnresolvedType::Uint(8).into()])
                .outputs(vec![UnresolvedType::array(
                    UnresolvedType::Boolean.into(),
                    Expression::U32Constant(8).into(),
                )
                .into()]),
            FlatEmbed::U16ToBits => UnresolvedSignature::new()
                .inputs(vec![UnresolvedType::Uint(16).into()])
                .outputs(vec![UnresolvedType::array(
                    UnresolvedType::Boolean.into(),
                    Expression::U32Constant(16).into(),
                )
                .into()]),
            FlatEmbed::U32ToBits => UnresolvedSignature::new()
                .inputs(vec![UnresolvedType::Uint(32).into()])
                .outputs(vec![UnresolvedType::array(
                    UnresolvedType::Boolean.into(),
                    Expression::U32Constant(32).into(),
                )
                .into()]),
            FlatEmbed::U64ToBits => UnresolvedSignature::new()
                .inputs(vec![UnresolvedType::Uint(64).into()])
                .outputs(vec![UnresolvedType::array(
                    UnresolvedType::Boolean.into(),
                    Expression::U32Constant(64).into(),
                )
                .into()]),
            FlatEmbed::U8FromBits => UnresolvedSignature::new()
                .outputs(vec![UnresolvedType::Uint(8).into()])
                .inputs(vec![UnresolvedType::array(
                    UnresolvedType::Boolean.into(),
                    Expression::U32Constant(8).into(),
                )
                .into()]),
            FlatEmbed::U16FromBits => UnresolvedSignature::new()
                .outputs(vec![UnresolvedType::Uint(16).into()])
                .inputs(vec![UnresolvedType::array(
                    UnresolvedType::Boolean.into(),
                    Expression::U32Constant(16).into(),
                )
                .into()]),
            FlatEmbed::U32FromBits => UnresolvedSignature::new()
                .outputs(vec![UnresolvedType::Uint(32).into()])
                .inputs(vec![UnresolvedType::array(
                    UnresolvedType::Boolean.into(),
                    Expression::U32Constant(32).into(),
                )
                .into()]),
            FlatEmbed::U64FromBits => UnresolvedSignature::new()
                .outputs(vec![UnresolvedType::Uint(64).into()])
                .inputs(vec![UnresolvedType::array(
                    UnresolvedType::Boolean.into(),
                    Expression::U32Constant(64).into(),
                )
                .into()]),
            #[cfg(feature = "bellman")]
            FlatEmbed::Sha256Round => UnresolvedSignature::new()
                .inputs(vec![
                    UnresolvedType::array(
                        UnresolvedType::Boolean.into(),
                        Expression::U32Constant(512).into(),
                    )
                    .into(),
                    UnresolvedType::array(
                        UnresolvedType::Boolean.into(),
                        Expression::U32Constant(256).into(),
                    )
                    .into(),
                ])
                .outputs(vec![UnresolvedType::array(
                    UnresolvedType::Boolean.into(),
                    Expression::U32Constant(256).into(),
                )
                .into()]),
            #[cfg(feature = "ark")]
            FlatEmbed::SnarkVerifyBls12377 => UnresolvedSignature::new()
                .generics(vec!["N".into(), "V".into()])
                .inputs(vec![
                    UnresolvedType::array(
                        UnresolvedType::FieldElement.into(),
                        Expression::Identifier("N").into(),
                    )
                    .into(), // inputs
                    UnresolvedType::array(
                        UnresolvedType::FieldElement.into(),
                        Expression::U32Constant(8).into(),
                    )
                    .into(), // proof
                    UnresolvedType::array(
                        UnresolvedType::FieldElement.into(),
                        Expression::Identifier("V").into(),
                    )
                    .into(), // 18 + (2 * n) // vk
                ])
                .outputs(vec![UnresolvedType::Boolean.into()]),
        }
    }

    pub fn typed_signature<T>(&self) -> DeclarationSignature<'static, T> {
        match self {
            FlatEmbed::BitArrayLe => DeclarationSignature::new()
                .generics(vec![Some(DeclarationConstant::Generic(
                    GenericIdentifier::with_name("N").with_index(0),
                ))])
                .inputs(vec![
                    DeclarationType::array((
                        DeclarationType::Boolean,
                        GenericIdentifier::with_name("N").with_index(0),
                    )),
                    DeclarationType::array((
                        DeclarationType::Boolean,
                        GenericIdentifier::with_name("N").with_index(0),
                    )),
                ])
                .outputs(vec![DeclarationType::Boolean]),
            FlatEmbed::Unpack => DeclarationSignature::new()
                .generics(vec![Some(DeclarationConstant::Generic(
                    GenericIdentifier::with_name("N").with_index(0),
                ))])
                .inputs(vec![DeclarationType::FieldElement])
                .outputs(vec![DeclarationType::array((
                    DeclarationType::Boolean,
                    GenericIdentifier::with_name("N").with_index(0),
                ))]),
            FlatEmbed::U8ToBits => DeclarationSignature::new()
                .inputs(vec![DeclarationType::uint(8)])
                .outputs(vec![DeclarationType::array((
                    DeclarationType::Boolean,
                    8u32,
                ))]),
            FlatEmbed::U16ToBits => DeclarationSignature::new()
                .inputs(vec![DeclarationType::uint(16)])
                .outputs(vec![DeclarationType::array((
                    DeclarationType::Boolean,
                    16u32,
                ))]),
            FlatEmbed::U32ToBits => DeclarationSignature::new()
                .inputs(vec![DeclarationType::uint(32)])
                .outputs(vec![DeclarationType::array((
                    DeclarationType::Boolean,
                    32u32,
                ))]),
            FlatEmbed::U64ToBits => DeclarationSignature::new()
                .inputs(vec![DeclarationType::uint(64)])
                .outputs(vec![DeclarationType::array((
                    DeclarationType::Boolean,
                    64u32,
                ))]),
            FlatEmbed::U8FromBits => DeclarationSignature::new()
                .outputs(vec![DeclarationType::uint(8)])
                .inputs(vec![DeclarationType::array((
                    DeclarationType::Boolean,
                    8u32,
                ))]),
            FlatEmbed::U16FromBits => DeclarationSignature::new()
                .outputs(vec![DeclarationType::uint(16)])
                .inputs(vec![DeclarationType::array((
                    DeclarationType::Boolean,
                    16u32,
                ))]),
            FlatEmbed::U32FromBits => DeclarationSignature::new()
                .outputs(vec![DeclarationType::uint(32)])
                .inputs(vec![DeclarationType::array((
                    DeclarationType::Boolean,
                    32u32,
                ))]),
            FlatEmbed::U64FromBits => DeclarationSignature::new()
                .outputs(vec![DeclarationType::uint(64)])
                .inputs(vec![DeclarationType::array((
                    DeclarationType::Boolean,
                    64u32,
                ))]),
            #[cfg(feature = "bellman")]
            FlatEmbed::Sha256Round => DeclarationSignature::new()
                .inputs(vec![
                    DeclarationType::array((DeclarationType::Boolean, 512u32)),
                    DeclarationType::array((DeclarationType::Boolean, 256u32)),
                ])
                .outputs(vec![DeclarationType::array((
                    DeclarationType::Boolean,
                    256u32,
                ))]),
            #[cfg(feature = "ark")]
            FlatEmbed::SnarkVerifyBls12377 => DeclarationSignature::new()
                .generics(vec![
                    Some(DeclarationConstant::Generic(
                        GenericIdentifier::with_name("N").with_index(0),
                    )),
                    Some(DeclarationConstant::Generic(
                        GenericIdentifier::with_name("V").with_index(1),
                    )),
                ])
                .inputs(vec![
                    DeclarationType::array((
                        DeclarationType::FieldElement,
                        GenericIdentifier::with_name("N").with_index(0),
                    )), // inputs
                    DeclarationType::array((DeclarationType::FieldElement, 8u32)), // proof
                    DeclarationType::array((
                        DeclarationType::FieldElement,
                        GenericIdentifier::with_name("V").with_index(1),
                    )), // 18 + (2 * n) // vk
                ])
                .outputs(vec![DeclarationType::Boolean]),
        }
    }

    pub fn generics<'ast, T>(&self, assignment: &ConcreteGenericsAssignment<'ast>) -> Vec<u32> {
        let gen = self.typed_signature().generics.into_iter().map(
            |c: Option<DeclarationConstant<'ast, T>>| match c.unwrap() {
                DeclarationConstant::Generic(g) => g,
                _ => unreachable!(),
            },
        );

        assert_eq!(gen.len(), assignment.0.len());
        gen.map(|g| *assignment.0.get(&g).unwrap() as u32).collect()
    }

    pub fn id(&self) -> &'static str {
        match self {
            FlatEmbed::BitArrayLe => "_BIT_ARRAY_LT",
            FlatEmbed::Unpack => "_UNPACK",
            FlatEmbed::U8ToBits => "_U8_TO_BITS",
            FlatEmbed::U16ToBits => "_U16_TO_BITS",
            FlatEmbed::U32ToBits => "_U32_TO_BITS",
            FlatEmbed::U64ToBits => "_U64_TO_BITS",
            FlatEmbed::U8FromBits => "_U8_FROM_BITS",
            FlatEmbed::U16FromBits => "_U16_FROM_BITS",
            FlatEmbed::U32FromBits => "_U32_FROM_BITS",
            FlatEmbed::U64FromBits => "_U64_FROM_BITS",
            #[cfg(feature = "bellman")]
            FlatEmbed::Sha256Round => "_SHA256_ROUND",
            #[cfg(feature = "ark")]
            FlatEmbed::SnarkVerifyBls12377 => "_SNARK_VERIFY_BLS12_377",
        }
    }

    // /// Actually get the `FlatFunction` that this `FlatEmbed` represents
    // pub fn synthetize<T: Field>(&self, generics: &[u32]) -> FlatFunctionIterator<T> {
    //     match self {
    //         FlatEmbed::Unpack => unpack_to_bitwidth(generics[0] as usize),
    //         #[cfg(feature = "bellman")]
    //         FlatEmbed::Sha256Round => sha256_round(),
    //         #[cfg(feature = "ark")]
    //         FlatEmbed::SnarkVerifyBls12377 => snark_verify_bls12_377(generics[0] as usize),
    //         _ => unreachable!(),
    //     }
    // }
}

// util to convert a vector of `(variable_id, coefficient)` to a flat_expression
// we build a binary tree of additions by splitting the vector recursively
#[cfg(any(feature = "ark", feature = "bellman"))]
fn flat_expression_from_vec<T: Field>(v: &[(usize, T)]) -> FlatExpression<T> {
    match v.len() {
        0 => FlatExpression::Number(T::zero()),
        1 => {
            let (key, val) = v[0].clone();
            FlatExpression::Mult(
                box FlatExpression::Number(val),
                box FlatExpression::Identifier(FlatVariable::new(key)),
            )
        }
        n => {
            let (u, v) = v.split_at(n / 2);
            FlatExpression::Add(
                box flat_expression_from_vec::<T>(u),
                box flat_expression_from_vec::<T>(v),
            )
        }
    }
}

/// Returns a flat function which computes a sha256 round
///
/// # Remarks
///
/// The variables inside the function are set in this order:
/// - constraint system variables
/// - arguments
#[cfg(feature = "bellman")]
pub fn sha256_round<T: Field>(
) -> FlatFunctionIterator<T, impl IntoIterator<Item = FlatStatement<T>>> {
    use zokrates_field::Bn128Field;
    assert_eq!(T::id(), Bn128Field::id());

    // Define iterators for all indices at hand
    let (r1cs, input_indices, current_hash_indices, output_indices) =
        generate_sha256_round_constraints::<Bn256>();

    // The output count
    let return_count = output_indices.len();
    // indices of the input
    let input_indices = input_indices.into_iter();
    // indices of the current hash
    let current_hash_indices = current_hash_indices.into_iter();
    // indices of the output
    let output_indices = output_indices.into_iter();
    let variable_count = r1cs.aux_count + 1; // auxiliary and ONE
                                             // indices of the sha256round constraint system variables
    let cs_indices = 0..variable_count;
    // indices of the arguments to the function
    // apply an offset of `variable_count` to get the indice of our dummy `input` argument
    let input_argument_indices: Vec<_> = input_indices
        .clone()
        .into_iter()
        .map(|i| i + variable_count)
        .collect();
    // apply an offset of `variable_count` to get the indice of our dummy `current_hash` argument
    let current_hash_argument_indices: Vec<_> = current_hash_indices
        .clone()
        .into_iter()
        .map(|i| i + variable_count)
        .collect();
    // define parameters to the function based on the variables
    let arguments = input_argument_indices
        .clone()
        .into_iter()
        .chain(current_hash_argument_indices.clone())
        .map(|i| FlatParameter {
            id: FlatVariable::new(i),
            private: true,
        })
        .collect();
    // define a binding of the first variable in the constraint system to one
    let one_binding_statement = FlatStatement::Condition(
        FlatVariable::new(0).into(),
        FlatExpression::Number(T::from(1)),
        RuntimeError::BellmanOneBinding,
    );
    let input_binding_statements =
    // bind input and current_hash to inputs
    input_indices.chain(current_hash_indices).zip(input_argument_indices.clone().into_iter().chain(current_hash_argument_indices.clone())).map(|(cs_index, argument_index)| {
        FlatStatement::Condition(
            FlatVariable::new(cs_index).into(),
            FlatVariable::new(argument_index).into(),
            RuntimeError::BellmanInputBinding
        )
    });
    // insert flattened statements to represent constraints
    let constraint_statements = r1cs.constraints.into_iter().map(|c| {
        let c = from_bellman::<T, Bn256>(c);
        let rhs_a = flat_expression_from_vec::<T>(c.a.as_slice());
        let rhs_b = flat_expression_from_vec::<T>(c.b.as_slice());
        let lhs = flat_expression_from_vec::<T>(c.c.as_slice());

        FlatStatement::Condition(
            lhs,
            FlatExpression::Mult(box rhs_a, box rhs_b),
            RuntimeError::BellmanConstraint,
        )
    });

    // define which subset of the witness is returned
    let outputs = output_indices.map(|o| FlatExpression::Identifier(FlatVariable::new(o)));
    // insert a directive to set the witness based on the bellman gadget and  inputs
    let directive_statement = FlatStatement::Directive(FlatDirective {
        outputs: cs_indices.map(FlatVariable::new).collect(),
        inputs: input_argument_indices
            .into_iter()
            .chain(current_hash_argument_indices)
            .map(|i| FlatVariable::new(i).into())
            .collect(),
        solver: Solver::Sha256Round,
    });
    // insert a statement to return the subset of the witness
    let return_statements = outputs
        .into_iter()
        .enumerate()
        .map(|(index, e)| FlatStatement::Definition(FlatVariable::public(index), e));
    let statements = std::iter::once(directive_statement)
        .chain(std::iter::once(one_binding_statement))
        .chain(input_binding_statements)
        .chain(constraint_statements)
        .chain(return_statements);

    FlatFunctionIterator {
        arguments,
        statements,
        return_count,
    }
}

#[cfg(feature = "ark")]
pub fn snark_verify_bls12_377<T: Field>(
    n: usize,
) -> FlatFunctionIterator<T, impl IntoIterator<Item = FlatStatement<T>>> {
    use zokrates_field::Bw6_761Field;
    assert_eq!(T::id(), Bw6_761Field::id());

    let (out_index, input_indices, proof_indices, vk_indices, constraints, variable_count) =
        generate_verify_constraints(n);

    let cs_indices = 0..variable_count;
    let input_indices = input_indices.into_iter();
    let proof_indices = proof_indices.into_iter();
    let vk_indices = vk_indices.into_iter();

    // indices of the arguments to the function
    let input_argument_indices = input_indices.clone().map(|i| i + variable_count);

    let proof_argument_indices = proof_indices.clone().map(|i| i + variable_count);

    let vk_argument_indices = vk_indices.clone().map(|i| i + variable_count);

    let input_arguments = input_argument_indices
        .clone()
        .map(|i| FlatParameter::private(FlatVariable::new(i)));

    let proof_arguments = proof_argument_indices
        .clone()
        .map(|i| FlatParameter::private(FlatVariable::new(i)));

    let vk_arguments = vk_argument_indices
        .clone()
        .map(|i| FlatParameter::private(FlatVariable::new(i)));

    let arguments = input_arguments
        .chain(proof_arguments)
        .chain(vk_arguments)
        .collect();

    let one_binding_statement = FlatStatement::Condition(
        FlatExpression::Identifier(FlatVariable::new(0)),
        FlatExpression::Number(T::from(1)),
        RuntimeError::ArkOneBinding,
    );

    let input_binding_statements: Vec<_> = input_indices
        .chain(proof_indices)
        .chain(vk_indices)
        .zip(
            input_argument_indices
                .clone()
                .chain(proof_argument_indices.clone())
                .chain(vk_argument_indices.clone()),
        )
        .map(|(cs_index, argument_index)| {
            FlatStatement::Condition(
                FlatVariable::new(cs_index).into(),
                FlatVariable::new(argument_index).into(),
                RuntimeError::ArkInputBinding,
            )
        })
        .collect();

    let constraint_statements: Vec<FlatStatement<T>> = constraints
        .into_iter()
        .map(|c| {
            let c = from_ark::<T, Bls12_377>(c);
            let rhs_a = flat_expression_from_vec::<T>(c.a.as_slice());
            let rhs_b = flat_expression_from_vec::<T>(c.b.as_slice());
            let lhs = flat_expression_from_vec::<T>(c.c.as_slice());

            FlatStatement::Condition(
                lhs,
                FlatExpression::Mult(box rhs_a, box rhs_b),
                RuntimeError::ArkConstraint,
            )
        })
        .collect();

    let return_statement = FlatStatement::Definition(
        FlatVariable::public(0),
        FlatExpression::Identifier(FlatVariable::new(out_index)),
    );

    // insert a directive to set the witness
    let directive_statement = FlatStatement::Directive(FlatDirective {
        outputs: cs_indices.map(FlatVariable::new).collect(),
        inputs: input_argument_indices
            .chain(proof_argument_indices)
            .chain(vk_argument_indices)
            .map(|i| FlatVariable::new(i).into())
            .collect(),
        solver: Solver::SnarkVerifyBls12377(n),
    });

    let statements = std::iter::once(directive_statement)
        .chain(std::iter::once(one_binding_statement))
        .chain(input_binding_statements)
        .chain(constraint_statements)
        .chain(std::iter::once(return_statement));

    FlatFunctionIterator {
        arguments,
        statements,
        return_count: 1,
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
/// * the return value of the `FlatFunction` is not deterministic if `bit_width >= T::get_required_bits()`
///   as some elements can have multiple representations: For example, `unpack(0)` is `[0, ..., 0]` but also `unpack(p)`
pub fn unpack_to_bitwidth<T: Field>(
    bit_width: usize,
) -> FlatFunctionIterator<T, impl IntoIterator<Item = FlatStatement<T>>> {
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

    #[allow(clippy::needless_collect)]
    let outputs: Vec<_> = directive_outputs
        .iter()
        .enumerate()
        .map(|(_, o)| FlatExpression::Identifier(*o))
        .collect();

    // o253, o252, ... o{253 - (bit_width - 1)} are bits
    let mut statements: Vec<FlatStatement<T>> = (0..bit_width)
        .map(|index| {
            let bit = FlatExpression::Identifier(FlatVariable::new(bit_width - index));
            FlatStatement::Condition(
                bit.clone(),
                FlatExpression::Mult(box bit.clone(), box bit.clone()),
                RuntimeError::Bitness,
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
        RuntimeError::Sum,
    ));

    statements.insert(
        0,
        FlatStatement::Directive(FlatDirective {
            inputs: directive_inputs,
            outputs: directive_outputs,
            solver,
        }),
    );

    statements.extend(
        outputs
            .into_iter()
            .enumerate()
            .map(|(index, e)| FlatStatement::Definition(FlatVariable::public(index), e)),
    );

    FlatFunctionIterator {
        arguments,
        statements: statements.into_iter(),
        return_count: bit_width,
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
            let unpack =
                unpack_to_bitwidth::<Bn128Field>(Bn128Field::get_required_bits()).collect();

            assert_eq!(
                unpack.arguments,
                vec![FlatParameter::private(FlatVariable::new(0))]
            );
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
                unpack.statements.len(),
                Bn128Field::get_required_bits() + 1 + 1 + Bn128Field::get_required_bits()
            ) // 254 bit checks, 1 directive, 1 sum check, 254 returns
        }
    }

    #[cfg(feature = "bellman")]
    #[cfg(test)]
    mod sha256 {
        use super::*;
        use crate::ir::Interpreter;

        #[test]
        fn generate_sha256_constraints() {
            let compiled = sha256_round::<Bn128Field>();

            let compiled = compiled.collect();

            // function should have 768 inputs
            assert_eq!(compiled.arguments.len(), 768);

            // function should return 256 values
            assert_eq!(compiled.return_count, 256,);

            // directive should take 768 inputs and return n_var outputs
            let directive = compiled
                .statements
                .iter()
                .filter_map(|s| match s {
                    FlatStatement::Directive(d) => Some(d.clone()),
                    _ => None,
                })
                .next()
                .unwrap();
            assert_eq!(directive.inputs.len(), 768);
            assert_eq!(directive.outputs.len(), 26935);
            // function input should be offset by variable_count
            assert_eq!(
                compiled.arguments[0].id,
                FlatVariable::new(directive.outputs.len() + 1)
            );

            // bellman variable #0: index 0 should equal 1
            assert_eq!(
                compiled.statements[1],
                FlatStatement::Condition(
                    FlatVariable::new(0).into(),
                    FlatExpression::Number(Bn128Field::from(1)),
                    RuntimeError::BellmanOneBinding
                )
            );

            // bellman input #0: index 1 should equal zokrates input #0: index v_count
            assert_eq!(
                compiled.statements[2],
                FlatStatement::Condition(
                    FlatVariable::new(1).into(),
                    FlatVariable::new(26936).into(),
                    RuntimeError::BellmanInputBinding
                )
            );

            let input: Vec<_> = (0..512)
                .map(|_| 0)
                .chain((0..256).map(|_| 1))
                .map(Bn128Field::from)
                .collect();

            let ir = crate::ir::from_flat::from_flat(compiled);

            let interpreter = Interpreter::default();
            interpreter.execute(ir, &input).unwrap();
        }
    }
}
