use crate::flat_absy::{
    FlatDirective, FlatExpression, FlatExpressionList, FlatFunction, FlatParameter, FlatStatement,
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
#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
pub enum FlatEmbed {
    U32ToField,
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
    pub fn signature(&self) -> DeclarationSignature<'static> {
        match self {
            FlatEmbed::U32ToField => DeclarationSignature::new()
                .inputs(vec![DeclarationType::uint(32)])
                .outputs(vec![DeclarationType::FieldElement]),
            FlatEmbed::Unpack => DeclarationSignature::new()
                .generics(vec![Some(DeclarationConstant::Generic(
                    GenericIdentifier {
                        name: "N",
                        index: 0,
                    },
                ))])
                .inputs(vec![DeclarationType::FieldElement])
                .outputs(vec![DeclarationType::array((
                    DeclarationType::Boolean,
                    GenericIdentifier {
                        name: "N",
                        index: 0,
                    },
                ))]),
            FlatEmbed::U8ToBits => DeclarationSignature::new()
                .inputs(vec![DeclarationType::uint(8)])
                .outputs(vec![DeclarationType::array((
                    DeclarationType::Boolean,
                    8usize,
                ))]),
            FlatEmbed::U16ToBits => DeclarationSignature::new()
                .inputs(vec![DeclarationType::uint(16)])
                .outputs(vec![DeclarationType::array((
                    DeclarationType::Boolean,
                    16usize,
                ))]),
            FlatEmbed::U32ToBits => DeclarationSignature::new()
                .inputs(vec![DeclarationType::uint(32)])
                .outputs(vec![DeclarationType::array((
                    DeclarationType::Boolean,
                    32usize,
                ))]),
            FlatEmbed::U64ToBits => DeclarationSignature::new()
                .inputs(vec![DeclarationType::uint(64)])
                .outputs(vec![DeclarationType::array((
                    DeclarationType::Boolean,
                    64usize,
                ))]),
            FlatEmbed::U8FromBits => DeclarationSignature::new()
                .outputs(vec![DeclarationType::uint(8)])
                .inputs(vec![DeclarationType::array((
                    DeclarationType::Boolean,
                    8usize,
                ))]),
            FlatEmbed::U16FromBits => DeclarationSignature::new()
                .outputs(vec![DeclarationType::uint(16)])
                .inputs(vec![DeclarationType::array((
                    DeclarationType::Boolean,
                    16usize,
                ))]),
            FlatEmbed::U32FromBits => DeclarationSignature::new()
                .outputs(vec![DeclarationType::uint(32)])
                .inputs(vec![DeclarationType::array((
                    DeclarationType::Boolean,
                    32usize,
                ))]),
            FlatEmbed::U64FromBits => DeclarationSignature::new()
                .outputs(vec![DeclarationType::uint(64)])
                .inputs(vec![DeclarationType::array((
                    DeclarationType::Boolean,
                    64usize,
                ))]),
            #[cfg(feature = "bellman")]
            FlatEmbed::Sha256Round => DeclarationSignature::new()
                .inputs(vec![
                    DeclarationType::array((DeclarationType::Boolean, 512usize)),
                    DeclarationType::array((DeclarationType::Boolean, 256usize)),
                ])
                .outputs(vec![DeclarationType::array((
                    DeclarationType::Boolean,
                    256usize,
                ))]),
            #[cfg(feature = "ark")]
            FlatEmbed::SnarkVerifyBls12377 => DeclarationSignature::new()
                .generics(vec![
                    Some(DeclarationConstant::Generic(GenericIdentifier {
                        name: "N",
                        index: 0,
                    })),
                    Some(DeclarationConstant::Generic(GenericIdentifier {
                        name: "V",
                        index: 1,
                    })),
                ])
                .inputs(vec![
                    DeclarationType::array((
                        DeclarationType::FieldElement,
                        GenericIdentifier {
                            name: "N",
                            index: 0,
                        },
                    )), // inputs
                    DeclarationType::array((DeclarationType::FieldElement, 8usize)), // proof
                    DeclarationType::array((
                        DeclarationType::FieldElement,
                        GenericIdentifier {
                            name: "V",
                            index: 1,
                        },
                    )), // 18 + (2 * n) // vk
                ])
                .outputs(vec![DeclarationType::Boolean]),
        }
    }

    pub fn generics<'ast>(&self, assignment: &ConcreteGenericsAssignment<'ast>) -> Vec<u32> {
        let gen = self
            .signature()
            .generics
            .into_iter()
            .map(|c| match c.unwrap() {
                DeclarationConstant::Generic(g) => g,
                _ => unreachable!(),
            });

        assert_eq!(gen.len(), assignment.0.len());
        gen.map(|g| *assignment.0.get(&g).unwrap() as u32).collect()
    }

    pub fn id(&self) -> &'static str {
        match self {
            FlatEmbed::U32ToField => "_U32_TO_FIELD",
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

    /// Actually get the `FlatFunction` that this `FlatEmbed` represents
    pub fn synthetize<T: Field>(&self, generics: &[u32]) -> FlatFunction<T> {
        match self {
            FlatEmbed::Unpack => unpack_to_bitwidth(generics[0] as usize),
            #[cfg(feature = "bellman")]
            FlatEmbed::Sha256Round => sha256_round(),
            #[cfg(feature = "ark")]
            FlatEmbed::SnarkVerifyBls12377 => snark_verify_bls12_377(generics[0] as usize),
            _ => unreachable!(),
        }
    }
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
pub fn sha256_round<T: Field>() -> FlatFunction<T> {
    use zokrates_field::Bn128Field;
    assert_eq!(T::id(), Bn128Field::id());

    // Define iterators for all indices at hand
    let (r1cs, input_indices, current_hash_indices, output_indices) =
        generate_sha256_round_constraints::<Bn256>();
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
    let input_argument_indices = input_indices
        .clone()
        .into_iter()
        .map(|i| i + variable_count);
    // apply an offset of `variable_count` to get the indice of our dummy `current_hash` argument
    let current_hash_argument_indices = current_hash_indices
        .clone()
        .into_iter()
        .map(|i| i + variable_count);
    // define parameters to the function based on the variables
    let arguments = input_argument_indices
        .clone()
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
    input_indices.chain(current_hash_indices).zip(input_argument_indices.clone().chain(current_hash_argument_indices.clone())).map(|(cs_index, argument_index)| {
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
    let outputs: Vec<FlatExpression<T>> = output_indices
        .map(|o| FlatExpression::Identifier(FlatVariable::new(o)))
        .collect();
    // insert a directive to set the witness based on the bellman gadget and  inputs
    let directive_statement = FlatStatement::Directive(FlatDirective {
        outputs: cs_indices.map(FlatVariable::new).collect(),
        inputs: input_argument_indices
            .chain(current_hash_argument_indices)
            .map(|i| FlatVariable::new(i).into())
            .collect(),
        solver: Solver::Sha256Round,
    });
    // insert a statement to return the subset of the witness
    let return_statement = FlatStatement::Return(FlatExpressionList {
        expressions: outputs,
    });
    let statements = std::iter::once(directive_statement)
        .chain(std::iter::once(one_binding_statement))
        .chain(input_binding_statements)
        .chain(constraint_statements)
        .chain(std::iter::once(return_statement))
        .collect();
    FlatFunction {
        arguments,
        statements,
    }
}

#[cfg(feature = "ark")]
pub fn snark_verify_bls12_377<T: Field>(n: usize) -> FlatFunction<T> {
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

    let return_statement = FlatStatement::Return(FlatExpressionList {
        expressions: vec![FlatExpression::Identifier(FlatVariable::new(out_index))],
    });

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

    let statements: Vec<_> = std::iter::once(directive_statement)
        .chain(std::iter::once(one_binding_statement))
        .chain(input_binding_statements)
        .chain(constraint_statements)
        .chain(std::iter::once(return_statement))
        .collect();

    FlatFunction {
        arguments,
        statements,
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

    #[cfg(feature = "bellman")]
    #[cfg(test)]
    mod sha256 {
        use super::*;
        use crate::ir::Interpreter;

        #[test]
        fn generate_sha256_constraints() {
            let compiled = sha256_round::<Bn128Field>();

            // function should have 768 inputs
            assert_eq!(compiled.arguments.len(), 768);

            // function should return 256 values
            assert_eq!(
                compiled
                    .statements
                    .iter()
                    .filter_map(|s| match s {
                        FlatStatement::Return(v) => Some(v),
                        _ => None,
                    })
                    .next()
                    .unwrap()
                    .expressions
                    .len(),
                256,
            );

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

            let f = crate::ir::Function::from(compiled);
            let prog = crate::ir::Prog {
                main: f,
                private: vec![true; 768],
            };

            let input: Vec<_> = (0..512)
                .map(|_| 0)
                .chain((0..256).map(|_| 1))
                .map(Bn128Field::from)
                .collect();

            let interpreter = Interpreter::default();
            interpreter.execute(&prog, &input).unwrap();
        }
    }
}
