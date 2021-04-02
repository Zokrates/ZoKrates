use crate::flat_absy::{
    FlatDirective, FlatExpression, FlatExpressionList, FlatFunction, FlatParameter, FlatStatement,
    FlatVariable,
};
use crate::solvers::Solver;
use crate::typed_absy::types::{
    ConcreteGenericsAssignment, Constant, DeclarationSignature, DeclarationType,
};
use std::collections::HashMap;
use zokrates_field::{Bn128Field, Field};

cfg_if::cfg_if! {
    if #[cfg(feature = "bellman")] {
        use pairing_ce::bn256::Bn256;
        use pairing_ce::ff::{PrimeField, PrimeFieldRepr};
        use pairing_ce::Engine;
        use zokrates_embed::{generate_sha256_round_constraints, BellmanConstraint};
    }
}

/// A low level function that contains non-deterministic introduction of variables. It is carried out as is until
/// the flattening step when it can be inlined.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
pub enum FlatEmbed {
    U32ToField,
    #[cfg(feature = "bellman")]
    Sha256Round,
    Unpack,
    U8ToBits,
    U16ToBits,
    U32ToBits,
    U64ToBits,
    U8FromBits,
    U16FromBits,
    U32FromBits,
    U64FromBits,
}

impl FlatEmbed {
    pub fn signature(&self) -> DeclarationSignature<'static> {
        match self {
            FlatEmbed::U32ToField => DeclarationSignature::new()
                .inputs(vec![DeclarationType::uint(32)])
                .outputs(vec![DeclarationType::FieldElement]),
            FlatEmbed::Unpack => DeclarationSignature::new()
                .generics(vec![Some(Constant::Generic("N"))])
                .inputs(vec![DeclarationType::FieldElement])
                .outputs(vec![DeclarationType::array((
                    DeclarationType::Boolean,
                    "N",
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
        }
    }

    pub fn generics<'ast>(&self, assignment: &ConcreteGenericsAssignment<'ast>) -> Vec<u32> {
        let gen = self
            .signature()
            .generics
            .into_iter()
            .map(|c| match c.unwrap() {
                Constant::Generic(g) => g,
                _ => unreachable!(),
            });

        assert_eq!(gen.len(), assignment.0.len());
        gen.map(|g| *assignment.0.get(&g).clone().unwrap() as u32)
            .collect()
    }

    pub fn id(&self) -> &'static str {
        match self {
            FlatEmbed::U32ToField => "_U32_TO_FIELD",
            #[cfg(feature = "bellman")]
            FlatEmbed::Sha256Round => "_SHA256_ROUND",
            FlatEmbed::Unpack => "_UNPACK",
            FlatEmbed::U8ToBits => "_U8_TO_BITS",
            FlatEmbed::U16ToBits => "_U16_TO_BITS",
            FlatEmbed::U32ToBits => "_U32_TO_BITS",
            FlatEmbed::U64ToBits => "_U64_TO_BITS",
            FlatEmbed::U8FromBits => "_U8_FROM_BITS",
            FlatEmbed::U16FromBits => "_U16_FROM_BITS",
            FlatEmbed::U32FromBits => "_U32_FROM_BITS",
            FlatEmbed::U64FromBits => "_U64_FROM_BITS",
        }
    }

    /// Actually get the `FlatFunction` that this `FlatEmbed` represents
    pub fn synthetize<T: Field>(&self, generics: &[u32]) -> FlatFunction<T> {
        match self {
            #[cfg(feature = "bellman")]
            FlatEmbed::Sha256Round => sha256_round(),
            FlatEmbed::Unpack => unpack_to_bitwidth(generics[0] as usize),
            _ => unreachable!(),
        }
    }
}

// util to convert a vector of `(variable_id, coefficient)` to a flat_expression
// we build a binary tree of additions by splitting the vector recursively
#[cfg(feature = "bellman")]
fn flat_expression_from_vec<T: Field, E: Engine>(v: &[(usize, E::Fr)]) -> FlatExpression<T> {
    match v.len() {
        0 => FlatExpression::Number(T::zero()),
        1 => {
            let (key, val) = v[0];
            let mut res: Vec<u8> = vec![];
            val.into_repr().write_le(&mut res).unwrap();
            FlatExpression::Mult(
                box FlatExpression::Number(T::from_byte_vector(res)),
                box FlatExpression::Identifier(FlatVariable::new(key)),
            )
        }
        n => {
            let (u, v) = v.split_at(n / 2);
            FlatExpression::Add(
                box flat_expression_from_vec::<T, E>(u),
                box flat_expression_from_vec::<T, E>(v),
            )
        }
    }
}

#[cfg(feature = "bellman")]
impl<T: Field, E: Engine> From<BellmanConstraint<E>> for FlatStatement<T> {
    fn from(c: BellmanConstraint<E>) -> FlatStatement<T> {
        let rhs_a = flat_expression_from_vec::<T, E>(&c.a);
        let rhs_b = flat_expression_from_vec::<T, E>(&c.b);
        let lhs = flat_expression_from_vec::<T, E>(&c.c);

        FlatStatement::Condition(lhs, FlatExpression::Mult(box rhs_a, box rhs_b))
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
    );
    let input_binding_statements =
    // bind input and current_hash to inputs
    input_indices.chain(current_hash_indices).zip(input_argument_indices.clone().chain(current_hash_argument_indices.clone())).map(|(cs_index, argument_index)| {
        FlatStatement::Condition(
            FlatVariable::new(cs_index).into(),
            FlatVariable::new(argument_index).into(),
        )
    });
    // insert flattened statements to represent constraints
    let constraint_statements = r1cs.constraints.into_iter().map(|c| c.into());
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
                    FlatExpression::Number(Bn128Field::from(1))
                )
            );

            // bellman input #0: index 1 should equal zokrates input #0: index v_count
            assert_eq!(
                compiled.statements[2],
                FlatStatement::Condition(
                    FlatVariable::new(1).into(),
                    FlatVariable::new(26936).into()
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
