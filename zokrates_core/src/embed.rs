use crate::solvers::Solver;
use bellman::pairing::ff::ScalarEngine;
use typed_absy::types::{FunctionKey, Signature, Type};
use typed_absy::*;
use zokrates_embed::{generate_sha256_round_constraints, BellmanConstraint};
use zokrates_field::field::Field;

/// A low level function that contains non-deterministic introduction of variables. It is carried out as is until
/// the flattening step when it can be inlined.
#[derive(Debug, Clone, PartialEq)]
pub enum FlatEmbed {
    Sha256Round,
    Unpack,
}

static SHA_256_ROUND_STR: &'static str = "sha256round";
static UNPACK_STR: &'static str = "unpack";

impl FlatEmbed {
    pub fn signature<T: Field>(&self) -> Signature {
        match self {
            FlatEmbed::Sha256Round => Signature::new()
                .inputs(vec![
                    Type::array(Type::FieldElement, 512),
                    Type::array(Type::FieldElement, 256),
                ])
                .outputs(vec![Type::array(Type::FieldElement, 256)]),
            FlatEmbed::Unpack => Signature::new()
                .inputs(vec![Type::FieldElement])
                .outputs(vec![Type::array(
                    Type::FieldElement,
                    T::get_required_bits(),
                )]),
        }
    }

    pub fn key<T: Field>(&self) -> FunctionKey<'static> {
        FunctionKey::with_id(self.id()).signature(self.signature::<T>())
    }

    pub fn id(&self) -> &'static str {
        match self {
            FlatEmbed::Sha256Round => "_SHA256_ROUND",
            FlatEmbed::Unpack => "_UNPACK",
        }
    }

    /// Actually get the `TypedFunction` that this `FlatEmbed` represents
    pub fn synthetize<T: Field>(&self) -> TypedFunction<T> {
        match self {
            FlatEmbed::Sha256Round => sha256_round(),
            FlatEmbed::Unpack => unpack(),
        }
    }
}

fn typed_expression_from_vec<T: Field>(
    v: Vec<(usize, <<T as Field>::BellmanEngine as ScalarEngine>::Fr)>,
) -> FieldElementExpression<'static, T> {
    balanced_addition(
        v.into_iter()
            .map(|(key, val)| {
                FieldElementExpression::Mult(
                    box FieldElementExpression::Number(T::from_bellman(val)),
                    box FieldElementExpression::Identifier(Identifier::internal(
                        SHA_256_ROUND_STR,
                        key,
                    )),
                )
            })
            .collect(),
    )
}

// util to convert a vector of `(variable_id, coefficient)` to a flat_expression
fn balanced_addition<T: Field>(
    v: Vec<FieldElementExpression<'static, T>>,
) -> FieldElementExpression<'static, T> {
    let mut v = v;
    match v.len() {
        0 => FieldElementExpression::Number(T::zero()),
        1 => v.pop().unwrap(),
        n => {
            let u = v.split_off(n / 2);
            FieldElementExpression::Add(box balanced_addition(u), box balanced_addition(v))
        }
    }
}

impl<T: Field> From<BellmanConstraint<T::BellmanEngine>> for TypedStatement<'static, T> {
    fn from(c: zokrates_embed::BellmanConstraint<T::BellmanEngine>) -> TypedStatement<'static, T> {
        let rhs_a = typed_expression_from_vec(c.a);
        let rhs_b = typed_expression_from_vec(c.b);
        let lhs = typed_expression_from_vec(c.c);

        TypedStatement::Condition(
            lhs.into(),
            FieldElementExpression::Mult(box rhs_a, box rhs_b).into(),
        )
    }
}

fn sha256_round<T: Field>() -> TypedFunction<'static, T> {
    // Define iterators for all indices at hand
    let (r1cs, input_indices, current_hash_indices, output_indices) =
        generate_sha256_round_constraints::<T::BellmanEngine>();

    // indices of the input
    let input_indices = input_indices.into_iter();
    // indices of the current hash
    let current_hash_indices = current_hash_indices.into_iter();
    // indices of the output
    let output_indices = output_indices.into_iter();

    let variable_count = r1cs.aux_count + 1; // auxiliary and ONE

    // each constraint system variable is a field element represented by an identifier (annotated in `[0, variable_count[`)
    // the two inputs are arrays annotated respectively `variable_count` and `variable_count + 1`
    let input_identifier = Identifier::internal(SHA_256_ROUND_STR, variable_count);
    let current_hash_identifier = Identifier::internal(SHA_256_ROUND_STR, variable_count + 1);

    // indices of the sha256round constraint system variables
    let cs_indices = (0..variable_count).into_iter();

    // define parameters to the function
    let arguments = vec![
        Parameter {
            id: Variable::array(input_identifier.clone(), Type::FieldElement, 512),
            private: true,
        },
        Parameter {
            id: Variable::array(current_hash_identifier.clone(), Type::FieldElement, 256),
            private: true,
        },
    ];

    // Bind constraint system variables to the inputs
    let input_binding_statements: Vec<_> = input_indices
        .clone()
        .chain(current_hash_indices.clone())
        .enumerate()
        .map(|(index, i)| {
            TypedStatement::Condition(
                FieldElementExpression::Identifier(Identifier::internal(SHA_256_ROUND_STR, i))
                    .into(),
                if index < 512 {
                    FieldElementExpression::select(
                        ArrayExpressionInner::Identifier(input_identifier.clone())
                            .annotate(Type::FieldElement, 512),
                        FieldElementExpression::Number(T::from(index)),
                    )
                    .into()
                } else {
                    FieldElementExpression::select(
                        ArrayExpressionInner::Identifier(current_hash_identifier.clone())
                            .annotate(Type::FieldElement, 256),
                        FieldElementExpression::Number(T::from(index - 512)),
                    )
                    .into()
                },
            )
        })
        .collect();

    // define a binding of the first variable in the constraint system to ~ONE
    let one_binding_statement = TypedStatement::Condition(
        FieldElementExpression::Identifier(Identifier::internal(SHA_256_ROUND_STR, 0)).into(),
        FieldElementExpression::Number(T::from(1)).into(),
    );

    // insert flattened statements to represent constraints
    let constraint_statements = r1cs.constraints.into_iter().map(|c| c.into());

    // define which subset of the witness is returned
    let output = ArrayExpressionInner::Value(
        output_indices
            .map(|o| {
                FieldElementExpression::Identifier(Identifier::internal(SHA_256_ROUND_STR, o))
                    .into()
            })
            .collect(),
    )
    .annotate(Type::FieldElement, 256)
    .into();

    // insert a directive to set the witness based on the bellman gadget and inputs
    let directive_statement = TypedStatement::Directive(TypedDirective {
        outputs: cs_indices
            .map(|i| Variable::field_element(Identifier::internal(SHA_256_ROUND_STR, i)))
            .collect(),
        inputs: vec![
            ArrayExpressionInner::Identifier(input_identifier)
                .annotate(Type::FieldElement, 512)
                .into(),
            ArrayExpressionInner::Identifier(current_hash_identifier)
                .annotate(Type::FieldElement, 256)
                .into(),
        ],
        solver: Solver::Sha256Round,
    });

    // insert a statement to return the subset of the witness
    let return_statement = TypedStatement::Return(vec![output]);

    let statements: Vec<_> = std::iter::once(directive_statement)
        .chain(constraint_statements)
        .chain(std::iter::once(one_binding_statement))
        .chain(input_binding_statements)
        .chain(std::iter::once(return_statement))
        .collect();

    let res = TypedFunction {
        arguments,
        statements,
        signature: FlatEmbed::Sha256Round.signature::<T>(),
    };

    res
}

/// A `FlatFunction` which returns a bit decomposition of a field element
///
/// # Remarks
/// * the return value of the `FlatFunction` is not deterministic: as we decompose over log_2(p) + 1 bits, some
///   elements can have multiple representations: For example, `unpack(0)` is `[0, ..., 0]` but also `unpack(p)`
pub fn unpack<'ast, T: Field>() -> TypedFunction<'static, T> {
    let nbits = T::get_required_bits();

    let input_identifier = Identifier::internal(UNPACK_STR, 0);
    let output_identifier = Identifier::internal(UNPACK_STR, 1);

    let arguments = vec![Parameter {
        id: Variable::field_element(input_identifier.clone()),
        private: true,
    }];

    // o0, ..., o253 = ToBits(i0)

    let directive_inputs =
        vec![FieldElementExpression::Identifier(input_identifier.clone()).into()];
    let directive_output = ArrayExpressionInner::Identifier(output_identifier.clone())
        .annotate(Type::FieldElement, T::get_required_bits());

    let solver = Solver::bits();

    let outputs = ArrayExpressionInner::Value(
        (0..nbits)
            .map(|i| {
                FieldElementExpression::Select(
                    box directive_output.clone(),
                    box FieldElementExpression::Number(T::from(i)),
                )
                .into()
            })
            .collect(),
    )
    .annotate(Type::FieldElement, nbits);

    // o253, o252, ... o{253 - (nbits - 1)} are bits
    let bit_constraint_statements: Vec<TypedStatement<T>> = (0..nbits)
        .map(|i| {
            let bit = FieldElementExpression::Select(
                box directive_output.clone(),
                box FieldElementExpression::Number(T::from(T::get_required_bits() - i - 1)),
            );
            TypedStatement::Condition(
                bit.clone().into(),
                FieldElementExpression::Mult(box bit.clone(), box bit).into(),
            )
        })
        .collect();

    // sum check: o253 + o252 * 2 + ... + o{253 - (nbits - 1)} * 2**(nbits - 1)
    let lhs_sum = balanced_addition(
        (0..nbits)
            .map(|i| {
                FieldElementExpression::Mult(
                    box FieldElementExpression::Select(
                        box directive_output.clone(),
                        box FieldElementExpression::Number(T::from(T::get_required_bits() - i - 1)),
                    ),
                    box FieldElementExpression::Number(T::from(2).pow(i)),
                )
            })
            .collect(),
    );

    let lhs_sum_check = TypedStatement::Condition(
        lhs_sum.into(),
        FieldElementExpression::Mult(
            box FieldElementExpression::Identifier(input_identifier.clone()),
            box FieldElementExpression::Number(T::from(1)),
        )
        .into(),
    );

    let directive_statement = TypedStatement::Directive(TypedDirective {
        inputs: directive_inputs,
        outputs: vec![Variable::array(
            output_identifier.clone(),
            Type::FieldElement,
            nbits,
        )],
        solver: solver,
    });

    let return_statement = TypedStatement::Return(vec![outputs.into()]);

    let statements = std::iter::once(directive_statement)
        .chain(bit_constraint_statements)
        .chain(std::iter::once(lhs_sum_check))
        .chain(std::iter::once(return_statement))
        .collect();

    let signature = FlatEmbed::Unpack.signature::<T>();

    TypedFunction {
        arguments,
        statements,
        signature,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    #[cfg(test)]
    mod split {
        use super::*;

        #[test]
        fn split254() {
            let unpack: TypedFunction<FieldPrime> = unpack();

            // assert_eq!(
            //     unpack.arguments,
            //     vec![FlatParameter::private(FlatVariable::new(0))]
            // );
            // assert_eq!(
            //     unpack.statements.len(),
            //     FieldPrime::get_required_bits() + 1 + 1 + 1
            // ); // 128 bit checks, 1 directive, 1 sum check, 1 return
            // assert_eq!(
            //     unpack.statements[0],
            //     FlatStatement::Directive(FlatDirective::new(
            //         (0..FieldPrime::get_required_bits())
            //             .map(|i| FlatVariable::new(i + 1))
            //             .collect(),
            //         Solver::bits(),
            //         vec![FlatVariable::new(0)]
            //     ))
            // );
            // assert_eq!(
            //     *unpack.statements.last().unwrap(),
            //     FlatStatement::Return(FlatExpressionList {
            //         expressions: (0..FieldPrime::get_required_bits())
            //             .map(|i| FlatExpression::Identifier(FlatVariable::new(i + 1)))
            //             .collect()
            //     })
            // );
        }
    }

    #[cfg(test)]
    mod sha256 {
        use super::*;

        #[test]
        fn generate_sha256_constraints() {
            let compiled = sha256_round::<FieldPrime>();

            // // function should have 2 inputs
            // assert_eq!(compiled.arguments.len(), 2);

            // // function should return 1 values
            // assert_eq!(
            //     compiled
            //         .statements
            //         .iter()
            //         .filter_map(|s| match s {
            //             TypedStatement::Return(v) => Some(v),
            //             _ => None,
            //         })
            //         .next()
            //         .unwrap()
            //         .len(),
            //     1,
            // );

            // // directive should take 768 inputs and return n_var outputs
            // let directive = compiled
            //     .statements
            //     .iter()
            //     .filter_map(|s| match s {
            //         TypedStatement::Directive(d) => Some(d.clone()),
            //         _ => None,
            //     })
            //     .next()
            //     .unwrap();
            // assert_eq!(directive.inputs.len(), 1);
            // assert_eq!(directive.outputs.len(), 1);
            // // function input should be offset by variable_count
            // assert_eq!(
            //     compiled.arguments[0].id,
            //     FlatVariable::new(directive.outputs.len() + 1)
            // );

            // // bellman variable #0: index 0 should equal 1
            // assert_eq!(
            //     compiled.statements[1],
            //     FlatStatement::Condition(
            //         FlatVariable::new(0).into(),
            //         FlatExpression::Number(FieldPrime::from(1))
            //     )
            // );

            // // bellman input #0: index 1 should equal zokrates input #0: index v_count
            // assert_eq!(
            //     compiled.statements[2],
            //     FlatStatement::Condition(
            //         FlatVariable::new(1).into(),
            //         FlatVariable::new(26936).into()
            //     )
            // );

            // let f = crate::ir::Function::from(compiled);
            // let prog = crate::ir::Prog {
            //     main: f,
            //     private: vec![true; 768],
            // };

            // let input = (0..512)
            //     .map(|_| FieldPrime::from(0))
            //     .chain((0..256).map(|_| FieldPrime::from(1)))
            //     .collect();

            // prog.execute(&input).unwrap();
        }
    }
}
