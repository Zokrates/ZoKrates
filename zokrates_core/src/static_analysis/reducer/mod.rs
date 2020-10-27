// The reducer reduces the program to a single function which is:
// - in SSA form
// - free of function calls (except for low level calls) thanks to inlining
// - free of for-loops thanks to unrolling

// The process happens in two steps
// 1. Shallow SSA for the `main` function
// We turn the `main` function into SSA form, but ignoring function calls and for loops
// 2. Unroll and inline
// We go through the shallow-SSA program and
// - unroll loops
// - inline function calls. This includes applying shallow-ssa on the target function

mod inline;
mod shallow_ssa;
mod unroll;

use self::inline::{inline_call, InlineError};
use std::collections::HashMap;
use typed_absy::types::GenericsAssignment;

use typed_absy::{
    CoreIdentifier, TypedExpressionList, TypedFunction, TypedFunctionSymbol, TypedModule,
    TypedModules, TypedProgram, TypedStatement,
};
use zokrates_field::Field;

use self::shallow_ssa::ShallowTransformer;

use static_analysis::Propagator;

// An SSA version map, giving access to the latest version number for each identifier
pub type Versions<'ast> = HashMap<CoreIdentifier<'ast>, usize>;

// A container to represent whether more treatment must be applied to the function
#[derive(Debug, PartialEq)]
pub enum Output<U, V> {
    Complete(U),
    Incomplete(U, V),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Error {
    Incompatible,
}

pub fn reduce_program<T: Field>(p: TypedProgram<T>) -> Result<TypedProgram<T>, Error> {
    let main_module = p.modules.get(&p.main).unwrap().clone();

    let (main_key, main_function) = main_module
        .functions
        .iter()
        .find(|(k, _)| k.id == "main")
        .unwrap()
        .clone();

    let main_function = match main_function {
        TypedFunctionSymbol::Here(f) => f.clone(),
        _ => unreachable!(),
    };

    assert_eq!(main_function.generics.len(), 0);

    let main_function = reduce_function(main_function, GenericsAssignment::default(), &p.modules)?;

    Ok(TypedProgram {
        main: p.main.clone(),
        modules: vec![(
            p.main,
            TypedModule {
                functions: vec![(main_key.clone(), TypedFunctionSymbol::Here(main_function))]
                    .into_iter()
                    .collect(),
            },
        )]
        .into_iter()
        .collect(),
    })
}

fn reduce_function<'ast, T: Field>(
    f: TypedFunction<'ast, T>,
    generics: GenericsAssignment<'ast>,
    modules: &TypedModules<'ast, T>,
) -> Result<TypedFunction<'ast, T>, Error> {
    let mut versions = Versions::default();

    match ShallowTransformer::transform(f, &generics, &mut versions) {
        Output::Complete(f) => Ok(f),
        Output::Incomplete(new_f, new_for_loop_versions) => {
            let mut for_loop_versions = new_for_loop_versions;

            let mut f = new_f;

            let statements = loop {
                match reduce_statements(
                    f.statements,
                    &mut for_loop_versions,
                    &mut versions,
                    modules,
                ) {
                    Ok(Output::Complete(statements)) => {
                        break statements;
                    }
                    Ok(Output::Incomplete(new_statements, new_for_loop_versions)) => {
                        let new_f = TypedFunction {
                            statements: new_statements,
                            ..f
                        };

                        use typed_absy::folder::Folder;

                        f = Propagator::verbose().fold_function(new_f);
                        for_loop_versions = new_for_loop_versions;
                    }
                    Err(e) => return Err(e),
                }
            };

            Ok(TypedFunction { statements, ..f })
        }
    }
}

fn reduce_statements<'ast, T: Field>(
    statements: Vec<TypedStatement<'ast, T>>,
    for_loop_versions: &mut Vec<Versions<'ast>>,
    versions: &mut Versions<'ast>,
    modules: &TypedModules<'ast, T>,
) -> Result<Output<Vec<TypedStatement<'ast, T>>, Vec<Versions<'ast>>>, Error> {
    let mut versions = versions;

    let statements = statements
        .into_iter()
        .map(|s| reduce_statement(s, for_loop_versions, &mut versions, modules));

    statements
        .into_iter()
        .fold(Ok(Output::Complete(vec![])), |state, e| match (state, e) {
            (Ok(state), Ok(e)) => {
                use self::Output::*;
                match (state, e) {
                    (Complete(mut s), Complete(c)) => {
                        s.extend(c);
                        Ok(Complete(s))
                    }
                    (Complete(mut s), Incomplete(stats, for_loop_versions)) => {
                        s.extend(stats);
                        Ok(Incomplete(s, for_loop_versions))
                    }
                    (Incomplete(mut stats, new_for_loop_versions), Complete(c)) => {
                        stats.extend(c);
                        Ok(Incomplete(stats, new_for_loop_versions))
                    }
                    (Incomplete(mut stats, mut versions), Incomplete(new_stats, new_versions)) => {
                        stats.extend(new_stats);
                        versions.extend(new_versions);
                        Ok(Incomplete(stats, versions))
                    }
                }
            }
            (Err(state), _) => Err(state),
            (Ok(_), Err(e)) => Err(e),
        })
}

fn reduce_statement<'ast, T: Field>(
    statement: TypedStatement<'ast, T>,
    _for_loop_versions: &mut Vec<Versions<'ast>>,
    versions: &mut Versions<'ast>,
    modules: &TypedModules<'ast, T>,
) -> Result<Output<Vec<TypedStatement<'ast, T>>, Vec<Versions<'ast>>>, Error> {
    use self::Output::*;

    match statement {
        TypedStatement::MultipleDefinition(
            v,
            TypedExpressionList::FunctionCall(key, arguments, output_types),
        ) => match inline_call(
            "main".into(),
            key,
            arguments,
            output_types,
            modules,
            versions,
        ) {
            Ok(Output::Complete((statements, expressions))) => {
                assert_eq!(v.len(), expressions.len());
                Ok(Output::Complete(
                    statements
                        .into_iter()
                        .chain(
                            v.into_iter()
                                .zip(expressions)
                                .map(|(v, e)| TypedStatement::Definition(v.into(), e)),
                        )
                        .collect(),
                ))
            }
            Ok(Output::Incomplete((statements, expressions), delta_for_loop_versions)) => {
                assert_eq!(v.len(), expressions.len());
                Ok(Output::Incomplete(
                    statements
                        .into_iter()
                        .chain(
                            v.into_iter()
                                .zip(expressions)
                                .map(|(v, e)| TypedStatement::Definition(v.into(), e)),
                        )
                        .collect(),
                    delta_for_loop_versions,
                ))
            }
            Err(InlineError::Generic(..)) => Err(Error::Incompatible),
            Err(InlineError::NonConstant(_module, key, arguments, output_types)) => {
                Ok(Output::Incomplete(
                    vec![TypedStatement::MultipleDefinition(
                        v,
                        TypedExpressionList::FunctionCall(key, arguments, output_types),
                    )],
                    vec![],
                ))
            }
            Err(InlineError::Flat) => unimplemented!(),
        },
        TypedStatement::For(..) => unimplemented!(),
        s => Ok(Complete(vec![s])),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typed_absy::{
        ArrayExpressionInner, ConcreteType, ConcreteVariable, DeclarationFunctionKey,
        DeclarationType, DeclarationVariable, FieldElementExpression, Identifier, Type,
        TypedExpression, TypedExpressionList, UBitwidth, UExpression, UExpressionInner, Variable,
    };
    use typed_absy::types::Constant;
    use typed_absy::types::DeclarationSignature;
    use zokrates_field::Bn128Field;

    #[test]
    fn no_generics() {
        // def foo(field a) -> field:
        //      return a
        // def main(field a) -> field:
        //      u32 n = 42
        //      n = n
        //      a = a
        //      a = foo(a)
        //      n = n
        //      return a

        // expected:
        // def main(field a_0) -> field:
        //      u32 n_0 = 42
        //      n_1 = n_0
        //      a_1 = a_0
        //      # PUSH CALL to foo with a_3 := a_1
        //      # POP CALL with foo_ifof_42 := a_3
        //      a_2 = foo_ifof_42
        //      n_2 = n_1
        //      return a_2

        let foo: TypedFunction<Bn128Field> = TypedFunction {
            generics: vec![],
            arguments: vec![DeclarationVariable::field_element("a").into()],
            statements: vec![TypedStatement::Return(vec![
                FieldElementExpression::Identifier("a".into()).into(),
            ])],
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        let main: TypedFunction<Bn128Field> = TypedFunction {
            generics: vec![],
            arguments: vec![DeclarationVariable::field_element("a").into()],
            statements: vec![
                TypedStatement::Definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    TypedExpression::Uint(42u32.into()),
                ),
                TypedStatement::Definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    UExpressionInner::Identifier("n".into())
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::Definition(
                    Variable::field_element("a").into(),
                    FieldElementExpression::Identifier("a".into()).into(),
                ),
                TypedStatement::MultipleDefinition(
                    vec![Variable::field_element("a").into()],
                    TypedExpressionList::FunctionCall(
                        DeclarationFunctionKey::with_id("foo").signature(
                            DeclarationSignature::new()
                                .inputs(vec![DeclarationType::FieldElement])
                                .outputs(vec![DeclarationType::FieldElement]),
                        ),
                        vec![FieldElementExpression::Identifier("a".into()).into()],
                        vec![Type::FieldElement],
                    ),
                ),
                TypedStatement::Definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    UExpressionInner::Identifier("n".into())
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::Return(vec![FieldElementExpression::Identifier("a".into()).into()]),
            ],
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        let p = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![
                        (
                            DeclarationFunctionKey::with_id("foo").signature(
                                DeclarationSignature::new()
                                    .inputs(vec![DeclarationType::FieldElement])
                                    .outputs(vec![DeclarationType::FieldElement]),
                            ),
                            TypedFunctionSymbol::Here(foo),
                        ),
                        (
                            DeclarationFunctionKey::with_id("main").signature(
                                DeclarationSignature::new()
                                    .inputs(vec![DeclarationType::FieldElement])
                                    .outputs(vec![DeclarationType::FieldElement]),
                            ),
                            TypedFunctionSymbol::Here(main),
                        ),
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
        };

        let reduced = reduce_program(p);

        let expected_main = TypedFunction {
            generics: vec![],
            arguments: vec![DeclarationVariable::field_element("a").into()],
            statements: vec![
                TypedStatement::Definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    TypedExpression::Uint(42u32.into()),
                ),
                TypedStatement::Definition(
                    Variable::uint(Identifier::from("n").version(1), UBitwidth::B32).into(),
                    UExpressionInner::Identifier("n".into())
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::Definition(
                    Variable::field_element(Identifier::from("a").version(1)).into(),
                    FieldElementExpression::Identifier("a".into()).into(),
                ),
                TypedStatement::PushCallLog(
                    "main".into(),
                    DeclarationFunctionKey::with_id("foo").signature(
                        DeclarationSignature::new()
                            .inputs(vec![DeclarationType::FieldElement])
                            .outputs(vec![DeclarationType::FieldElement]),
                    ),
                    GenericsAssignment::default(),
                    vec![(
                        ConcreteVariable::with_id_and_type(
                            Identifier::from("a").version(3),
                            ConcreteType::FieldElement,
                        ),
                        FieldElementExpression::Identifier(Identifier::from("a").version(1)).into(),
                    )],
                ),
                TypedStatement::PopCallLog(vec![(
                    ConcreteVariable::with_id_and_type(
                        Identifier::from(CoreIdentifier::Call(0)).version(0),
                        ConcreteType::FieldElement,
                    ),
                    FieldElementExpression::Identifier(Identifier::from("a").version(3)).into(),
                )]),
                TypedStatement::Definition(
                    Variable::field_element(Identifier::from("a").version(2)).into(),
                    FieldElementExpression::Identifier(
                        Identifier::from(CoreIdentifier::Call(0)).version(0),
                    )
                    .into(),
                ),
                TypedStatement::Definition(
                    Variable::uint(Identifier::from("n").version(2), UBitwidth::B32).into(),
                    UExpressionInner::Identifier(Identifier::from("n").version(1))
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::Return(vec![FieldElementExpression::Identifier(
                    Identifier::from("a").version(2),
                )
                .into()]),
            ],
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        let expected: TypedProgram<Bn128Field> = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![(
                        DeclarationFunctionKey::with_id("main").signature(
                            DeclarationSignature::new()
                                .inputs(vec![DeclarationType::FieldElement])
                                .outputs(vec![DeclarationType::FieldElement]),
                        ),
                        TypedFunctionSymbol::Here(expected_main),
                    )]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
        };

        assert_eq!(reduced.unwrap(), expected);
    }

    #[test]
    fn with_generics() {
        // def foo<K>(field[K] a) -> field[K]:
        //      return a
        // def main(field a) -> field:
        //      u32 n = 42
        //      n = n
        //      field[1] b = [42]
        //      b = foo(b)
        //      n = n
        //      return a

        // expected:
        // def main(field a_0) -> field:
        //      u32 n_0 = 42
        //      n_1 = n_0
        //      field[1] b_0 = [42]
        //      # PUSH CALL to foo::<1> with a_0 := b_0
        //      # POP CALL with foo_if[1]_of[1]_42 := a_0
        //      b_1 = foo_if[1]_of[1]_42
        //      n_2 = n_1
        //      return a_2

        let foo_signature = DeclarationSignature::new()
            .inputs(vec![DeclarationType::array(
                DeclarationType::FieldElement,
                Constant::Generic("K"),
            )])
            .outputs(vec![DeclarationType::array(
                DeclarationType::FieldElement,
                Constant::Generic("K"),
            )]);

        let foo: TypedFunction<Bn128Field> = TypedFunction {
            generics: vec!["K".into()],
            arguments: vec![DeclarationVariable::array(
                "a",
                DeclarationType::FieldElement,
                "K".into(),
            )
            .into()],
            statements: vec![TypedStatement::Return(vec![
                ArrayExpressionInner::Identifier("a".into())
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
            ])],
            signature: foo_signature.clone(),
        };

        let main: TypedFunction<Bn128Field> = TypedFunction {
            generics: vec![],
            arguments: vec![DeclarationVariable::field_element("a").into()],
            statements: vec![
                TypedStatement::Definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    TypedExpression::Uint(42u32.into()),
                ),
                TypedStatement::Definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    UExpressionInner::Identifier("n".into())
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::Definition(
                    Variable::array("b", Type::FieldElement, 1u32.into()).into(),
                    ArrayExpressionInner::Value(vec![
                        FieldElementExpression::Number(1.into()).into()
                    ])
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
                ),
                TypedStatement::MultipleDefinition(
                    vec![Variable::array("b", Type::FieldElement, 1u32.into()).into()],
                    TypedExpressionList::FunctionCall(
                        DeclarationFunctionKey::with_id("foo").signature(foo_signature.clone()),
                        vec![ArrayExpressionInner::Identifier("b".into())
                            .annotate(Type::FieldElement, 1u32)
                            .into()],
                        vec![Type::array(Type::FieldElement, 1u32)],
                    ),
                ),
                TypedStatement::Definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    UExpressionInner::Identifier("n".into())
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::Return(vec![FieldElementExpression::Identifier("a".into()).into()]),
            ],
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        let p = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![
                        (
                            DeclarationFunctionKey::with_id("foo").signature(foo_signature.clone()),
                            TypedFunctionSymbol::Here(foo),
                        ),
                        (
                            DeclarationFunctionKey::with_id("main").signature(
                                DeclarationSignature::new()
                                    .inputs(vec![DeclarationType::FieldElement])
                                    .outputs(vec![DeclarationType::FieldElement]),
                            ),
                            TypedFunctionSymbol::Here(main),
                        ),
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
        };

        let reduced = reduce_program(p);

        let expected_main = TypedFunction {
            generics: vec![],
            arguments: vec![DeclarationVariable::field_element("a").into()],
            statements: vec![
                TypedStatement::Definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    TypedExpression::Uint(42u32.into()),
                ),
                TypedStatement::Definition(
                    Variable::uint(Identifier::from("n").version(1), UBitwidth::B32).into(),
                    UExpressionInner::Identifier("n".into())
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::Definition(
                    Variable::array("b", Type::FieldElement, 1u32.into()).into(),
                    ArrayExpressionInner::Value(vec![
                        FieldElementExpression::Number(1.into()).into()
                    ])
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
                ),
                TypedStatement::PushCallLog(
                    "main".into(),
                    DeclarationFunctionKey::with_id("foo").signature(foo_signature.clone()),
                    GenericsAssignment(vec![("K", 1)].into_iter().collect()),
                    vec![(
                        ConcreteVariable::array(
                            Identifier::from("a").version(1),
                            ConcreteType::FieldElement,
                            1,
                        )
                        .into(),
                        ArrayExpressionInner::Identifier("b".into())
                            .annotate(Type::FieldElement, 1u32)
                            .into(),
                    )],
                ),
                TypedStatement::Definition(
                    Variable::uint("K", UBitwidth::B32).into(),
                    UExpression::from(1u32).into(),
                ),
                TypedStatement::PopCallLog(vec![(
                    ConcreteVariable::array(
                        Identifier::from(CoreIdentifier::Call(0)).version(0),
                        ConcreteType::FieldElement,
                        1,
                    ),
                    ArrayExpressionInner::Identifier(Identifier::from("a").version(1))
                        .annotate(Type::FieldElement, 1u32)
                        .into(),
                )]),
                TypedStatement::Definition(
                    Variable::array(
                        Identifier::from("b").version(1),
                        Type::FieldElement,
                        1u32.into(),
                    )
                    .into(),
                    ArrayExpressionInner::Identifier(
                        Identifier::from(CoreIdentifier::Call(0)).version(0),
                    )
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
                ),
                TypedStatement::Definition(
                    Variable::uint(Identifier::from("n").version(2), UBitwidth::B32).into(),
                    UExpressionInner::Identifier(Identifier::from("n").version(1))
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::Return(vec![FieldElementExpression::Identifier("a".into()).into()]),
            ],
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        let expected = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![(
                        DeclarationFunctionKey::with_id("main").signature(
                            DeclarationSignature::new()
                                .inputs(vec![DeclarationType::FieldElement])
                                .outputs(vec![DeclarationType::FieldElement]),
                        ),
                        TypedFunctionSymbol::Here(expected_main),
                    )]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
        };

        assert_eq!(reduced.unwrap(), expected);
    }

    #[test]
    fn with_generics_and_propagation() {
        // def foo<K>(field[K] a) -> field[K]:
        //      return a
        // def main(field a) -> field:
        //      u32 n = 2
        //      n = n
        //      field[n - 1] b = [42]
        //      b = foo(b)
        //      n = n
        //      return a

        // expected:
        // def main(field a_0) -> field:
        //      u32 n_0 = 2
        //      n_1 = 2
        //      field[1] b_0 = [42]
        //      # PUSH CALL to foo::<1> with a_3 := b_0
        //      # POP CALL with foo_if[1]of[1]_42 := a_3
        //      b_1 = foo_if[1]of[1]_42
        //      n_2 = 2
        //      return a_2

        let foo_signature = DeclarationSignature::new()
            .inputs(vec![DeclarationType::array(
                DeclarationType::FieldElement,
                Constant::Generic("K"),
            )])
            .outputs(vec![DeclarationType::array(
                DeclarationType::FieldElement,
                Constant::Generic("K"),
            )]);

        let foo: TypedFunction<Bn128Field> = TypedFunction {
            generics: vec!["K".into()],
            arguments: vec![DeclarationVariable::array(
                "a",
                DeclarationType::FieldElement,
                "K".into(),
            )
            .into()],
            statements: vec![TypedStatement::Return(vec![
                ArrayExpressionInner::Identifier("a".into())
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
            ])],
            signature: foo_signature.clone(),
        };

        let main: TypedFunction<Bn128Field> = TypedFunction {
            generics: vec![],
            arguments: vec![DeclarationVariable::field_element("a").into()],
            statements: vec![
                TypedStatement::Definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    TypedExpression::Uint(2u32.into()),
                ),
                TypedStatement::Definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    UExpressionInner::Identifier("n".into())
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::Definition(
                    Variable::array(
                        "b",
                        Type::FieldElement,
                        UExpressionInner::Sub(
                            box UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32),
                            box 1u32.into(),
                        )
                        .annotate(UBitwidth::B32),
                    )
                    .into(),
                    ArrayExpressionInner::Value(vec![
                        FieldElementExpression::Number(1.into()).into()
                    ])
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
                ),
                TypedStatement::MultipleDefinition(
                    vec![Variable::array(
                        "b",
                        Type::FieldElement,
                        UExpressionInner::Sub(
                            box UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32),
                            box 1u32.into(),
                        )
                        .annotate(UBitwidth::B32),
                    )
                    .into()],
                    TypedExpressionList::FunctionCall(
                        DeclarationFunctionKey::with_id("foo").signature(foo_signature.clone()),
                        vec![ArrayExpressionInner::Identifier("b".into())
                            .annotate(
                                Type::FieldElement,
                                UExpressionInner::Sub(
                                    box UExpressionInner::Identifier("n".into())
                                        .annotate(UBitwidth::B32),
                                    box 1u32.into(),
                                )
                                .annotate(UBitwidth::B32),
                            )
                            .into()],
                        vec![Type::array(
                            Type::FieldElement,
                            UExpressionInner::Sub(
                                box UExpressionInner::Identifier("n".into())
                                    .annotate(UBitwidth::B32),
                                box 1u32.into(),
                            )
                            .annotate(UBitwidth::B32),
                        )],
                    ),
                ),
                TypedStatement::Definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    UExpressionInner::Identifier("n".into())
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::Return(vec![FieldElementExpression::Identifier("a".into()).into()]),
            ],
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        let p = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![
                        (
                            DeclarationFunctionKey::with_id("foo").signature(foo_signature.clone()),
                            TypedFunctionSymbol::Here(foo),
                        ),
                        (
                            DeclarationFunctionKey::with_id("main").signature(
                                DeclarationSignature::new()
                                    .inputs(vec![DeclarationType::FieldElement])
                                    .outputs(vec![DeclarationType::FieldElement]),
                            ),
                            TypedFunctionSymbol::Here(main),
                        ),
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
        };

        let reduced = reduce_program(p);

        let expected_main = TypedFunction {
            generics: vec![],
            arguments: vec![DeclarationVariable::field_element("a").into()],
            statements: vec![
                TypedStatement::Definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    TypedExpression::Uint(2u32.into()),
                ),
                TypedStatement::Definition(
                    Variable::uint(Identifier::from("n").version(1), UBitwidth::B32).into(),
                    TypedExpression::Uint(2u32.into()),
                ),
                TypedStatement::Definition(
                    Variable::array("b", Type::FieldElement, 1u32.into()).into(),
                    ArrayExpressionInner::Value(vec![
                        FieldElementExpression::Number(1.into()).into()
                    ])
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
                ),
                TypedStatement::PushCallLog(
                    "main".into(),
                    DeclarationFunctionKey::with_id("foo").signature(foo_signature.clone()),
                    GenericsAssignment(vec![("K", 1)].into_iter().collect()),
                    vec![(
                        ConcreteVariable::array(
                            Identifier::from("a").version(1),
                            ConcreteType::FieldElement,
                            1,
                        )
                        .into(),
                        ArrayExpressionInner::Value(vec![
                            FieldElementExpression::Number(1.into()).into()
                        ])
                        .annotate(Type::FieldElement, 1u32)
                        .into(),
                    )],
                ),
                TypedStatement::Definition(
                    Variable::uint("K", UBitwidth::B32).into(),
                    UExpression::from(1u32).into(),
                ),
                TypedStatement::PopCallLog(vec![(
                    ConcreteVariable::array(
                        Identifier::from(CoreIdentifier::Call(0)).version(0),
                        ConcreteType::FieldElement,
                        1,
                    ),
                    ArrayExpressionInner::Identifier(Identifier::from("a").version(1))
                        .annotate(Type::FieldElement, 1u32)
                        .into(),
                )]),
                TypedStatement::Definition(
                    Variable::array(
                        Identifier::from("b").version(1),
                        Type::FieldElement,
                        1u32.into(),
                    )
                    .into(),
                    ArrayExpressionInner::Identifier(
                        Identifier::from(CoreIdentifier::Call(0)).version(0),
                    )
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
                ),
                TypedStatement::Definition(
                    Variable::uint(Identifier::from("n").version(2), UBitwidth::B32).into(),
                    TypedExpression::Uint(2u32.into()),
                ),
                TypedStatement::Return(vec![FieldElementExpression::Identifier("a".into()).into()]),
            ],
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        let expected = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![(
                        DeclarationFunctionKey::with_id("main").signature(
                            DeclarationSignature::new()
                                .inputs(vec![DeclarationType::FieldElement])
                                .outputs(vec![DeclarationType::FieldElement]),
                        ),
                        TypedFunctionSymbol::Here(expected_main),
                    )]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
        };

        assert_eq!(reduced.unwrap(), expected);
    }

    // #[test]
    // fn call_in_call() {
    //     // we use a global ssa counter, hence reusing variable names in called functions
    //     // leads to counter increase

    //     // def bar<K>(field[K] a) -> field[K]:
    //     //      return a

    //     // def foo<K>(field[K] a) -> field[K]:
    //     //      field[K] ret = bar([...a, 0])[0..K]
    //     //      return ret

    //     // def main():
    //     //      field[1] b = foo([1])
    //     //      return

    //     // expected:
    //     // def main():
    //     //      # PUSH CALL to foo::<1> with a_0 := [1]
    //     //      # PUSH CALL to bar::<2> with a_0 := [...a, 0]
    //     //      # POP CALL with field[1] ~bar_0 := a_0
    //     //      field[1] ret = ~bar_0[0..1]
    //     //      # POP CALL with field[1] b_0 := ret
    //     //      return

    //     let foo_signature = DeclarationSignature::new()
    //         .inputs(vec![DeclarationType::array(
    //             DeclarationType::FieldElement,
    //             Constant::Generic("K"),
    //         )])
    //         .outputs(vec![DeclarationType::array(
    //             DeclarationType::FieldElement,
    //             Constant::Generic("K"),
    //         )]);

    //     let foo: TypedFunction<Bn128Field> = TypedFunction {
    //         generics: vec!["K".into()],
    //         arguments: vec![DeclarationVariable::array(
    //             "a",
    //             DeclarationType::FieldElement,
    //             "K".into(),
    //         )
    //         .into()],
    //         statements: vec![TypedStatement::Return(vec![
    //             ArrayExpressionInner::Identifier("a".into())
    //                 .annotate(
    //                     Type::FieldElement,
    //                     UExpressionInner::Identifier("K".into()).annotate(UBitwidth::B32),
    //                 )
    //                 .into(),
    //         ])],
    //         signature: foo_signature.clone(),
    //     };

    //     let bar_signature = DeclarationSignature::new()
    //         .inputs(vec![DeclarationType::array(
    //             DeclarationType::FieldElement,
    //             Constant::Generic("K"),
    //         )])
    //         .outputs(vec![DeclarationType::array(
    //             DeclarationType::FieldElement,
    //             Constant::Generic("K"),
    //         )]);

    //     let bar: TypedFunction<Bn128Field> = TypedFunction {
    //         generics: vec!["K".into()],
    //         arguments: vec![DeclarationVariable::array(
    //             "a",
    //             DeclarationType::FieldElement,
    //             "K".into(),
    //         )
    //         .into()],
    //         statements: vec![TypedStatement::Return(vec![
    //             ArrayExpressionInner::Identifier("a".into())
    //                 .annotate(
    //                     Type::FieldElement,
    //                     UExpressionInner::Identifier("K".into()).annotate(UBitwidth::B32),
    //                 )
    //                 .into(),
    //         ])],
    //         signature: foo_signature.clone(),
    //     };

    //     let main: TypedFunction<Bn128Field> = TypedFunction {
    //         generics: vec![],
    //         arguments: vec![DeclarationVariable::field_element("a").into()],
    //         statements: vec![
    //             TypedStatement::MultipleDefinition(
    //                 vec![Variable::array("b", Type::FieldElement, 1u32.into()).into()],
    //                 TypedExpressionList::FunctionCall(
    //                     DeclarationFunctionKey::with_id("foo").signature(foo_signature.clone()),
    //                     vec![ArrayExpressionInner::Identifier("b".into())
    //                         .annotate(Type::FieldElement, 1u32)
    //                         .into()],
    //                     vec![Type::array(Type::FieldElement, 1u32)],
    //                 ),
    //             ),
    //             TypedStatement::Return(vec![]),
    //         ],
    //         signature: DeclarationSignature::new(),
    //     };

    //     let p = TypedProgram {
    //         main: "main".into(),
    //         modules: vec![(
    //             "main".into(),
    //             TypedModule {
    //                 functions: vec![
    //                     (
    //                         DeclarationFunctionKey::with_id("foo").signature(foo_signature.clone()),
    //                         TypedFunctionSymbol::Here(foo),
    //                     ),
    //                     (
    //                         DeclarationFunctionKey::with_id("main"),
    //                         TypedFunctionSymbol::Here(main),
    //                     ),
    //                 ]
    //                 .into_iter()
    //                 .collect(),
    //             },
    //         )]
    //         .into_iter()
    //         .collect(),
    //     };

    //     let reduced = reduce_program(p);

    //     let expected_main = TypedFunction {
    //         generics: vec![],
    //         arguments: vec![DeclarationVariable::field_element("a").into()],
    //         statements: vec![
    //             TypedStatement::Definition(
    //                 Variable::uint("n", UBitwidth::B32).into(),
    //                 TypedExpression::Uint(42u32.into()),
    //             ),
    //             TypedStatement::Definition(
    //                 Variable::uint(Identifier::from("n").version(1), UBitwidth::B32).into(),
    //                 UExpressionInner::Identifier("n".into())
    //                     .annotate(UBitwidth::B32)
    //                     .into(),
    //             ),
    //             TypedStatement::Definition(
    //                 Variable::array("b", Type::FieldElement, 1u32.into()).into(),
    //                 ArrayExpressionInner::Value(vec![
    //                     FieldElementExpression::Number(1.into()).into()
    //                 ])
    //                 .annotate(Type::FieldElement, 1u32)
    //                 .into(),
    //             ),
    //             TypedStatement::PushCallLog(
    //                 "main".into(),
    //                 DeclarationFunctionKey::with_id("foo").signature(foo_signature.clone()),
    //                 GenericsAssignment(vec![("K", 1)].into_iter().collect()),
    //                 vec![(
    //                     ConcreteVariable::array("a", ConcreteType::FieldElement, 1).into(),
    //                     ArrayExpressionInner::Identifier("b".into())
    //                         .annotate(Type::FieldElement, 1u32)
    //                         .into(),
    //                 )],
    //             ),
    //             TypedStatement::Definition(
    //                 Variable::uint("K", UBitwidth::B32).into(),
    //                 UExpression::from(1u32).into(),
    //             ),
    //             TypedStatement::PopCallLog(vec![(
    //                 ConcreteVariable::array(
    //                     Identifier::from("b").version(1),
    //                     ConcreteType::FieldElement,
    //                     1,
    //                 ),
    //                 ArrayExpressionInner::Identifier("a".into())
    //                     .annotate(Type::FieldElement, 1u32)
    //                     .into(),
    //             )]),
    //             TypedStatement::Definition(
    //                 Variable::uint(Identifier::from("n").version(2), UBitwidth::B32).into(),
    //                 UExpressionInner::Identifier(Identifier::from("n").version(1))
    //                     .annotate(UBitwidth::B32)
    //                     .into(),
    //             ),
    //             TypedStatement::Return(vec![FieldElementExpression::Identifier("a".into()).into()]),
    //         ],
    //         signature: DeclarationSignature::new()
    //             .inputs(vec![DeclarationType::FieldElement])
    //             .outputs(vec![DeclarationType::FieldElement]),
    //     };

    //     let expected = TypedProgram {
    //         main: "main".into(),
    //         modules: vec![(
    //             "main".into(),
    //             TypedModule {
    //                 functions: vec![(
    //                     DeclarationFunctionKey::with_id("main").signature(
    //                         DeclarationSignature::new()
    //                             .inputs(vec![DeclarationType::FieldElement])
    //                             .outputs(vec![DeclarationType::FieldElement]),
    //                     ),
    //                     TypedFunctionSymbol::Here(expected_main),
    //                 )]
    //                 .into_iter()
    //                 .collect(),
    //             },
    //         )]
    //         .into_iter()
    //         .collect(),
    //     };

    //     println!("{}", reduced.clone().unwrap());
    //     println!("{}", expected);

    //     assert_eq!(reduced.unwrap(), expected);
    // }

    #[test]
    fn incompatible() {
        // def foo<K>(field[K] a) -> field[K]:
        //      return a
        // def main():
        //      field[1] b = foo([])
        //      return

        // expected:
        // Error: Incompatible

        let foo_signature = DeclarationSignature::new()
            .inputs(vec![DeclarationType::array(
                DeclarationType::FieldElement,
                Constant::Generic("K"),
            )])
            .outputs(vec![DeclarationType::array(
                DeclarationType::FieldElement,
                Constant::Generic("K"),
            )]);

        let foo: TypedFunction<Bn128Field> = TypedFunction {
            generics: vec!["K".into()],
            arguments: vec![DeclarationVariable::array(
                "a",
                DeclarationType::FieldElement,
                "K".into(),
            )
            .into()],
            statements: vec![TypedStatement::Return(vec![
                ArrayExpressionInner::Identifier("a".into())
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
            ])],
            signature: foo_signature.clone(),
        };

        let main: TypedFunction<Bn128Field> = TypedFunction {
            generics: vec![],
            arguments: vec![],
            statements: vec![
                TypedStatement::MultipleDefinition(
                    vec![Variable::array("b", Type::FieldElement, 1u32.into()).into()],
                    TypedExpressionList::FunctionCall(
                        DeclarationFunctionKey::with_id("foo").signature(foo_signature.clone()),
                        vec![ArrayExpressionInner::Value(vec![])
                            .annotate(Type::FieldElement, 0u32)
                            .into()],
                        vec![Type::array(Type::FieldElement, 1u32)],
                    ),
                ),
                TypedStatement::Return(vec![]),
            ],
            signature: DeclarationSignature::new().inputs(vec![]).outputs(vec![]),
        };

        let p = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![
                        (
                            DeclarationFunctionKey::with_id("foo").signature(foo_signature.clone()),
                            TypedFunctionSymbol::Here(foo),
                        ),
                        (
                            DeclarationFunctionKey::with_id("main").signature(
                                DeclarationSignature::new().inputs(vec![]).outputs(vec![]),
                            ),
                            TypedFunctionSymbol::Here(main),
                        ),
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
        };

        let reduced = reduce_program(p);

        assert_eq!(reduced, Err(Error::Incompatible));
    }
}
