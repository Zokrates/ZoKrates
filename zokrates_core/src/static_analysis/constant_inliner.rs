use crate::static_analysis::Propagator;
use crate::typed_absy::folder::*;
use crate::typed_absy::result_folder::ResultFolder;
use crate::typed_absy::types::DeclarationConstant;
use crate::typed_absy::*;
use std::collections::HashMap;
use std::convert::TryInto;
use zokrates_field::Field;

type ProgramConstants<'ast, T> =
    HashMap<OwnedTypedModuleId, HashMap<Identifier<'ast>, TypedExpression<'ast, T>>>;

pub struct ConstantInliner<'ast, T> {
    modules: TypedModules<'ast, T>,
    location: OwnedTypedModuleId,
    constants: ProgramConstants<'ast, T>,
}

impl<'ast, 'a, T: Field> ConstantInliner<'ast, T> {
    pub fn new(
        modules: TypedModules<'ast, T>,
        location: OwnedTypedModuleId,
        constants: ProgramConstants<'ast, T>,
    ) -> Self {
        ConstantInliner {
            modules,
            location,
            constants,
        }
    }
    pub fn inline(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        let constants = ProgramConstants::new();
        let mut inliner = ConstantInliner::new(p.modules.clone(), p.main.clone(), constants);
        inliner.fold_program(p)
    }

    fn change_location(&mut self, location: OwnedTypedModuleId) -> OwnedTypedModuleId {
        let prev = self.location.clone();
        self.location = location;
        self.constants.entry(self.location.clone()).or_default();
        prev
    }

    fn treated(&self, id: &TypedModuleId) -> bool {
        self.constants.contains_key(id)
    }

    fn get_constant(
        &self,
        id: &CanonicalConstantIdentifier<'ast>,
    ) -> Option<TypedExpression<'ast, T>> {
        self.constants
            .get(&id.module)
            .and_then(|constants| constants.get(&id.id.into()))
            .cloned()
    }

    fn get_constant_for_identifier(
        &self,
        id: &Identifier<'ast>,
    ) -> Option<TypedExpression<'ast, T>> {
        self.constants
            .get(&self.location)
            .and_then(|constants| constants.get(&id))
            .cloned()
    }
}

impl<'ast, T: Field> Folder<'ast, T> for ConstantInliner<'ast, T> {
    fn fold_module_id(&mut self, id: OwnedTypedModuleId) -> OwnedTypedModuleId {
        // anytime we encounter a module id, visit the corresponding module if it hasn't been done yet
        if !self.treated(&id) {
            let current_m_id = self.change_location(id.clone());
            let m = self.modules.remove(&id).unwrap();
            let m = self.fold_module(m);
            self.modules.insert(id.clone(), m);
            self.change_location(current_m_id);
        }
        id
    }

    fn fold_module(&mut self, m: TypedModule<'ast, T>) -> TypedModule<'ast, T> {
        TypedModule {
            constants: m
                .constants
                .into_iter()
                .map(|(id, tc)| {
                    let constant = match tc {
                        TypedConstantSymbol::There(imported_id) => {
                            // visit the imported symbol. This triggers visiting the corresponding module if needed
                            let imported_id = self.fold_canonical_constant_identifier(imported_id);
                            // after that, the constant must have been defined defined in the global map. It is already reduced
                            // to a literal, so running propagation isn't required
                            self.get_constant(&imported_id).unwrap()
                        }
                        TypedConstantSymbol::Here(c) => {
                            let non_propagated_constant = fold_constant(self, c).expression;
                            // folding the constant above only reduces it to an expression containing only literals, not to a single literal.
                            // propagating with an empty map of constants reduces it to a single literal
                            Propagator::with_constants(&mut HashMap::default())
                                .fold_expression(non_propagated_constant)
                                .unwrap()
                        }
                    };

                    // add to the constant map. The value added is always a single litteral
                    self.constants
                        .get_mut(&self.location)
                        .unwrap()
                        .insert(id.id.into(), constant.clone());

                    (
                        id,
                        TypedConstantSymbol::Here(TypedConstant {
                            expression: constant,
                        }),
                    )
                })
                .collect(),
            functions: m
                .functions
                .into_iter()
                .map(|(key, fun)| {
                    (
                        self.fold_declaration_function_key(key),
                        self.fold_function_symbol(fun),
                    )
                })
                .collect(),
        }
    }

    fn fold_declaration_constant(
        &mut self,
        c: DeclarationConstant<'ast>,
    ) -> DeclarationConstant<'ast> {
        match c {
            // replace constants by their concrete value in declaration types
            DeclarationConstant::Constant(id) => {
                let id = CanonicalConstantIdentifier {
                    module: self.fold_module_id(id.module),
                    ..id
                };

                DeclarationConstant::Concrete(match self.get_constant(&id).unwrap() {
                    TypedExpression::Uint(UExpression {
                        inner: UExpressionInner::Value(v),
                        ..
                    }) => v as u32,
                    _ => unreachable!("all constants found in declaration types should be reduceable to u32 literals"),
                })
            }
            c => c,
        }
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> FieldElementExpression<'ast, T> {
        match e {
            FieldElementExpression::Identifier(ref id) => {
                match self.get_constant_for_identifier(id) {
                    Some(c) => c.try_into().unwrap(),
                    None => fold_field_expression(self, e),
                }
            }
            e => fold_field_expression(self, e),
        }
    }

    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> BooleanExpression<'ast, T> {
        match e {
            BooleanExpression::Identifier(ref id) => match self.get_constant_for_identifier(id) {
                Some(c) => c.try_into().unwrap(),
                None => fold_boolean_expression(self, e),
            },
            e => fold_boolean_expression(self, e),
        }
    }

    fn fold_uint_expression_inner(
        &mut self,
        size: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> UExpressionInner<'ast, T> {
        match e {
            UExpressionInner::Identifier(ref id) => match self.get_constant_for_identifier(id) {
                Some(c) => {
                    let e: UExpression<'ast, T> = c.try_into().unwrap();
                    e.into_inner()
                }
                None => fold_uint_expression_inner(self, size, e),
            },
            e => fold_uint_expression_inner(self, size, e),
        }
    }

    fn fold_array_expression_inner(
        &mut self,
        ty: &ArrayType<'ast, T>,
        e: ArrayExpressionInner<'ast, T>,
    ) -> ArrayExpressionInner<'ast, T> {
        match e {
            ArrayExpressionInner::Identifier(ref id) => {
                match self.get_constant_for_identifier(id) {
                    Some(c) => {
                        let e: ArrayExpression<'ast, T> = c.try_into().unwrap();
                        e.into_inner()
                    }
                    None => fold_array_expression_inner(self, ty, e),
                }
            }
            e => fold_array_expression_inner(self, ty, e),
        }
    }

    fn fold_struct_expression_inner(
        &mut self,
        ty: &StructType<'ast, T>,
        e: StructExpressionInner<'ast, T>,
    ) -> StructExpressionInner<'ast, T> {
        match e {
            StructExpressionInner::Identifier(ref id) => match self.get_constant_for_identifier(id)
            {
                Some(c) => {
                    let e: StructExpression<'ast, T> = c.try_into().unwrap();
                    e.into_inner()
                }
                None => fold_struct_expression_inner(self, ty, e),
            },
            e => fold_struct_expression_inner(self, ty, e),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typed_absy::types::DeclarationSignature;
    use crate::typed_absy::{
        DeclarationArrayType, DeclarationFunctionKey, DeclarationType, FieldElementExpression,
        GType, Identifier, TypedConstant, TypedExpression, TypedFunction, TypedFunctionSymbol,
        TypedStatement,
    };
    use zokrates_field::Bn128Field;

    #[test]
    fn inline_const_field() {
        // const field a = 1
        //
        // def main() -> field:
        //      return a

        let const_id = "a";
        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![],
            statements: vec![TypedStatement::Return(vec![
                FieldElementExpression::Identifier(Identifier::from(const_id)).into(),
            ])],
            signature: DeclarationSignature::new()
                .inputs(vec![])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        let constants: TypedConstantSymbols<_> = vec![(
            CanonicalConstantIdentifier::new(
                const_id,
                "main".into(),
                DeclarationType::FieldElement,
            ),
            TypedConstantSymbol::Here(TypedConstant::new(TypedExpression::FieldElement(
                FieldElementExpression::Number(Bn128Field::from(1)),
            ))),
        )]
        .into_iter()
        .collect();

        let program = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![(
                        DeclarationFunctionKey::with_location("main", "main").signature(
                            DeclarationSignature::new()
                                .inputs(vec![])
                                .outputs(vec![DeclarationType::FieldElement]),
                        ),
                        TypedFunctionSymbol::Here(main),
                    )]
                    .into_iter()
                    .collect(),
                    constants: constants.clone(),
                },
            )]
            .into_iter()
            .collect(),
        };

        let program = ConstantInliner::inline(program);

        let expected_main = TypedFunction {
            arguments: vec![],
            statements: vec![TypedStatement::Return(vec![
                FieldElementExpression::Number(Bn128Field::from(1)).into(),
            ])],
            signature: DeclarationSignature::new()
                .inputs(vec![])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        let expected_program: TypedProgram<Bn128Field> = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![(
                        DeclarationFunctionKey::with_location("main", "main").signature(
                            DeclarationSignature::new()
                                .inputs(vec![])
                                .outputs(vec![DeclarationType::FieldElement]),
                        ),
                        TypedFunctionSymbol::Here(expected_main),
                    )]
                    .into_iter()
                    .collect(),
                    constants,
                },
            )]
            .into_iter()
            .collect(),
        };

        assert_eq!(program, expected_program)
    }

    #[test]
    fn inline_const_boolean() {
        // const bool a = true
        //
        // def main() -> bool:
        //      return a

        let const_id = "a";
        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![],
            statements: vec![TypedStatement::Return(vec![BooleanExpression::Identifier(
                Identifier::from(const_id),
            )
            .into()])],
            signature: DeclarationSignature::new()
                .inputs(vec![])
                .outputs(vec![DeclarationType::Boolean]),
        };

        let constants: TypedConstantSymbols<_> = vec![(
            CanonicalConstantIdentifier::new(const_id, "main".into(), DeclarationType::Boolean),
            TypedConstantSymbol::Here(TypedConstant::new(TypedExpression::Boolean(
                BooleanExpression::Value(true),
            ))),
        )]
        .into_iter()
        .collect();

        let program = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![(
                        DeclarationFunctionKey::with_location("main", "main").signature(
                            DeclarationSignature::new()
                                .inputs(vec![])
                                .outputs(vec![DeclarationType::Boolean]),
                        ),
                        TypedFunctionSymbol::Here(main),
                    )]
                    .into_iter()
                    .collect(),
                    constants: constants.clone(),
                },
            )]
            .into_iter()
            .collect(),
        };

        let program = ConstantInliner::inline(program);

        let expected_main = TypedFunction {
            arguments: vec![],
            statements: vec![TypedStatement::Return(vec![
                BooleanExpression::Value(true).into()
            ])],
            signature: DeclarationSignature::new()
                .inputs(vec![])
                .outputs(vec![DeclarationType::Boolean]),
        };

        let expected_program: TypedProgram<Bn128Field> = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![(
                        DeclarationFunctionKey::with_location("main", "main").signature(
                            DeclarationSignature::new()
                                .inputs(vec![])
                                .outputs(vec![DeclarationType::Boolean]),
                        ),
                        TypedFunctionSymbol::Here(expected_main),
                    )]
                    .into_iter()
                    .collect(),
                    constants,
                },
            )]
            .into_iter()
            .collect(),
        };

        assert_eq!(program, expected_program)
    }

    #[test]
    fn inline_const_uint() {
        // const u32 a = 0x00000001
        //
        // def main() -> u32:
        //      return a

        let const_id = "a";
        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![],
            statements: vec![TypedStatement::Return(vec![UExpressionInner::Identifier(
                Identifier::from(const_id),
            )
            .annotate(UBitwidth::B32)
            .into()])],
            signature: DeclarationSignature::new()
                .inputs(vec![])
                .outputs(vec![DeclarationType::Uint(UBitwidth::B32)]),
        };

        let constants: TypedConstantSymbols<_> = vec![(
            CanonicalConstantIdentifier::new(
                const_id,
                "main".into(),
                DeclarationType::Uint(UBitwidth::B32),
            ),
            TypedConstantSymbol::Here(TypedConstant::new(
                UExpressionInner::Value(1u128)
                    .annotate(UBitwidth::B32)
                    .into(),
            )),
        )]
        .into_iter()
        .collect();

        let program = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![(
                        DeclarationFunctionKey::with_location("main", "main").signature(
                            DeclarationSignature::new()
                                .inputs(vec![])
                                .outputs(vec![DeclarationType::Uint(UBitwidth::B32)]),
                        ),
                        TypedFunctionSymbol::Here(main),
                    )]
                    .into_iter()
                    .collect(),
                    constants: constants.clone(),
                },
            )]
            .into_iter()
            .collect(),
        };

        let program = ConstantInliner::inline(program);

        let expected_main = TypedFunction {
            arguments: vec![],
            statements: vec![TypedStatement::Return(vec![UExpressionInner::Value(1u128)
                .annotate(UBitwidth::B32)
                .into()])],
            signature: DeclarationSignature::new()
                .inputs(vec![])
                .outputs(vec![DeclarationType::Uint(UBitwidth::B32)]),
        };

        let expected_program: TypedProgram<Bn128Field> = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![(
                        DeclarationFunctionKey::with_location("main", "main").signature(
                            DeclarationSignature::new()
                                .inputs(vec![])
                                .outputs(vec![DeclarationType::Uint(UBitwidth::B32)]),
                        ),
                        TypedFunctionSymbol::Here(expected_main),
                    )]
                    .into_iter()
                    .collect(),
                    constants,
                },
            )]
            .into_iter()
            .collect(),
        };

        assert_eq!(program, expected_program)
    }

    #[test]
    fn inline_const_field_array() {
        // const field[2] a = [2, 2]
        //
        // def main() -> field:
        //      return a[0] + a[1]

        let const_id = "a";
        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![],
            statements: vec![TypedStatement::Return(vec![FieldElementExpression::Add(
                FieldElementExpression::select(
                    ArrayExpressionInner::Identifier(Identifier::from(const_id))
                        .annotate(GType::FieldElement, 2usize),
                    UExpressionInner::Value(0u128).annotate(UBitwidth::B32),
                )
                .into(),
                FieldElementExpression::select(
                    ArrayExpressionInner::Identifier(Identifier::from(const_id))
                        .annotate(GType::FieldElement, 2usize),
                    UExpressionInner::Value(1u128).annotate(UBitwidth::B32),
                )
                .into(),
            )
            .into()])],
            signature: DeclarationSignature::new()
                .inputs(vec![])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        let constants: TypedConstantSymbols<_> = vec![(
            CanonicalConstantIdentifier::new(
                const_id,
                "main".into(),
                DeclarationType::Array(DeclarationArrayType::new(
                    DeclarationType::FieldElement,
                    2u32,
                )),
            ),
            TypedConstantSymbol::Here(TypedConstant::new(TypedExpression::Array(
                ArrayExpressionInner::Value(
                    vec![
                        FieldElementExpression::Number(Bn128Field::from(2)).into(),
                        FieldElementExpression::Number(Bn128Field::from(2)).into(),
                    ]
                    .into(),
                )
                .annotate(GType::FieldElement, 2usize),
            ))),
        )]
        .into_iter()
        .collect();

        let program = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![(
                        DeclarationFunctionKey::with_location("main", "main").signature(
                            DeclarationSignature::new()
                                .inputs(vec![])
                                .outputs(vec![DeclarationType::FieldElement]),
                        ),
                        TypedFunctionSymbol::Here(main),
                    )]
                    .into_iter()
                    .collect(),
                    constants: constants.clone(),
                },
            )]
            .into_iter()
            .collect(),
        };

        let program = ConstantInliner::inline(program);

        let expected_main = TypedFunction {
            arguments: vec![],
            statements: vec![TypedStatement::Return(vec![FieldElementExpression::Add(
                FieldElementExpression::select(
                    ArrayExpressionInner::Value(
                        vec![
                            FieldElementExpression::Number(Bn128Field::from(2)).into(),
                            FieldElementExpression::Number(Bn128Field::from(2)).into(),
                        ]
                        .into(),
                    )
                    .annotate(GType::FieldElement, 2usize),
                    UExpressionInner::Value(0u128).annotate(UBitwidth::B32),
                )
                .into(),
                FieldElementExpression::select(
                    ArrayExpressionInner::Value(
                        vec![
                            FieldElementExpression::Number(Bn128Field::from(2)).into(),
                            FieldElementExpression::Number(Bn128Field::from(2)).into(),
                        ]
                        .into(),
                    )
                    .annotate(GType::FieldElement, 2usize),
                    UExpressionInner::Value(1u128).annotate(UBitwidth::B32),
                )
                .into(),
            )
            .into()])],
            signature: DeclarationSignature::new()
                .inputs(vec![])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        let expected_program: TypedProgram<Bn128Field> = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![(
                        DeclarationFunctionKey::with_location("main", "main").signature(
                            DeclarationSignature::new()
                                .inputs(vec![])
                                .outputs(vec![DeclarationType::FieldElement]),
                        ),
                        TypedFunctionSymbol::Here(expected_main),
                    )]
                    .into_iter()
                    .collect(),
                    constants,
                },
            )]
            .into_iter()
            .collect(),
        };

        assert_eq!(program, expected_program)
    }

    #[test]
    fn inline_nested_const_field() {
        // const field a = 1
        // const field b = a + 1
        //
        // def main() -> field:
        //      return b

        let const_a_id = "a";
        let const_b_id = "b";

        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![],
            statements: vec![TypedStatement::Return(vec![
                FieldElementExpression::Identifier(Identifier::from(const_b_id)).into(),
            ])],
            signature: DeclarationSignature::new()
                .inputs(vec![])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        let program = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![(
                        DeclarationFunctionKey::with_location("main", "main").signature(
                            DeclarationSignature::new()
                                .inputs(vec![])
                                .outputs(vec![DeclarationType::FieldElement]),
                        ),
                        TypedFunctionSymbol::Here(main),
                    )]
                    .into_iter()
                    .collect(),
                    constants: vec![
                        (
                            CanonicalConstantIdentifier::new(
                                const_a_id,
                                "main".into(),
                                DeclarationType::FieldElement,
                            ),
                            TypedConstantSymbol::Here(TypedConstant::new(
                                TypedExpression::FieldElement(FieldElementExpression::Number(
                                    Bn128Field::from(1),
                                )),
                            )),
                        ),
                        (
                            CanonicalConstantIdentifier::new(
                                const_b_id,
                                "main".into(),
                                DeclarationType::FieldElement,
                            ),
                            TypedConstantSymbol::Here(TypedConstant::new(
                                TypedExpression::FieldElement(FieldElementExpression::Add(
                                    box FieldElementExpression::Identifier(Identifier::from(
                                        const_a_id,
                                    )),
                                    box FieldElementExpression::Number(Bn128Field::from(1)),
                                )),
                            )),
                        ),
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
        };

        let program = ConstantInliner::inline(program);

        let expected_main = TypedFunction {
            arguments: vec![],
            statements: vec![TypedStatement::Return(vec![
                FieldElementExpression::Number(Bn128Field::from(2)).into(),
            ])],
            signature: DeclarationSignature::new()
                .inputs(vec![])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        let expected_program: TypedProgram<Bn128Field> = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![(
                        DeclarationFunctionKey::with_location("main", "main").signature(
                            DeclarationSignature::new()
                                .inputs(vec![])
                                .outputs(vec![DeclarationType::FieldElement]),
                        ),
                        TypedFunctionSymbol::Here(expected_main),
                    )]
                    .into_iter()
                    .collect(),
                    constants: vec![
                        (
                            CanonicalConstantIdentifier::new(
                                const_a_id,
                                "main".into(),
                                DeclarationType::FieldElement,
                            ),
                            TypedConstantSymbol::Here(TypedConstant::new(
                                TypedExpression::FieldElement(FieldElementExpression::Number(
                                    Bn128Field::from(1),
                                )),
                            )),
                        ),
                        (
                            CanonicalConstantIdentifier::new(
                                const_b_id,
                                "main".into(),
                                DeclarationType::FieldElement,
                            ),
                            TypedConstantSymbol::Here(TypedConstant::new(
                                TypedExpression::FieldElement(FieldElementExpression::Number(
                                    Bn128Field::from(2),
                                )),
                            )),
                        ),
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
        };

        assert_eq!(program, expected_program)
    }

    #[test]
    fn inline_imported_constant() {
        // ---------------------
        // module `foo`
        // --------------------
        // const field FOO = 42
        //
        // def main():
        //     return
        //
        // ---------------------
        // module `main`
        // ---------------------
        // from "foo" import FOO
        //
        // def main() -> field:
        //     return FOO

        let foo_const_id = "FOO";
        let foo_module = TypedModule {
            functions: vec![(
                DeclarationFunctionKey::with_location("main", "main")
                    .signature(DeclarationSignature::new().inputs(vec![]).outputs(vec![])),
                TypedFunctionSymbol::Here(TypedFunction {
                    arguments: vec![],
                    statements: vec![],
                    signature: DeclarationSignature::new().inputs(vec![]).outputs(vec![]),
                }),
            )]
            .into_iter()
            .collect(),
            constants: vec![(
                CanonicalConstantIdentifier::new(
                    foo_const_id,
                    "foo".into(),
                    DeclarationType::FieldElement,
                ),
                TypedConstantSymbol::Here(TypedConstant::new(TypedExpression::FieldElement(
                    FieldElementExpression::Number(Bn128Field::from(42)),
                ))),
            )]
            .into_iter()
            .collect(),
        };

        let main_module = TypedModule {
            functions: vec![(
                DeclarationFunctionKey::with_location("main", "main").signature(
                    DeclarationSignature::new()
                        .inputs(vec![])
                        .outputs(vec![DeclarationType::FieldElement]),
                ),
                TypedFunctionSymbol::Here(TypedFunction {
                    arguments: vec![],
                    statements: vec![TypedStatement::Return(vec![
                        FieldElementExpression::Identifier(Identifier::from(foo_const_id)).into(),
                    ])],
                    signature: DeclarationSignature::new()
                        .inputs(vec![])
                        .outputs(vec![DeclarationType::FieldElement]),
                }),
            )]
            .into_iter()
            .collect(),
            constants: vec![(
                CanonicalConstantIdentifier::new(
                    foo_const_id,
                    "main".into(),
                    DeclarationType::FieldElement,
                ),
                TypedConstantSymbol::There(CanonicalConstantIdentifier::new(
                    foo_const_id,
                    "foo".into(),
                    DeclarationType::FieldElement,
                )),
            )]
            .into_iter()
            .collect(),
        };

        let program = TypedProgram {
            main: "main".into(),
            modules: vec![
                ("main".into(), main_module),
                ("foo".into(), foo_module.clone()),
            ]
            .into_iter()
            .collect(),
        };

        let program = ConstantInliner::inline(program);
        let expected_main_module = TypedModule {
            functions: vec![(
                DeclarationFunctionKey::with_location("main", "main").signature(
                    DeclarationSignature::new()
                        .inputs(vec![])
                        .outputs(vec![DeclarationType::FieldElement]),
                ),
                TypedFunctionSymbol::Here(TypedFunction {
                    arguments: vec![],
                    statements: vec![TypedStatement::Return(vec![
                        FieldElementExpression::Number(Bn128Field::from(42)).into(),
                    ])],
                    signature: DeclarationSignature::new()
                        .inputs(vec![])
                        .outputs(vec![DeclarationType::FieldElement]),
                }),
            )]
            .into_iter()
            .collect(),
            constants: vec![(
                CanonicalConstantIdentifier::new(
                    foo_const_id,
                    "main".into(),
                    DeclarationType::FieldElement,
                ),
                TypedConstantSymbol::Here(TypedConstant::new(TypedExpression::FieldElement(
                    FieldElementExpression::Number(Bn128Field::from(42)),
                ))),
            )]
            .into_iter()
            .collect(),
        };

        let expected_program: TypedProgram<Bn128Field> = TypedProgram {
            main: "main".into(),
            modules: vec![
                ("main".into(), expected_main_module),
                ("foo".into(), foo_module),
            ]
            .into_iter()
            .collect(),
        };

        assert_eq!(program, expected_program)
    }
}
