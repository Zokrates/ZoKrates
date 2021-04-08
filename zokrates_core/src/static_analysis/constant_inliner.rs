use crate::typed_absy::folder::*;
use crate::typed_absy::*;
use std::convert::TryInto;
use zokrates_field::Field;

pub struct ConstantInliner<'ast, T: Field> {
    modules: TypedModules<'ast, T>,
    location: OwnedTypedModuleId,
}

impl<'ast, T: Field> ConstantInliner<'ast, T> {
    fn with_modules_and_location(
        modules: TypedModules<'ast, T>,
        location: OwnedTypedModuleId,
    ) -> Self {
        ConstantInliner { modules, location }
    }

    pub fn inline(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        // initialize an inliner over all modules, starting from the main module
        let mut inliner =
            ConstantInliner::with_modules_and_location(p.modules.clone(), p.main.clone());

        inliner.fold_program(p)
    }

    pub fn module(&self) -> &TypedModule<'ast, T> {
        self.modules.get(&self.location).unwrap()
    }

    pub fn change_location(&mut self, location: OwnedTypedModuleId) -> OwnedTypedModuleId {
        let prev = self.location.clone();
        self.location = location;
        prev
    }

    pub fn get_constant(&mut self, id: &Identifier) -> Option<TypedConstant<'ast, T>> {
        self.modules
            .get(&self.location)
            .unwrap()
            .constants
            .as_ref()
            .and_then(|c| c.get(id.clone().try_into().unwrap()))
            .cloned()
            .and_then(|tc| {
                let symbol = self.fold_constant_symbol(tc);
                match symbol {
                    TypedConstantSymbol::Here(tc) => Some(tc),
                    _ => None,
                }
            })
    }
}

impl<'ast, T: Field> Folder<'ast, T> for ConstantInliner<'ast, T> {
    fn fold_program(&mut self, p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        TypedProgram {
            modules: p
                .modules
                .into_iter()
                .map(|(module_id, module)| {
                    self.change_location(module_id.clone());
                    (module_id, self.fold_module(module))
                })
                .collect(),
            main: p.main,
        }
    }

    fn fold_constant_symbol(
        &mut self,
        p: TypedConstantSymbol<'ast, T>,
    ) -> TypedConstantSymbol<'ast, T> {
        match p {
            TypedConstantSymbol::There(module_id, id) => {
                let location = self.change_location(module_id);
                let symbol = self
                    .module()
                    .constants
                    .as_ref()
                    .and_then(|c| c.get(id))
                    .unwrap()
                    .to_owned();

                let symbol = self.fold_constant_symbol(symbol);
                let _ = self.change_location(location);
                symbol
            }
            _ => fold_constant_symbol(self, p),
        }
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> FieldElementExpression<'ast, T> {
        match e {
            FieldElementExpression::Identifier(ref id) => match self.get_constant(id) {
                Some(c) => fold_field_expression(self, c.expression.try_into().unwrap()),
                None => fold_field_expression(self, e),
            },
            e => fold_field_expression(self, e),
        }
    }

    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> BooleanExpression<'ast, T> {
        match e {
            BooleanExpression::Identifier(ref id) => match self.get_constant(id) {
                Some(c) => fold_boolean_expression(self, c.expression.try_into().unwrap()),
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
            UExpressionInner::Identifier(ref id) => match self.get_constant(id) {
                Some(c) => {
                    fold_uint_expression(self, c.expression.try_into().unwrap()).into_inner()
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
            ArrayExpressionInner::Identifier(ref id) => match self.get_constant(id) {
                Some(c) => {
                    fold_array_expression(self, c.expression.try_into().unwrap()).into_inner()
                }
                None => fold_array_expression_inner(self, ty, e),
            },
            e => fold_array_expression_inner(self, ty, e),
        }
    }

    fn fold_struct_expression_inner(
        &mut self,
        ty: &StructType<'ast, T>,
        e: StructExpressionInner<'ast, T>,
    ) -> StructExpressionInner<'ast, T> {
        match e {
            StructExpressionInner::Identifier(ref id) => match self.get_constant(id) {
                Some(c) => {
                    fold_struct_expression(self, c.expression.try_into().unwrap()).into_inner()
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
        DeclarationFunctionKey, DeclarationType, FieldElementExpression, GType, Identifier,
        TypedConstant, TypedExpression, TypedFunction, TypedFunctionSymbol, TypedStatement,
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
            const_id,
            TypedConstantSymbol::Here(TypedConstant {
                id: Identifier::from(const_id),
                ty: GType::FieldElement,
                expression: (TypedExpression::FieldElement(FieldElementExpression::Number(
                    Bn128Field::from(1),
                ))),
            }),
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
                    constants: Some(constants.clone()),
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
                    constants: Some(constants),
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
            const_id,
            TypedConstantSymbol::Here(TypedConstant {
                id: Identifier::from(const_id),
                ty: GType::Boolean,
                expression: (TypedExpression::Boolean(BooleanExpression::Value(true))),
            }),
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
                    constants: Some(constants.clone()),
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
                    constants: Some(constants),
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
            const_id,
            TypedConstantSymbol::Here(TypedConstant {
                id: Identifier::from(const_id),
                ty: GType::Uint(UBitwidth::B32),
                expression: (UExpressionInner::Value(1u128)
                    .annotate(UBitwidth::B32)
                    .into()),
            }),
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
                    constants: Some(constants.clone()),
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
                    constants: Some(constants),
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
                FieldElementExpression::Select(
                    box ArrayExpressionInner::Identifier(Identifier::from(const_id))
                        .annotate(GType::FieldElement, 2usize),
                    box UExpressionInner::Value(0u128).annotate(UBitwidth::B32),
                )
                .into(),
                FieldElementExpression::Select(
                    box ArrayExpressionInner::Identifier(Identifier::from(const_id))
                        .annotate(GType::FieldElement, 2usize),
                    box UExpressionInner::Value(1u128).annotate(UBitwidth::B32),
                )
                .into(),
            )
            .into()])],
            signature: DeclarationSignature::new()
                .inputs(vec![])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        let constants: TypedConstantSymbols<_> = vec![(
            const_id,
            TypedConstantSymbol::Here(TypedConstant {
                id: Identifier::from(const_id),
                ty: GType::FieldElement,
                expression: TypedExpression::Array(
                    ArrayExpressionInner::Value(
                        vec![
                            FieldElementExpression::Number(Bn128Field::from(2)).into(),
                            FieldElementExpression::Number(Bn128Field::from(2)).into(),
                        ]
                        .into(),
                    )
                    .annotate(GType::FieldElement, 2usize),
                ),
            }),
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
                    constants: Some(constants.clone()),
                },
            )]
            .into_iter()
            .collect(),
        };

        let program = ConstantInliner::inline(program);

        let expected_main = TypedFunction {
            arguments: vec![],
            statements: vec![TypedStatement::Return(vec![FieldElementExpression::Add(
                FieldElementExpression::Select(
                    box ArrayExpressionInner::Value(
                        vec![
                            FieldElementExpression::Number(Bn128Field::from(2)).into(),
                            FieldElementExpression::Number(Bn128Field::from(2)).into(),
                        ]
                        .into(),
                    )
                    .annotate(GType::FieldElement, 2usize),
                    box UExpressionInner::Value(0u128).annotate(UBitwidth::B32),
                )
                .into(),
                FieldElementExpression::Select(
                    box ArrayExpressionInner::Value(
                        vec![
                            FieldElementExpression::Number(Bn128Field::from(2)).into(),
                            FieldElementExpression::Number(Bn128Field::from(2)).into(),
                        ]
                        .into(),
                    )
                    .annotate(GType::FieldElement, 2usize),
                    box UExpressionInner::Value(1u128).annotate(UBitwidth::B32),
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
                    constants: Some(constants),
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
                    constants: Some(
                        vec![
                            (
                                const_a_id,
                                TypedConstantSymbol::Here(TypedConstant {
                                    id: Identifier::from(const_a_id),
                                    ty: GType::FieldElement,
                                    expression: (TypedExpression::FieldElement(
                                        FieldElementExpression::Number(Bn128Field::from(1)),
                                    )),
                                }),
                            ),
                            (
                                const_b_id,
                                TypedConstantSymbol::Here(TypedConstant {
                                    id: Identifier::from(const_b_id),
                                    ty: GType::FieldElement,
                                    expression: (TypedExpression::FieldElement(
                                        FieldElementExpression::Add(
                                            box FieldElementExpression::Identifier(
                                                Identifier::from(const_a_id),
                                            ),
                                            box FieldElementExpression::Number(Bn128Field::from(1)),
                                        ),
                                    )),
                                }),
                            ),
                        ]
                        .into_iter()
                        .collect(),
                    ),
                },
            )]
            .into_iter()
            .collect(),
        };

        let program = ConstantInliner::inline(program);

        let expected_main = TypedFunction {
            arguments: vec![],
            statements: vec![TypedStatement::Return(vec![FieldElementExpression::Add(
                box FieldElementExpression::Number(Bn128Field::from(1)),
                box FieldElementExpression::Number(Bn128Field::from(1)),
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
                    constants: Some(
                        vec![
                            (
                                const_a_id,
                                TypedConstantSymbol::Here(TypedConstant {
                                    id: Identifier::from(const_a_id),
                                    ty: GType::FieldElement,
                                    expression: (TypedExpression::FieldElement(
                                        FieldElementExpression::Number(Bn128Field::from(1)),
                                    )),
                                }),
                            ),
                            (
                                const_b_id,
                                TypedConstantSymbol::Here(TypedConstant {
                                    id: Identifier::from(const_b_id),
                                    ty: GType::FieldElement,
                                    expression: (TypedExpression::FieldElement(
                                        FieldElementExpression::Add(
                                            box FieldElementExpression::Number(Bn128Field::from(1)),
                                            box FieldElementExpression::Number(Bn128Field::from(1)),
                                        ),
                                    )),
                                }),
                            ),
                        ]
                        .into_iter()
                        .collect(),
                    ),
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
            constants: Some(
                vec![(
                    foo_const_id,
                    TypedConstantSymbol::Here(TypedConstant {
                        id: Identifier::from(foo_const_id),
                        ty: GType::FieldElement,
                        expression: (TypedExpression::FieldElement(
                            FieldElementExpression::Number(Bn128Field::from(42)),
                        )),
                    }),
                )]
                .into_iter()
                .collect(),
            ),
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
            constants: Some(
                vec![(
                    foo_const_id,
                    TypedConstantSymbol::There(OwnedTypedModuleId::from("foo"), foo_const_id),
                )]
                .into_iter()
                .collect(),
            ),
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
            constants: Some(
                vec![(
                    foo_const_id,
                    TypedConstantSymbol::Here(TypedConstant {
                        id: Identifier::from(foo_const_id),
                        ty: GType::FieldElement,
                        expression: (TypedExpression::FieldElement(
                            FieldElementExpression::Number(Bn128Field::from(42)),
                        )),
                    }),
                )]
                .into_iter()
                .collect(),
            ),
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
