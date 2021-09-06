// Static analysis step to replace all imported constants with the imported value
// This does *not* reduce constants to their literal value
// This step cannot fail as the imports were checked during semantics

use crate::typed_absy::folder::*;
use crate::typed_absy::*;
use std::collections::HashMap;
use zokrates_field::Field;

// a map of the canonical constants in this program. with all imported constants reduced to their canonical value
type ProgramConstants<'ast, T> =
    HashMap<OwnedTypedModuleId, HashMap<ConstantIdentifier<'ast>, TypedConstant<'ast, T>>>;

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
    ) -> Option<TypedConstant<'ast, T>> {
        self.constants
            .get(&id.module)
            .and_then(|constants| constants.get(&id.id))
            .cloned()
    }
}

impl<'ast, T: Field> Folder<'ast, T> for ConstantInliner<'ast, T> {
    fn fold_program(&mut self, p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        self.fold_module_id(p.main.clone());

        TypedProgram {
            modules: std::mem::take(&mut self.modules),
            ..p
        }
    }

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
                    let id = self.fold_canonical_constant_identifier(id);

                    let constant = match tc {
                        TypedConstantSymbol::There(imported_id) => {
                            // visit the imported symbol. This triggers visiting the corresponding module if needed
                            let imported_id = self.fold_canonical_constant_identifier(imported_id);
                            // after that, the constant must have been defined defined in the global map
                            self.get_constant(&imported_id).unwrap()
                        }
                        TypedConstantSymbol::Here(c) => fold_constant(self, c),
                    };
                    self.constants
                        .get_mut(&self.location)
                        .unwrap()
                        .insert(id.id, constant.clone());

                    (id, TypedConstantSymbol::Here(constant))
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
            CanonicalConstantIdentifier::new(const_id, "main".into()),
            TypedConstantSymbol::Here(TypedConstant::new(
                TypedExpression::FieldElement(FieldElementExpression::Number(Bn128Field::from(1))),
                DeclarationType::FieldElement,
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

        let expected_program = program.clone();

        let program = ConstantInliner::inline(program);

        assert_eq!(program, expected_program)
    }

    #[test]
    fn inline_const_boolean() {
        // const bool a = true
        //
        // def main() -> bool:
        //      return main.zok/a

        let const_id = CanonicalConstantIdentifier::new("a", "main".into());
        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![],
            statements: vec![TypedStatement::Return(vec![BooleanExpression::Identifier(
                Identifier::from(const_id.clone()),
            )
            .into()])],
            signature: DeclarationSignature::new()
                .inputs(vec![])
                .outputs(vec![DeclarationType::Boolean]),
        };

        let constants: TypedConstantSymbols<_> = vec![(
            const_id,
            TypedConstantSymbol::Here(TypedConstant::new(
                TypedExpression::Boolean(BooleanExpression::Value(true)),
                DeclarationType::Boolean,
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

        let expected_program = program.clone();

        let program = ConstantInliner::inline(program);

        assert_eq!(program, expected_program)
    }

    #[test]
    fn inline_const_uint() {
        // const u32 a = 0x00000001
        //
        // def main() -> u32:
        //      return a

        let const_id = CanonicalConstantIdentifier::new("a", "main".into());
        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![],
            statements: vec![TypedStatement::Return(vec![UExpressionInner::Identifier(
                Identifier::from(const_id.clone()),
            )
            .annotate(UBitwidth::B32)
            .into()])],
            signature: DeclarationSignature::new()
                .inputs(vec![])
                .outputs(vec![DeclarationType::Uint(UBitwidth::B32)]),
        };

        let constants: TypedConstantSymbols<_> = vec![(
            const_id,
            TypedConstantSymbol::Here(TypedConstant::new(
                UExpressionInner::Value(1u128)
                    .annotate(UBitwidth::B32)
                    .into(),
                DeclarationType::Uint(UBitwidth::B32),
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

        let expected_program = program.clone();

        let program = ConstantInliner::inline(program);

        assert_eq!(program, expected_program)
    }

    #[test]
    fn inline_const_field_array() {
        // const field[2] a = [2, 2]
        //
        // def main() -> field:
        //      return a[0] + a[1]

        let const_id = CanonicalConstantIdentifier::new("a", "main".into());
        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![],
            statements: vec![TypedStatement::Return(vec![FieldElementExpression::Add(
                FieldElementExpression::select(
                    ArrayExpressionInner::Identifier(Identifier::from(const_id.clone()))
                        .annotate(GType::FieldElement, 2usize),
                    UExpressionInner::Value(0u128).annotate(UBitwidth::B32),
                )
                .into(),
                FieldElementExpression::select(
                    ArrayExpressionInner::Identifier(Identifier::from(const_id.clone()))
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
            const_id.clone(),
            TypedConstantSymbol::Here(TypedConstant::new(
                TypedExpression::Array(
                    ArrayExpressionInner::Value(
                        vec![
                            FieldElementExpression::Number(Bn128Field::from(2)).into(),
                            FieldElementExpression::Number(Bn128Field::from(2)).into(),
                        ]
                        .into(),
                    )
                    .annotate(GType::FieldElement, 2usize),
                ),
                DeclarationType::Array(DeclarationArrayType::new(
                    DeclarationType::FieldElement,
                    2u32,
                )),
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

        let expected_program = program.clone();

        let program = ConstantInliner::inline(program);

        assert_eq!(program, expected_program)
    }

    #[test]
    fn inline_nested_const_field() {
        // const field a = 1
        // const field b = a + 1
        //
        // def main() -> field:
        //      return b

        let const_a_id = CanonicalConstantIdentifier::new("a", "main".into());
        let const_b_id = CanonicalConstantIdentifier::new("a", "main".into());

        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![],
            statements: vec![TypedStatement::Return(vec![
                FieldElementExpression::Identifier(Identifier::from(const_b_id.clone())).into(),
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
                            const_a_id.clone(),
                            TypedConstantSymbol::Here(TypedConstant::new(
                                TypedExpression::FieldElement(FieldElementExpression::Number(
                                    Bn128Field::from(1),
                                )),
                                DeclarationType::FieldElement,
                            )),
                        ),
                        (
                            const_b_id.clone(),
                            TypedConstantSymbol::Here(TypedConstant::new(
                                TypedExpression::FieldElement(FieldElementExpression::Add(
                                    box FieldElementExpression::Identifier(Identifier::from(
                                        const_a_id.clone(),
                                    )),
                                    box FieldElementExpression::Number(Bn128Field::from(1)),
                                )),
                                DeclarationType::FieldElement,
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

        let expected_program = program.clone();

        let program = ConstantInliner::inline(program);

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

        let foo_const_id = CanonicalConstantIdentifier::new("FOO", "foo".into());
        let foo_module = TypedModule {
            functions: vec![(
                DeclarationFunctionKey::with_location("foo", "main")
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
                foo_const_id.clone(),
                TypedConstantSymbol::Here(TypedConstant::new(
                    TypedExpression::FieldElement(FieldElementExpression::Number(
                        Bn128Field::from(42),
                    )),
                    DeclarationType::FieldElement,
                )),
            )]
            .into_iter()
            .collect(),
        };

        let main_const_id = CanonicalConstantIdentifier::new("FOO", "main".into());
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
                        FieldElementExpression::Identifier(Identifier::from(main_const_id.clone()))
                            .into(),
                    ])],
                    signature: DeclarationSignature::new()
                        .inputs(vec![])
                        .outputs(vec![DeclarationType::FieldElement]),
                }),
            )]
            .into_iter()
            .collect(),
            constants: vec![(
                main_const_id.clone(),
                TypedConstantSymbol::There(foo_const_id),
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
                        FieldElementExpression::Identifier(Identifier::from(main_const_id.clone()))
                            .into(),
                    ])],
                    signature: DeclarationSignature::new()
                        .inputs(vec![])
                        .outputs(vec![DeclarationType::FieldElement]),
                }),
            )]
            .into_iter()
            .collect(),
            constants: vec![(
                main_const_id,
                TypedConstantSymbol::Here(TypedConstant::new(
                    TypedExpression::FieldElement(FieldElementExpression::Number(
                        Bn128Field::from(42),
                    )),
                    DeclarationType::FieldElement,
                )),
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
