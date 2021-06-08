use crate::typed_absy::folder::*;
use crate::typed_absy::types::DeclarationConstant;
use crate::typed_absy::*;
use core::str;
use std::collections::HashMap;
use std::convert::TryInto;
use zokrates_field::Field;

type ModuleConstants<'ast, T> =
    HashMap<OwnedTypedModuleId, HashMap<&'ast str, TypedConstant<'ast, T>>>;

pub struct ConstantInliner<'ast, T> {
    modules: TypedModules<'ast, T>,
    location: OwnedTypedModuleId,
    constants: ModuleConstants<'ast, T>,
}

impl<'ast, 'a, T: Field> ConstantInliner<'ast, T> {
    pub fn new(
        modules: TypedModules<'ast, T>,
        location: OwnedTypedModuleId,
        constants: ModuleConstants<'ast, T>,
    ) -> Self {
        ConstantInliner {
            modules,
            location,
            constants,
        }
    }
    pub fn inline(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        let constants = HashMap::new();
        let mut inliner = ConstantInliner::new(p.modules.clone(), p.main.clone(), constants);
        inliner.fold_program(p)
    }

    // fn module(&self) -> &TypedModule<'ast, T> {
    //     self.modules.get(&self.location).unwrap()
    // }

    fn change_location(&mut self, location: OwnedTypedModuleId) -> OwnedTypedModuleId {
        let prev = self.location.clone();
        self.location = location;
        prev
    }

    fn get_constant(&mut self, id: &Identifier) -> Option<TypedConstant<'ast, T>> {
        assert_eq!(id.version, 0);
        match id.id {
            CoreIdentifier::Call(..) => {
                unreachable!("calls indentifiers are only available after call inlining")
            }
            CoreIdentifier::Source(id) => self
                .constants
                .get(&self.location)
                .and_then(|constants| constants.get(id))
                .cloned(),
        }
    }
}

impl<'ast, T: Field> Folder<'ast, T> for ConstantInliner<'ast, T> {
    fn fold_program(&mut self, p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        TypedProgram {
            modules: p
                .modules
                .into_iter()
                .map(|(m_id, m)| {
                    self.change_location(m_id.clone());
                    (m_id, self.fold_module(m))
                })
                .collect(),
            ..p
        }
    }

    fn fold_module(&mut self, m: TypedModule<'ast, T>) -> TypedModule<'ast, T> {
        // only treat this module if its constants are not in the map yet
        if !self.constants.contains_key(&self.location) {
            self.constants.entry(self.location.clone()).or_default();
            TypedModule {
                constants: m
                    .constants
                    .into_iter()
                    .map(|(id, tc)| {
                        let constant = match tc {
                            TypedConstantSymbol::There(imported_id) => {
                                if !self.constants.contains_key(&imported_id.module) {
                                    let current_m_id = self.change_location(id.module.clone());
                                    let _ = self
                                        .fold_module(self.modules.get(&id.module).unwrap().clone());
                                    self.change_location(current_m_id);
                                }
                                self.constants
                                    .get(&imported_id.module)
                                    .unwrap()
                                    .get(&imported_id.id)
                                    .cloned()
                                    .unwrap()
                            }
                            TypedConstantSymbol::Here(c) => fold_constant(self, c),
                        };

                        assert!(self
                            .constants
                            .entry(self.location.clone())
                            .or_default()
                            .insert(id.id, constant.clone())
                            .is_none());

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
        } else {
            m
        }
    }

    fn fold_declaration_constant(
        &mut self,
        c: DeclarationConstant<'ast>,
    ) -> DeclarationConstant<'ast> {
        println!("id {}", c);
        println!("constants {:#?}", self.constants);
        println!("location {}", self.location.display());

        match c {
            DeclarationConstant::Constant(id) => DeclarationConstant::Concrete(
                match self
                    .constants
                    .get(&self.location)
                    .unwrap()
                    .get(&id)
                    .cloned()
                    .unwrap()
                {
                    TypedConstant {
                        ty: Type::Uint(UBitwidth::B32),
                        expression:
                            TypedExpression::Uint(UExpression {
                                inner: UExpressionInner::Value(v),
                                ..
                            }),
                    } => v as u32,
                    _ => unreachable!(),
                },
            ),
            c => c,
        }
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> FieldElementExpression<'ast, T> {
        match e {
            FieldElementExpression::Identifier(ref id) => match self.get_constant(id) {
                Some(c) => self.fold_constant(c).try_into().unwrap(),
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
                Some(c) => self.fold_constant(c).try_into().unwrap(),
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
                    let e: UExpression<'ast, T> = self.fold_constant(c).try_into().unwrap();
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
            ArrayExpressionInner::Identifier(ref id) => match self.get_constant(id) {
                Some(c) => {
                    let e: ArrayExpression<'ast, T> = self.fold_constant(c).try_into().unwrap();
                    e.into_inner()
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
                    let e: StructExpression<'ast, T> = self.fold_constant(c).try_into().unwrap();
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
            TypedConstantSymbol::Here(TypedConstant::new(
                GType::FieldElement,
                TypedExpression::FieldElement(FieldElementExpression::Number(Bn128Field::from(1))),
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
            const_id,
            TypedConstantSymbol::Here(TypedConstant::new(
                GType::Boolean,
                TypedExpression::Boolean(BooleanExpression::Value(true)),
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
            const_id,
            TypedConstantSymbol::Here(TypedConstant::new(
                GType::Uint(UBitwidth::B32),
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
            const_id,
            TypedConstantSymbol::Here(TypedConstant::new(
                GType::FieldElement,
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
                            const_a_id,
                            TypedConstantSymbol::Here(TypedConstant::new(
                                GType::FieldElement,
                                TypedExpression::FieldElement(FieldElementExpression::Number(
                                    Bn128Field::from(1),
                                )),
                            )),
                        ),
                        (
                            const_b_id,
                            TypedConstantSymbol::Here(TypedConstant::new(
                                GType::FieldElement,
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
                            const_a_id,
                            TypedConstantSymbol::Here(TypedConstant::new(
                                GType::FieldElement,
                                TypedExpression::FieldElement(FieldElementExpression::Number(
                                    Bn128Field::from(1),
                                )),
                            )),
                        ),
                        (
                            const_b_id,
                            TypedConstantSymbol::Here(TypedConstant::new(
                                GType::FieldElement,
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
                foo_const_id,
                TypedConstantSymbol::Here(TypedConstant::new(
                    GType::FieldElement,
                    TypedExpression::FieldElement(FieldElementExpression::Number(
                        Bn128Field::from(42),
                    )),
                )),
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
                foo_const_id,
                TypedConstantSymbol::There(OwnedTypedModuleId::from("foo"), foo_const_id),
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
                foo_const_id,
                TypedConstantSymbol::Here(TypedConstant::new(
                    GType::FieldElement,
                    TypedExpression::FieldElement(FieldElementExpression::Number(
                        Bn128Field::from(42),
                    )),
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
