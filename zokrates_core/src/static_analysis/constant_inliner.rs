use crate::typed_absy::folder::{
    fold_array_expression, fold_array_expression_inner, fold_boolean_expression,
    fold_field_expression, fold_module, fold_struct_expression, fold_struct_expression_inner,
    fold_uint_expression, fold_uint_expression_inner, Folder,
};
use crate::typed_absy::{
    ArrayExpression, ArrayExpressionInner, ArrayType, BooleanExpression, FieldElementExpression,
    StructExpression, StructExpressionInner, StructType, TypedConstants, TypedModule, TypedProgram,
    UBitwidth, UExpression, UExpressionInner,
};
use std::collections::HashMap;
use std::convert::TryInto;
use zokrates_field::Field;

pub struct ConstantInliner<'ast, T: Field> {
    constants: TypedConstants<'ast, T>,
}

impl<'ast, T: Field> ConstantInliner<'ast, T> {
    pub fn inline(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        let mut inliner = ConstantInliner {
            constants: HashMap::new(),
        };
        inliner.fold_program(p)
    }
}

impl<'ast, T: Field> Folder<'ast, T> for ConstantInliner<'ast, T> {
    fn fold_module(&mut self, p: TypedModule<'ast, T>) -> TypedModule<'ast, T> {
        self.constants = p.constants.clone().unwrap_or_default();
        TypedModule {
            functions: fold_module(self, p).functions,
            constants: None,
        }
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> FieldElementExpression<'ast, T> {
        match e {
            FieldElementExpression::Identifier(ref id) => match self.constants.get(id).cloned() {
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
            BooleanExpression::Identifier(ref id) => match self.constants.get(id).cloned() {
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
            UExpressionInner::Identifier(ref id) => match self.constants.get(id).cloned() {
                Some(c) => {
                    let expr: UExpression<'ast, T> = c.expression.try_into().unwrap();
                    fold_uint_expression(self, expr).into_inner()
                }
                None => fold_uint_expression_inner(self, size, e),
            },
            // default
            e => fold_uint_expression_inner(self, size, e),
        }
    }

    fn fold_array_expression_inner(
        &mut self,
        ty: &ArrayType<'ast, T>,
        e: ArrayExpressionInner<'ast, T>,
    ) -> ArrayExpressionInner<'ast, T> {
        match e {
            ArrayExpressionInner::Identifier(ref id) => match self.constants.get(id).cloned() {
                Some(c) => {
                    let expr: ArrayExpression<'ast, T> = c.expression.try_into().unwrap();
                    fold_array_expression(self, expr).into_inner()
                }
                None => fold_array_expression_inner(self, ty, e),
            },
            // default
            e => fold_array_expression_inner(self, ty, e),
        }
    }

    fn fold_struct_expression_inner(
        &mut self,
        ty: &StructType<'ast, T>,
        e: StructExpressionInner<'ast, T>,
    ) -> StructExpressionInner<'ast, T> {
        match e {
            StructExpressionInner::Identifier(ref id) => match self.constants.get(id).cloned() {
                Some(c) => {
                    let expr: StructExpression<'ast, T> = c.expression.try_into().unwrap();
                    fold_struct_expression(self, expr).into_inner()
                }
                None => fold_struct_expression_inner(self, ty, e),
            },
            // default
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

        let const_id = Identifier::from("a");
        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![],
            statements: vec![TypedStatement::Return(vec![
                FieldElementExpression::Identifier(const_id.clone()).into(),
            ])],
            signature: DeclarationSignature::new()
                .inputs(vec![])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        let mut constants = TypedConstants::<Bn128Field>::new();
        constants.insert(
            const_id.clone(),
            TypedConstant {
                id: const_id.clone(),
                ty: GType::FieldElement,
                expression: (TypedExpression::FieldElement(FieldElementExpression::Number(
                    Bn128Field::from(1),
                ))),
            },
        );

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
                    constants: Some(constants),
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
                    constants: None,
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

        let const_id = Identifier::from("a");
        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![],
            statements: vec![TypedStatement::Return(vec![BooleanExpression::Identifier(
                const_id.clone(),
            )
            .into()])],
            signature: DeclarationSignature::new()
                .inputs(vec![])
                .outputs(vec![DeclarationType::Boolean]),
        };

        let mut constants = TypedConstants::<Bn128Field>::new();
        constants.insert(
            const_id.clone(),
            TypedConstant {
                id: const_id.clone(),
                ty: GType::Boolean,
                expression: (TypedExpression::Boolean(BooleanExpression::Value(true))),
            },
        );

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
                    constants: Some(constants),
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
                    constants: None,
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

        let const_id = Identifier::from("a");
        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![],
            statements: vec![TypedStatement::Return(vec![UExpressionInner::Identifier(
                const_id.clone(),
            )
            .annotate(UBitwidth::B32)
            .into()])],
            signature: DeclarationSignature::new()
                .inputs(vec![])
                .outputs(vec![DeclarationType::Uint(UBitwidth::B32)]),
        };

        let mut constants = TypedConstants::<Bn128Field>::new();
        constants.insert(
            const_id.clone(),
            TypedConstant {
                id: const_id.clone(),
                ty: GType::Uint(UBitwidth::B32),
                expression: (UExpressionInner::Value(1u128)
                    .annotate(UBitwidth::B32)
                    .into()),
            },
        );

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
                    constants: Some(constants),
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
                    constants: None,
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

        let const_id = Identifier::from("a");
        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![],
            statements: vec![TypedStatement::Return(vec![FieldElementExpression::Add(
                FieldElementExpression::Select(
                    box ArrayExpressionInner::Identifier(const_id.clone())
                        .annotate(GType::FieldElement, 2usize),
                    box UExpressionInner::Value(0u128).annotate(UBitwidth::B32),
                )
                .into(),
                FieldElementExpression::Select(
                    box ArrayExpressionInner::Identifier(const_id.clone())
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

        let mut constants = TypedConstants::<Bn128Field>::new();
        constants.insert(
            const_id.clone(),
            TypedConstant {
                id: const_id.clone(),
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
            },
        );

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
                    constants: Some(constants),
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
                    constants: None,
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

        let const_a_id = Identifier::from("a");
        let const_b_id = Identifier::from("b");

        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![],
            statements: vec![TypedStatement::Return(vec![
                FieldElementExpression::Identifier(const_b_id.clone()).into(),
            ])],
            signature: DeclarationSignature::new()
                .inputs(vec![])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        let mut constants = TypedConstants::<Bn128Field>::new();
        constants.extend(vec![
            (
                const_a_id.clone(),
                TypedConstant {
                    id: const_a_id.clone(),
                    ty: GType::FieldElement,
                    expression: (TypedExpression::FieldElement(FieldElementExpression::Number(
                        Bn128Field::from(1),
                    ))),
                },
            ),
            (
                const_b_id.clone(),
                TypedConstant {
                    id: const_b_id.clone(),
                    ty: GType::FieldElement,
                    expression: (TypedExpression::FieldElement(FieldElementExpression::Add(
                        box FieldElementExpression::Identifier(const_a_id.clone()),
                        box FieldElementExpression::Number(Bn128Field::from(1)),
                    ))),
                },
            ),
        ]);

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
                    constants: Some(constants),
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
                    constants: None,
                },
            )]
            .into_iter()
            .collect(),
        };

        assert_eq!(program, expected_program)
    }
}
