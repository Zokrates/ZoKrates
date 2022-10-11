// The SSA transformation leaves gaps in the indices when it hits a for-loop, so that the body of the for-loop can
// modify the variables in scope. The state of the indices before all for-loops is returned to account for that possibility.
// Function calls are also left unvisited
// Saving the indices is not required for function calls, as they cannot modify their environment

// Example:
// def main(field a) -> field {
// 	   u32 n = 42;
// 	   a = a + 1;
// 	   field b = foo(a);
// 	   for u32 i in 0..n {
// 	       <body>
// 	   }
// 	   return b;
// }

// Should be turned into
// def main(field a_0) -> field {
// 	   u32 n_0 = 42;
// 	   a_1 = a_0 + 1;
// 	   field b_0 = foo(a_1); // we keep the function call as is
// 	   # versions: {n: 0, a: 1, b: 0}
// 	   for u32 i_0 in 0..n_0 {
// 	       <body> // we keep the loop body as is
// 	   }
// 	   return b_3; // we leave versions b_1 and b_2 to make b accessible and modifiable inside the for-loop
// }

use zokrates_ast::typed::folder::*;
use zokrates_ast::typed::types::ConcreteGenericsAssignment;
use zokrates_ast::typed::types::Type;
use zokrates_ast::typed::*;

use zokrates_field::Field;

use super::{Output, Versions};

pub struct ShallowTransformer<'ast, 'a> {
    // version index for any variable name
    pub versions: &'a mut Versions<'ast>,
    // A backup of the versions before each for-loop
    pub for_loop_backups: Vec<Versions<'ast>>,
    // whether all statements could be unrolled so far. Loops with variable bounds cannot.
    pub blocked: bool,
}

impl<'ast, 'a> ShallowTransformer<'ast, 'a> {
    pub fn with_versions(versions: &'a mut Versions<'ast>) -> Self {
        ShallowTransformer {
            versions,
            for_loop_backups: Vec::default(),
            blocked: false,
        }
    }

    // increase all versions by 1 and return the old versions
    fn create_version_gap(&mut self) -> Versions<'ast> {
        let ret = self.versions.clone();
        self.versions.values_mut().for_each(|v| *v += 1);
        ret
    }

    fn issue_next_identifier(&mut self, c_id: CoreIdentifier<'ast>) -> Identifier<'ast> {
        let version = *self
            .versions
            .entry(c_id.clone())
            .and_modify(|e| *e += 1) // if it was already declared, we increment
            .or_insert(0); // otherwise, we start from this version

        Identifier::from(c_id).version(version)
    }

    fn issue_next_ssa_variable<T: Field>(&mut self, v: Variable<'ast, T>) -> Variable<'ast, T> {
        assert_eq!(v.id.version, 0);

        Variable {
            id: self.issue_next_identifier(v.id.id),
            ..v
        }
    }

    pub fn transform<T: Field>(
        f: TypedFunction<'ast, T>,
        generics: &ConcreteGenericsAssignment<'ast>,
        versions: &'a mut Versions<'ast>,
    ) -> Output<TypedFunction<'ast, T>, Vec<Versions<'ast>>> {
        let mut unroller = ShallowTransformer::with_versions(versions);

        let f = unroller.fold_function(f, generics);

        match unroller.blocked {
            false => Output::Complete(f),
            true => Output::Incomplete(f, unroller.for_loop_backups),
        }
    }

    fn fold_function<T: Field>(
        &mut self,
        f: TypedFunction<'ast, T>,
        generics: &ConcreteGenericsAssignment<'ast>,
    ) -> TypedFunction<'ast, T> {
        let mut f = f;

        f.statements = generics
            .0
            .clone()
            .into_iter()
            .map(|(g, v)| {
                TypedStatement::definition(
                    Variable::new(CoreIdentifier::from(g), Type::Uint(UBitwidth::B32), false)
                        .into(),
                    UExpression::from(v as u32).into(),
                )
            })
            .chain(f.statements)
            .collect();

        for arg in &f.arguments {
            let _ = self.issue_next_identifier(arg.id.id.id.clone());
        }

        fold_function(self, f)
    }
}

impl<'ast, 'a, T: Field> Folder<'ast, T> for ShallowTransformer<'ast, 'a> {
    fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        match s {
            TypedStatement::Definition(a, DefinitionRhs::Expression(e)) => {
                let e = self.fold_expression(e);

                let a = match a {
                    TypedAssignee::Identifier(v) => {
                        let v = self.issue_next_ssa_variable(v);
                        TypedAssignee::Identifier(self.fold_variable(v))
                    }
                    a => fold_assignee(self, a),
                };

                vec![TypedStatement::definition(a, e)]
            }
            TypedStatement::Definition(assignee, DefinitionRhs::EmbedCall(embed_call)) => {
                let assignee = match assignee {
                    TypedAssignee::Identifier(v) => {
                        let v = self.issue_next_ssa_variable(v);
                        TypedAssignee::Identifier(self.fold_variable(v))
                    }
                    a => fold_assignee(self, a),
                };
                let embed_call = self.fold_embed_call(embed_call);
                vec![TypedStatement::embed_call_definition(assignee, embed_call)]
            }
            TypedStatement::For(v, from, to, stats) => {
                let from = self.fold_uint_expression(from);
                let to = self.fold_uint_expression(to);
                self.blocked = true;
                let versions_before_loop = self.create_version_gap();
                self.for_loop_backups.push(versions_before_loop);
                vec![TypedStatement::For(v, from, to, stats)]
            }
            s => fold_statement(self, s),
        }
    }

    fn fold_name(&mut self, n: Identifier<'ast>) -> Identifier<'ast> {
        let res = Identifier {
            version: *self.versions.get(&(n.id)).unwrap_or(&0),
            ..n
        };
        res
    }

    fn fold_function_call_expression<
        E: Id<'ast, T> + From<TypedExpression<'ast, T>> + Expr<'ast, T> + FunctionCall<'ast, T>,
    >(
        &mut self,
        ty: &E::Ty,
        c: FunctionCallExpression<'ast, T, E>,
    ) -> FunctionCallOrExpression<'ast, T, E> {
        if !c.function_key.id.starts_with('_') {
            self.blocked = true;
        }

        fold_function_call_expression(self, ty, c)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_ast::typed::types::DeclarationSignature;
    use zokrates_field::Bn128Field;
    mod normal {
        use super::*;

        #[test]
        fn detect_non_constant_bound() {
            let loops: Vec<TypedStatement<Bn128Field>> = vec![TypedStatement::For(
                Variable::new("i", Type::Uint(UBitwidth::B32), false),
                UExpressionInner::Identifier("i".into()).annotate(UBitwidth::B32),
                2u32.into(),
                vec![],
            )];

            let statements = loops;

            let f = TypedFunction {
                arguments: vec![],
                signature: DeclarationSignature::new(),
                statements,
            };

            match ShallowTransformer::transform(
                f,
                &ConcreteGenericsAssignment::default(),
                &mut Versions::default(),
            ) {
                Output::Incomplete(..) => {}
                _ => unreachable!(),
            };
        }

        #[test]
        fn definition() {
            // field a
            // a = 5
            // a = 6
            // a

            // should be turned into
            // a_0 = 5
            // a_1 = 6
            // a_1

            let mut versions = Versions::new();

            let mut u = ShallowTransformer::with_versions(&mut versions);

            let s = TypedStatement::definition(
                TypedAssignee::Identifier(Variable::field_element("a")),
                FieldElementExpression::Number(Bn128Field::from(5)).into(),
            );
            assert_eq!(
                u.fold_statement(s),
                vec![TypedStatement::definition(
                    TypedAssignee::Identifier(Variable::field_element(
                        Identifier::from("a").version(0)
                    )),
                    FieldElementExpression::Number(Bn128Field::from(5)).into()
                )]
            );

            let s = TypedStatement::definition(
                TypedAssignee::Identifier(Variable::field_element("a")),
                FieldElementExpression::Number(Bn128Field::from(6)).into(),
            );
            assert_eq!(
                u.fold_statement(s),
                vec![TypedStatement::definition(
                    TypedAssignee::Identifier(Variable::field_element(
                        Identifier::from("a").version(1)
                    )),
                    FieldElementExpression::Number(Bn128Field::from(6)).into()
                )]
            );

            let e: FieldElementExpression<Bn128Field> =
                FieldElementExpression::Identifier("a".into());
            assert_eq!(
                u.fold_field_expression(e),
                FieldElementExpression::Identifier(Identifier::from("a").version(1))
            );
        }

        #[test]
        fn incremental_definition() {
            // field a
            // a = 5
            // a = a + 1

            // should be turned into
            // a_0 = 5
            // a_1 = a_0 + 1

            let mut versions = Versions::new();

            let mut u = ShallowTransformer::with_versions(&mut versions);

            let s = TypedStatement::definition(
                TypedAssignee::Identifier(Variable::field_element("a")),
                FieldElementExpression::Number(Bn128Field::from(5)).into(),
            );
            assert_eq!(
                u.fold_statement(s),
                vec![TypedStatement::definition(
                    TypedAssignee::Identifier(Variable::field_element(
                        Identifier::from("a").version(0)
                    )),
                    FieldElementExpression::Number(Bn128Field::from(5)).into()
                )]
            );

            let s = TypedStatement::definition(
                TypedAssignee::Identifier(Variable::field_element("a")),
                FieldElementExpression::Add(
                    box FieldElementExpression::Identifier("a".into()),
                    box FieldElementExpression::Number(Bn128Field::from(1)),
                )
                .into(),
            );
            assert_eq!(
                u.fold_statement(s),
                vec![TypedStatement::definition(
                    TypedAssignee::Identifier(Variable::field_element(
                        Identifier::from("a").version(1)
                    )),
                    FieldElementExpression::Add(
                        box FieldElementExpression::Identifier(Identifier::from("a").version(0)),
                        box FieldElementExpression::Number(Bn128Field::from(1))
                    )
                    .into()
                )]
            );
        }

        #[test]
        fn incremental_multiple_definition() {
            // field a
            // a = 2
            // a = foo(a)

            // should be turned into
            // a_0 = 2
            // a_1 = foo(a_0)

            let mut versions = Versions::new();

            let mut u = ShallowTransformer::with_versions(&mut versions);

            let s = TypedStatement::definition(
                TypedAssignee::Identifier(Variable::field_element("a")),
                FieldElementExpression::Number(Bn128Field::from(2)).into(),
            );
            assert_eq!(
                u.fold_statement(s),
                vec![TypedStatement::definition(
                    TypedAssignee::Identifier(Variable::field_element(
                        Identifier::from("a").version(0)
                    )),
                    FieldElementExpression::Number(Bn128Field::from(2)).into()
                )]
            );

            let s: TypedStatement<Bn128Field> = TypedStatement::definition(
                Variable::field_element("a").into(),
                FieldElementExpression::function_call(
                    DeclarationFunctionKey::with_location("main", "foo").signature(
                        DeclarationSignature::new()
                            .inputs(vec![DeclarationType::FieldElement])
                            .output(DeclarationType::FieldElement),
                    ),
                    vec![],
                    vec![FieldElementExpression::Identifier("a".into()).into()],
                )
                .into(),
            );
            assert_eq!(
                u.fold_statement(s),
                vec![TypedStatement::definition(
                    Variable::field_element(Identifier::from("a").version(1)).into(),
                    FieldElementExpression::function_call(
                        DeclarationFunctionKey::with_location("main", "foo").signature(
                            DeclarationSignature::new()
                                .inputs(vec![DeclarationType::FieldElement])
                                .output(DeclarationType::FieldElement)
                        ),
                        vec![],
                        vec![
                            FieldElementExpression::Identifier(Identifier::from("a").version(0))
                                .into()
                        ]
                    )
                    .into()
                )]
            );
        }

        #[test]
        fn incremental_array_definition() {
            // field[2] a = [1, 1]
            // a[1] = 2

            // should be turned into
            // a_0 = [1, 1]
            // a_0[1] = 2

            let mut versions = Versions::new();

            let mut u = ShallowTransformer::with_versions(&mut versions);

            let s = TypedStatement::definition(
                TypedAssignee::Identifier(Variable::array("a", Type::FieldElement, 2u32)),
                ArrayExpressionInner::Value(
                    vec![
                        FieldElementExpression::Number(Bn128Field::from(1)).into(),
                        FieldElementExpression::Number(Bn128Field::from(1)).into(),
                    ]
                    .into(),
                )
                .annotate(Type::FieldElement, 2u32)
                .into(),
            );

            assert_eq!(
                u.fold_statement(s),
                vec![TypedStatement::definition(
                    TypedAssignee::Identifier(Variable::array(
                        Identifier::from("a").version(0),
                        Type::FieldElement,
                        2u32
                    )),
                    ArrayExpressionInner::Value(
                        vec![
                            FieldElementExpression::Number(Bn128Field::from(1)).into(),
                            FieldElementExpression::Number(Bn128Field::from(1)).into()
                        ]
                        .into()
                    )
                    .annotate(Type::FieldElement, 2u32)
                    .into()
                )]
            );

            let s: TypedStatement<Bn128Field> = TypedStatement::definition(
                TypedAssignee::Select(
                    box TypedAssignee::Identifier(Variable::array("a", Type::FieldElement, 2u32)),
                    box UExpression::from(1u32),
                ),
                FieldElementExpression::Number(Bn128Field::from(2)).into(),
            );

            assert_eq!(u.fold_statement(s.clone()), vec![s]);
        }

        #[test]
        fn incremental_array_of_arrays_definition() {
            // field[2][2] a = [[0, 1], [2, 3]]
            // a[1] = [4, 5]

            // should be turned into
            // a_0 = [[0, 1], [2, 3]]
            // a_0 = [4, 5]

            let mut versions = Versions::new();

            let mut u = ShallowTransformer::with_versions(&mut versions);

            let array_of_array_ty = Type::array((Type::array((Type::FieldElement, 2u32)), 2u32));

            let s = TypedStatement::definition(
                TypedAssignee::Identifier(Variable::new("a", array_of_array_ty.clone(), true)),
                ArrayExpressionInner::Value(
                    vec![
                        ArrayExpressionInner::Value(
                            vec![
                                FieldElementExpression::Number(Bn128Field::from(0)).into(),
                                FieldElementExpression::Number(Bn128Field::from(1)).into(),
                            ]
                            .into(),
                        )
                        .annotate(Type::FieldElement, 2u32)
                        .into(),
                        ArrayExpressionInner::Value(
                            vec![
                                FieldElementExpression::Number(Bn128Field::from(2)).into(),
                                FieldElementExpression::Number(Bn128Field::from(3)).into(),
                            ]
                            .into(),
                        )
                        .annotate(Type::FieldElement, 2u32)
                        .into(),
                    ]
                    .into(),
                )
                .annotate(Type::array((Type::FieldElement, 2u32)), 2u32)
                .into(),
            );

            assert_eq!(
                u.fold_statement(s),
                vec![TypedStatement::definition(
                    TypedAssignee::Identifier(Variable::new(
                        Identifier::from("a").version(0),
                        array_of_array_ty.clone(),
                        true,
                    )),
                    ArrayExpressionInner::Value(
                        vec![
                            ArrayExpressionInner::Value(
                                vec![
                                    FieldElementExpression::Number(Bn128Field::from(0)).into(),
                                    FieldElementExpression::Number(Bn128Field::from(1)).into(),
                                ]
                                .into()
                            )
                            .annotate(Type::FieldElement, 2u32)
                            .into(),
                            ArrayExpressionInner::Value(
                                vec![
                                    FieldElementExpression::Number(Bn128Field::from(2)).into(),
                                    FieldElementExpression::Number(Bn128Field::from(3)).into(),
                                ]
                                .into()
                            )
                            .annotate(Type::FieldElement, 2u32)
                            .into(),
                        ]
                        .into()
                    )
                    .annotate(Type::array((Type::FieldElement, 2u32)), 2u32)
                    .into(),
                )]
            );

            let s: TypedStatement<Bn128Field> = TypedStatement::definition(
                TypedAssignee::Select(
                    box TypedAssignee::Identifier(Variable::new(
                        "a",
                        array_of_array_ty.clone(),
                        true,
                    )),
                    box UExpression::from(1u32),
                ),
                ArrayExpressionInner::Value(
                    vec![
                        FieldElementExpression::Number(Bn128Field::from(4)).into(),
                        FieldElementExpression::Number(Bn128Field::from(5)).into(),
                    ]
                    .into(),
                )
                .annotate(Type::FieldElement, 2u32)
                .into(),
            );

            assert_eq!(u.fold_statement(s.clone()), vec![s]);
        }
    }

    mod for_loop {
        use super::*;
        use zokrates_ast::typed::types::GGenericsAssignment;
        #[test]
        fn treat_loop() {
            // def main<K>(field a) -> field {
            //     u32 n = 42;
            //     n = n;
            //     a = a;
            //     for u32 i in n..n*n {
            //         a = a;
            //     }
            //     a = a;
            //     for u32 i in n..n*n {
            //         a = a;
            //     }
            //     a = a;
            //     return a;
            // }

            // When called with K := 1, expected:
            // def main(field a_0) -> field {
            //     u32 K = 1;
            //     u32 n_0 = 42;
            //     n_1 = n_0;
            //     a_1 = a_0;
            //     # versions: {n: 1, a: 1, K: 0}
            //     for u32 i_0 in n_1..n_1*n_1 {
            //         a_0 = a_0;
            //     }
            //     a_3 = a_2;
            //     # versions: {n: 2, a: 3, K: 1}
            //     for u32 i_0 in n_2..n_2*n_2 {
            //         a_0 = a_0;
            //     }
            //     a_5 = a_4;
            //     return a_5;
            // } # versions: {n: 3, a: 5, K: 2}

            let f: TypedFunction<Bn128Field> = TypedFunction {
                arguments: vec![DeclarationVariable::field_element("a").into()],
                statements: vec![
                    TypedStatement::definition(
                        Variable::uint("n", UBitwidth::B32).into(),
                        TypedExpression::Uint(42u32.into()),
                    ),
                    TypedStatement::definition(
                        Variable::uint("n", UBitwidth::B32).into(),
                        UExpressionInner::Identifier("n".into())
                            .annotate(UBitwidth::B32)
                            .into(),
                    ),
                    TypedStatement::definition(
                        Variable::field_element("a").into(),
                        FieldElementExpression::Identifier("a".into()).into(),
                    ),
                    TypedStatement::For(
                        Variable::uint("i", UBitwidth::B32),
                        UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32),
                        UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32)
                            * UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32),
                        vec![TypedStatement::definition(
                            Variable::field_element("a").into(),
                            FieldElementExpression::Identifier("a".into()).into(),
                        )],
                    ),
                    TypedStatement::definition(
                        Variable::field_element("a").into(),
                        FieldElementExpression::Identifier("a".into()).into(),
                    ),
                    TypedStatement::For(
                        Variable::uint("i", UBitwidth::B32),
                        UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32),
                        UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32)
                            * UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32),
                        vec![TypedStatement::definition(
                            Variable::field_element("a").into(),
                            FieldElementExpression::Identifier("a".into()).into(),
                        )],
                    ),
                    TypedStatement::definition(
                        Variable::field_element("a").into(),
                        FieldElementExpression::Identifier("a".into()).into(),
                    ),
                    TypedStatement::Return(FieldElementExpression::Identifier("a".into()).into()),
                ],
                signature: DeclarationSignature::new()
                    .generics(vec![Some(
                        GenericIdentifier::with_name("K").with_index(0).into(),
                    )])
                    .inputs(vec![DeclarationType::FieldElement])
                    .output(DeclarationType::FieldElement),
            };

            let mut versions = Versions::default();

            let ssa = ShallowTransformer::transform(
                f,
                &GGenericsAssignment(
                    vec![(GenericIdentifier::with_name("K").with_index(0), 1)]
                        .into_iter()
                        .collect(),
                ),
                &mut versions,
            );

            let expected = TypedFunction {
                arguments: vec![DeclarationVariable::field_element("a").into()],
                statements: vec![
                    TypedStatement::definition(
                        Variable::uint("K", UBitwidth::B32).into(),
                        TypedExpression::Uint(1u32.into()),
                    ),
                    TypedStatement::definition(
                        Variable::uint("n", UBitwidth::B32).into(),
                        TypedExpression::Uint(42u32.into()),
                    ),
                    TypedStatement::definition(
                        Variable::uint(Identifier::from("n").version(1), UBitwidth::B32).into(),
                        UExpressionInner::Identifier("n".into())
                            .annotate(UBitwidth::B32)
                            .into(),
                    ),
                    TypedStatement::definition(
                        Variable::field_element(Identifier::from("a").version(1)).into(),
                        FieldElementExpression::Identifier("a".into()).into(),
                    ),
                    TypedStatement::For(
                        Variable::uint("i", UBitwidth::B32),
                        UExpressionInner::Identifier(Identifier::from("n").version(1))
                            .annotate(UBitwidth::B32),
                        UExpressionInner::Identifier(Identifier::from("n").version(1))
                            .annotate(UBitwidth::B32)
                            * UExpressionInner::Identifier(Identifier::from("n").version(1))
                                .annotate(UBitwidth::B32),
                        vec![TypedStatement::definition(
                            Variable::field_element("a").into(),
                            FieldElementExpression::Identifier("a".into()).into(),
                        )],
                    ),
                    TypedStatement::definition(
                        Variable::field_element(Identifier::from("a").version(3)).into(),
                        FieldElementExpression::Identifier(Identifier::from("a").version(2)).into(),
                    ),
                    TypedStatement::For(
                        Variable::uint("i", UBitwidth::B32),
                        UExpressionInner::Identifier(Identifier::from("n").version(2))
                            .annotate(UBitwidth::B32),
                        UExpressionInner::Identifier(Identifier::from("n").version(2))
                            .annotate(UBitwidth::B32)
                            * UExpressionInner::Identifier(Identifier::from("n").version(2))
                                .annotate(UBitwidth::B32),
                        vec![TypedStatement::definition(
                            Variable::field_element("a").into(),
                            FieldElementExpression::Identifier("a".into()).into(),
                        )],
                    ),
                    TypedStatement::definition(
                        Variable::field_element(Identifier::from("a").version(5)).into(),
                        FieldElementExpression::Identifier(Identifier::from("a").version(4)).into(),
                    ),
                    TypedStatement::Return(
                        FieldElementExpression::Identifier(Identifier::from("a").version(5)).into(),
                    ),
                ],
                signature: DeclarationSignature::new()
                    .generics(vec![Some(
                        GenericIdentifier::with_name("K").with_index(0).into(),
                    )])
                    .inputs(vec![DeclarationType::FieldElement])
                    .output(DeclarationType::FieldElement),
            };

            assert_eq!(
                versions,
                vec![("n".into(), 3), ("a".into(), 5), ("K".into(), 2)]
                    .into_iter()
                    .collect::<Versions>()
            );

            let expected = Output::Incomplete(
                expected,
                vec![
                    vec![("n".into(), 1), ("a".into(), 1), ("K".into(), 0)]
                        .into_iter()
                        .collect::<Versions>(),
                    vec![("n".into(), 2), ("a".into(), 3), ("K".into(), 1)]
                        .into_iter()
                        .collect::<Versions>(),
                ],
            );

            assert_eq!(ssa, expected);
        }
    }

    mod shadowing {
        use zokrates_ast::typed::types::GGenericsAssignment;

        use super::*;

        #[test]
        fn same_scope() {
            // def main(field a) {
            //     field a = 42;
            //     bool a = true
            //     return;
            // }

            // should become

            // def main(field a_0) {
            //     field a_1 = 42;
            //     bool a_2 = true;
            //     return;
            // }

            let f: TypedFunction<Bn128Field> = TypedFunction {
                arguments: vec![DeclarationVariable::field_element("a").into()],
                statements: vec![
                    TypedStatement::definition(
                        Variable::field_element("a").into(),
                        TypedExpression::Uint(42u32.into()),
                    ),
                    TypedStatement::definition(
                        Variable::boolean("a").into(),
                        BooleanExpression::Value(true).into(),
                    ),
                    TypedStatement::Return(
                        TupleExpressionInner::Value(vec![])
                            .annotate(TupleType::new(vec![]))
                            .into(),
                    ),
                ],
                signature: DeclarationSignature::new()
                    .generics(vec![])
                    .inputs(vec![DeclarationType::FieldElement]),
            };

            let expected: TypedFunction<Bn128Field> = TypedFunction {
                arguments: vec![DeclarationVariable::field_element("a").into()],
                statements: vec![
                    TypedStatement::definition(
                        Variable::field_element(Identifier::from("a").version(1)).into(),
                        TypedExpression::Uint(42u32.into()),
                    ),
                    TypedStatement::definition(
                        Variable::boolean(Identifier::from("a").version(2)).into(),
                        BooleanExpression::Value(true).into(),
                    ),
                    TypedStatement::Return(
                        TupleExpressionInner::Value(vec![])
                            .annotate(TupleType::new(vec![]))
                            .into(),
                    ),
                ],
                signature: DeclarationSignature::new()
                    .generics(vec![])
                    .inputs(vec![DeclarationType::FieldElement]),
            };

            let mut versions = Versions::default();

            let ssa =
                ShallowTransformer::transform(f, &GGenericsAssignment::default(), &mut versions);

            assert_eq!(ssa, Output::Complete(expected));
        }

        #[test]
        fn next_scope() {
            // def main(field a) {
            //    for u32 i in 0..1 {
            //       a = a + 1
            //       field a = 42
            //    }
            //    return a
            // }

            // should become

            // def main(field a_0) {
            //    # versions: {a: 0}
            //    for u32 i in 0..1 {
            //       a_0 = a_0
            //       field a_0 = 42
            //    }
            //    return a_1
            // }

            let f: TypedFunction<Bn128Field> = TypedFunction {
                arguments: vec![DeclarationVariable::field_element("a").into()],
                statements: vec![
                    TypedStatement::For(
                        Variable::uint("i", UBitwidth::B32),
                        0u32.into(),
                        1u32.into(),
                        vec![
                            TypedStatement::definition(
                                Variable::field_element(Identifier::from("a")).into(),
                                FieldElementExpression::Identifier("a".into()).into(),
                            ),
                            TypedStatement::definition(
                                Variable::field_element(Identifier::from("a")).into(),
                                FieldElementExpression::Number(42usize.into()).into(),
                            ),
                        ],
                    ),
                    TypedStatement::Return(
                        TupleExpressionInner::Value(vec![FieldElementExpression::Identifier(
                            "a".into(),
                        )
                        .into()])
                        .annotate(TupleType::new(vec![Type::FieldElement]))
                        .into(),
                    ),
                ],
                signature: DeclarationSignature::new()
                    .generics(vec![])
                    .inputs(vec![DeclarationType::FieldElement])
                    .output(DeclarationType::FieldElement),
            };

            let expected: TypedFunction<Bn128Field> = TypedFunction {
                arguments: vec![DeclarationVariable::field_element("a").into()],
                statements: vec![
                    TypedStatement::For(
                        Variable::uint("i", UBitwidth::B32),
                        0u32.into(),
                        1u32.into(),
                        vec![
                            TypedStatement::definition(
                                Variable::field_element(Identifier::from("a")).into(),
                                FieldElementExpression::Identifier(Identifier::from("a")).into(),
                            ),
                            TypedStatement::definition(
                                Variable::field_element(Identifier::from("a")).into(),
                                FieldElementExpression::Number(42usize.into()).into(),
                            ),
                        ],
                    ),
                    TypedStatement::Return(
                        TupleExpressionInner::Value(vec![FieldElementExpression::Identifier(
                            Identifier::from("a").version(1),
                        )
                        .into()])
                        .annotate(TupleType::new(vec![Type::FieldElement]))
                        .into(),
                    ),
                ],
                signature: DeclarationSignature::new()
                    .generics(vec![])
                    .inputs(vec![DeclarationType::FieldElement])
                    .output(DeclarationType::FieldElement),
            };

            let mut versions = Versions::default();

            let ssa =
                ShallowTransformer::transform(f, &GGenericsAssignment::default(), &mut versions);

            assert_eq!(
                ssa,
                Output::Incomplete(expected, vec![vec![("a".into(), 0)].into_iter().collect()])
            );
        }
    }

    mod function_call {
        use super::*;
        use zokrates_ast::typed::types::GGenericsAssignment;
        // test that function calls are left in
        #[test]
        fn treat_calls() {
            // def main<K>(field a) -> field {
            //     u32 n = 42;
            //     n = n;
            //     a = a;
            //     a = foo::<n>(a);
            //     n = n;
            //     a = a * foo::<n>(a);
            //     return a;
            // }

            // When called with K := 1, expected:
            // def main(field a_0) -> field {
            //     K = 1;
            //     u32 n_0 = 42;
            //     n_1 = n_0;
            //     a_1 = a_0;
            //     a_2 = foo::<n_1>(a_1);
            //     n_2 = n_1;
            //     a_3 = a_2 * foo::<n_2>(a_2);
            //     return a_3;
            // } # versions: {n: 2, a: 3}

            let f: TypedFunction<Bn128Field> = TypedFunction {
                arguments: vec![DeclarationVariable::field_element("a").into()],
                statements: vec![
                    TypedStatement::definition(
                        Variable::uint("n", UBitwidth::B32).into(),
                        TypedExpression::Uint(42u32.into()),
                    ),
                    TypedStatement::definition(
                        Variable::uint("n", UBitwidth::B32).into(),
                        UExpressionInner::Identifier("n".into())
                            .annotate(UBitwidth::B32)
                            .into(),
                    ),
                    TypedStatement::definition(
                        Variable::field_element("a").into(),
                        FieldElementExpression::Identifier("a".into()).into(),
                    ),
                    TypedStatement::definition(
                        Variable::field_element("a").into(),
                        FieldElementExpression::function_call(
                            DeclarationFunctionKey::with_location("main", "foo"),
                            vec![Some(
                                UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32),
                            )],
                            vec![FieldElementExpression::Identifier("a".into()).into()],
                        )
                        .into(),
                    ),
                    TypedStatement::definition(
                        Variable::uint("n", UBitwidth::B32).into(),
                        UExpressionInner::Identifier("n".into())
                            .annotate(UBitwidth::B32)
                            .into(),
                    ),
                    TypedStatement::definition(
                        Variable::field_element("a").into(),
                        (FieldElementExpression::Identifier("a".into())
                            * FieldElementExpression::function_call(
                                DeclarationFunctionKey::with_location("main", "foo"),
                                vec![Some(
                                    UExpressionInner::Identifier("n".into())
                                        .annotate(UBitwidth::B32),
                                )],
                                vec![FieldElementExpression::Identifier("a".into()).into()],
                            ))
                        .into(),
                    ),
                    TypedStatement::Return(FieldElementExpression::Identifier("a".into()).into()),
                ],
                signature: DeclarationSignature::new()
                    .generics(vec![Some(
                        GenericIdentifier::with_name("K").with_index(0).into(),
                    )])
                    .inputs(vec![DeclarationType::FieldElement])
                    .output(DeclarationType::FieldElement),
            };

            let mut versions = Versions::default();

            let ssa = ShallowTransformer::transform(
                f,
                &GGenericsAssignment(
                    vec![(GenericIdentifier::with_name("K").with_index(0), 1)]
                        .into_iter()
                        .collect(),
                ),
                &mut versions,
            );

            let expected = TypedFunction {
                arguments: vec![DeclarationVariable::field_element("a").into()],
                statements: vec![
                    TypedStatement::definition(
                        Variable::uint("K", UBitwidth::B32).into(),
                        TypedExpression::Uint(1u32.into()),
                    ),
                    TypedStatement::definition(
                        Variable::uint("n", UBitwidth::B32).into(),
                        TypedExpression::Uint(42u32.into()),
                    ),
                    TypedStatement::definition(
                        Variable::uint(Identifier::from("n").version(1), UBitwidth::B32).into(),
                        UExpressionInner::Identifier("n".into())
                            .annotate(UBitwidth::B32)
                            .into(),
                    ),
                    TypedStatement::definition(
                        Variable::field_element(Identifier::from("a").version(1)).into(),
                        FieldElementExpression::Identifier("a".into()).into(),
                    ),
                    TypedStatement::definition(
                        Variable::field_element(Identifier::from("a").version(2)).into(),
                        FieldElementExpression::function_call(
                            DeclarationFunctionKey::with_location("main", "foo"),
                            vec![Some(
                                UExpressionInner::Identifier(Identifier::from("n").version(1))
                                    .annotate(UBitwidth::B32),
                            )],
                            vec![FieldElementExpression::Identifier(
                                Identifier::from("a").version(1),
                            )
                            .into()],
                        )
                        .into(),
                    ),
                    TypedStatement::definition(
                        Variable::uint(Identifier::from("n").version(2), UBitwidth::B32).into(),
                        UExpressionInner::Identifier(Identifier::from("n").version(1))
                            .annotate(UBitwidth::B32)
                            .into(),
                    ),
                    TypedStatement::definition(
                        Variable::field_element(Identifier::from("a").version(3)).into(),
                        (FieldElementExpression::Identifier(Identifier::from("a").version(2))
                            * FieldElementExpression::function_call(
                                DeclarationFunctionKey::with_location("main", "foo"),
                                vec![Some(
                                    UExpressionInner::Identifier(Identifier::from("n").version(2))
                                        .annotate(UBitwidth::B32),
                                )],
                                vec![FieldElementExpression::Identifier(
                                    Identifier::from("a").version(2),
                                )
                                .into()],
                            ))
                        .into(),
                    ),
                    TypedStatement::Return(
                        FieldElementExpression::Identifier(Identifier::from("a").version(3)).into(),
                    ),
                ],
                signature: DeclarationSignature::new()
                    .generics(vec![Some(
                        GenericIdentifier::with_name("K").with_index(0).into(),
                    )])
                    .inputs(vec![DeclarationType::FieldElement])
                    .output(DeclarationType::FieldElement),
            };

            assert_eq!(
                versions,
                vec![("n".into(), 2), ("a".into(), 3), ("K".into(), 0)]
                    .into_iter()
                    .collect::<Versions>()
            );

            assert_eq!(ssa, Output::Incomplete(expected, vec![],));
        }
    }
}
