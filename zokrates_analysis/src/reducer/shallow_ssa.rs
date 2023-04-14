// The SSA transformation
// * introduces new versions if and only if we are assigning to an identifier
// * does not visit the statements of loops

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
// 	   for u32 i_0 in 0..n_0 {
// 	       <body> // we keep the loop body as is
// 	   }
// 	   return b_3; // we leave versions b_1 and b_2 to make b accessible and modifiable inside the for-loop
// }

use std::collections::HashMap;

use zokrates_ast::typed::folder::*;

use zokrates_ast::typed::*;

use zokrates_field::Field;

// An SSA version map, giving access to the latest version number for each identifier
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Versions<'ast> {
    map: HashMap<usize, HashMap<CoreIdentifier<'ast>, usize>>,
}

impl<'ast> Default for Versions<'ast> {
    fn default() -> Self {
        // create a call frame at index 0
        Self {
            map: vec![(0, Default::default())].into_iter().collect(),
        }
    }
}

#[derive(Debug, Default)]
pub struct ShallowTransformer<'ast> {
    // version index for any variable name
    pub versions: Versions<'ast>,
    pub frames: Vec<usize>,
    pub latest_frame: usize,
}

impl<'ast> ShallowTransformer<'ast> {
    pub fn issue_next_identifier(&mut self, c_id: CoreIdentifier<'ast>) -> Identifier<'ast> {
        let frame = self.frame();

        let frame_versions = self.versions.map.entry(frame).or_default();

        let version = frame_versions
            .entry(c_id.clone())
            .and_modify(|e| *e += 1) // if it was already declared, we increment
            .or_default(); // otherwise, we start from this version

        Identifier::from(c_id.in_frame(frame)).version(*version)
    }

    fn issue_next_ssa_variable<T: Field>(&mut self, v: Variable<'ast, T>) -> Variable<'ast, T> {
        assert_eq!(v.id.version, 0);

        Variable {
            id: self.issue_next_identifier(v.id.id.id),
            ..v
        }
    }

    fn frame(&self) -> usize {
        *self.frames.last().unwrap_or(&0)
    }

    pub fn push_call_frame(&mut self) {
        self.latest_frame += 1;
        self.frames.push(self.latest_frame);
        self.versions
            .map
            .insert(self.latest_frame, Default::default());
    }

    pub fn pop_call_frame(&mut self) {
        let frame = self.frames.pop().unwrap();
        self.versions.map.remove(&frame);
    }

    // fold an assignee replacing by the latest version. This is necessary because the trait implementation increases the ssa version for identifiers,
    // but this should not be applied recursively to complex assignees
    fn fold_assignee_no_ssa_increase<T: Field>(
        &mut self,
        a: TypedAssignee<'ast, T>,
    ) -> TypedAssignee<'ast, T> {
        match a {
            TypedAssignee::Identifier(v) => TypedAssignee::Identifier(self.fold_variable(v)),
            TypedAssignee::Select(a, index) => TypedAssignee::select(
                self.fold_assignee_no_ssa_increase(*a),
                self.fold_uint_expression(*index),
            ),
            TypedAssignee::Member(s, m) => {
                TypedAssignee::member(self.fold_assignee_no_ssa_increase(*s), m)
            }
            TypedAssignee::Element(s, index) => {
                TypedAssignee::element(self.fold_assignee_no_ssa_increase(*s), index)
            }
        }
    }
}

impl<'ast, T: Field> Folder<'ast, T> for ShallowTransformer<'ast> {
    fn fold_function(&mut self, f: TypedFunction<'ast, T>) -> TypedFunction<'ast, T> {
        for g in &f.signature.generics {
            let generic_parameter = match g.as_ref().unwrap() {
                DeclarationConstant::Generic(g) => g,
                _ => unreachable!(),
            };
            let _ = self.issue_next_identifier(CoreIdentifier::from(generic_parameter.clone()));
        }

        fold_function(self, f)
    }

    fn fold_parameter(
        &mut self,
        p: DeclarationParameter<'ast, T>,
    ) -> DeclarationParameter<'ast, T> {
        DeclarationParameter {
            id: DeclarationVariable {
                id: self.issue_next_identifier(p.id.id.id.id),
                ..p.id
            },
            ..p
        }
    }

    fn fold_assignee(&mut self, a: TypedAssignee<'ast, T>) -> TypedAssignee<'ast, T> {
        match a {
            // create a new version for assignments to identifiers
            TypedAssignee::Identifier(v) => {
                let v = self.issue_next_ssa_variable(v);
                TypedAssignee::Identifier(self.fold_variable(v))
            }
            // otherwise, simply replace by the current version
            a => self.fold_assignee_no_ssa_increase(a),
        }
    }

    // only fold bounds of for loop statements
    fn fold_for_statement(&mut self, s: ForStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        let from = self.fold_uint_expression(s.from);
        let to = self.fold_uint_expression(s.to);
        vec![TypedStatement::for_(s.var, from, to, s.statements)]
    }

    // retrieve the latest version
    fn fold_name(&mut self, n: Identifier<'ast>) -> Identifier<'ast> {
        let version = self
            .versions
            .map
            .get(&self.frame())
            .unwrap()
            .get(&n.id.id)
            .cloned()
            .unwrap_or(0);

        n.in_frame(self.frame()).version(version)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ops::*;
    use zokrates_ast::typed::types::DeclarationSignature;
    use zokrates_field::Bn128Field;
    mod normal {
        use super::*;

        #[test]
        fn ignore_loop_content() {
            // field foo = 0
            // u32 i = 4;
            // for u32 i in i..2 {
            //     foo = 5;
            // }

            // should be left unchanged, as we do not visit the loop content nor the index variable

            let f = TypedFunction {
                arguments: vec![],
                statements: vec![
                    TypedStatement::definition(
                        TypedAssignee::Identifier(Variable::field_element(Identifier::from("foo"))),
                        FieldElementExpression::value(Bn128Field::from(4)).into(),
                    ),
                    TypedStatement::definition(
                        TypedAssignee::Identifier(Variable::uint(
                            Identifier::from("i"),
                            UBitwidth::B32,
                        )),
                        UExpression::from(0u32).into(),
                    ),
                    TypedStatement::for_(
                        Variable::new("i", Type::Uint(UBitwidth::B32)),
                        UExpression::identifier("i".into()).annotate(UBitwidth::B32),
                        2u32.into(),
                        vec![TypedStatement::definition(
                            TypedAssignee::Identifier(Variable::field_element(Identifier::from(
                                "foo",
                            ))),
                            FieldElementExpression::value(Bn128Field::from(5)).into(),
                        )],
                    ),
                    TypedStatement::ret(
                        TupleExpression::value(vec![])
                            .annotate(TupleType::new(vec![]))
                            .into(),
                    ),
                ],
                signature: DeclarationSignature::default(),
            };

            let mut ssa = ShallowTransformer::default();

            assert_eq!(ssa.fold_function(f.clone()), f);
        }

        #[test]
        fn definition() {
            // field a = 5
            // a = 6
            // a

            // should be turned into
            // a_0 = 5
            // a_1 = 6
            // a_1

            let mut u = ShallowTransformer::default();

            let s = TypedStatement::definition(
                TypedAssignee::Identifier(Variable::field_element("a")),
                FieldElementExpression::value(Bn128Field::from(5)).into(),
            );
            assert_eq!(
                u.fold_statement(s),
                vec![TypedStatement::definition(
                    TypedAssignee::Identifier(Variable::field_element(
                        Identifier::from("a").version(0)
                    )),
                    FieldElementExpression::value(Bn128Field::from(5)).into()
                )]
            );

            let s = TypedStatement::definition(
                TypedAssignee::Identifier(Variable::field_element("a")),
                FieldElementExpression::value(Bn128Field::from(6)).into(),
            );
            assert_eq!(
                u.fold_statement(s),
                vec![TypedStatement::definition(
                    TypedAssignee::Identifier(Variable::field_element(
                        Identifier::from("a").version(1)
                    )),
                    FieldElementExpression::value(Bn128Field::from(6)).into()
                )]
            );

            let e: FieldElementExpression<Bn128Field> =
                FieldElementExpression::identifier("a".into());
            assert_eq!(
                u.fold_field_expression(e),
                FieldElementExpression::identifier(Identifier::from("a").version(1))
            );
        }

        #[test]
        fn incremental_definition() {
            // field a = 5
            // a = a + 1

            // should be turned into
            // a_0 = 5
            // a_1 = a_0 + 1

            let mut u = ShallowTransformer::default();

            let s = TypedStatement::definition(
                TypedAssignee::Identifier(Variable::field_element("a")),
                FieldElementExpression::value(Bn128Field::from(5)).into(),
            );
            assert_eq!(
                u.fold_statement(s),
                vec![TypedStatement::definition(
                    TypedAssignee::Identifier(Variable::field_element(
                        Identifier::from("a").version(0)
                    )),
                    FieldElementExpression::value(Bn128Field::from(5)).into()
                )]
            );

            let s = TypedStatement::definition(
                TypedAssignee::Identifier(Variable::field_element("a")),
                FieldElementExpression::add(
                    FieldElementExpression::identifier("a".into()),
                    FieldElementExpression::value(Bn128Field::from(1)),
                )
                .into(),
            );
            assert_eq!(
                u.fold_statement(s),
                vec![TypedStatement::definition(
                    TypedAssignee::Identifier(Variable::field_element(
                        Identifier::from("a").version(1)
                    )),
                    FieldElementExpression::add(
                        FieldElementExpression::identifier(Identifier::from("a").version(0)),
                        FieldElementExpression::value(Bn128Field::from(1))
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

            let mut u = ShallowTransformer::default();

            let s = TypedStatement::definition(
                TypedAssignee::Identifier(Variable::field_element("a")),
                FieldElementExpression::value(Bn128Field::from(2)).into(),
            );
            assert_eq!(
                u.fold_statement(s),
                vec![TypedStatement::definition(
                    TypedAssignee::Identifier(Variable::field_element(
                        Identifier::from("a").version(0)
                    )),
                    FieldElementExpression::value(Bn128Field::from(2)).into()
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
                    vec![FieldElementExpression::identifier("a".into()).into()],
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
                            FieldElementExpression::identifier(Identifier::from("a").version(0))
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

            let mut u = ShallowTransformer::default();

            let s = TypedStatement::definition(
                TypedAssignee::Identifier(Variable::array("a", Type::FieldElement, 2u32)),
                ArrayExpression::value(vec![
                    FieldElementExpression::value(Bn128Field::from(1)).into(),
                    FieldElementExpression::value(Bn128Field::from(1)).into(),
                ])
                .annotate(ArrayType::new(Type::FieldElement, 2u32))
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
                    ArrayExpression::value(vec![
                        FieldElementExpression::value(Bn128Field::from(1)).into(),
                        FieldElementExpression::value(Bn128Field::from(1)).into()
                    ])
                    .annotate(ArrayType::new(Type::FieldElement, 2u32))
                    .into()
                )]
            );

            let s: TypedStatement<Bn128Field> = TypedStatement::definition(
                TypedAssignee::Select(
                    Box::new(TypedAssignee::Identifier(Variable::array(
                        "a",
                        Type::FieldElement,
                        2u32,
                    ))),
                    Box::new(UExpression::from(1u32)),
                ),
                FieldElementExpression::value(Bn128Field::from(2)).into(),
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

            let mut u = ShallowTransformer::default();

            let array_of_array_ty = Type::array((Type::array((Type::FieldElement, 2u32)), 2u32));

            let s = TypedStatement::definition(
                TypedAssignee::Identifier(Variable::new("a", array_of_array_ty.clone())),
                ArrayExpression::value(vec![
                    ArrayExpression::value(vec![
                        FieldElementExpression::value(Bn128Field::from(0)).into(),
                        FieldElementExpression::value(Bn128Field::from(1)).into(),
                    ])
                    .annotate(ArrayType::new(Type::FieldElement, 2u32))
                    .into(),
                    ArrayExpression::value(vec![
                        FieldElementExpression::value(Bn128Field::from(2)).into(),
                        FieldElementExpression::value(Bn128Field::from(3)).into(),
                    ])
                    .annotate(ArrayType::new(Type::FieldElement, 2u32))
                    .into(),
                ])
                .annotate(ArrayType::new(
                    Type::array((Type::FieldElement, 2u32)),
                    2u32,
                ))
                .into(),
            );

            assert_eq!(
                u.fold_statement(s),
                vec![TypedStatement::definition(
                    TypedAssignee::Identifier(Variable::new(
                        Identifier::from("a").version(0),
                        array_of_array_ty.clone(),
                    )),
                    ArrayExpression::value(vec![
                        ArrayExpression::value(vec![
                            FieldElementExpression::value(Bn128Field::from(0)).into(),
                            FieldElementExpression::value(Bn128Field::from(1)).into(),
                        ])
                        .annotate(ArrayType::new(Type::FieldElement, 2u32))
                        .into(),
                        ArrayExpression::value(vec![
                            FieldElementExpression::value(Bn128Field::from(2)).into(),
                            FieldElementExpression::value(Bn128Field::from(3)).into(),
                        ])
                        .annotate(ArrayType::new(Type::FieldElement, 2u32))
                        .into(),
                    ])
                    .annotate(ArrayType::new(
                        Type::array((Type::FieldElement, 2u32)),
                        2u32
                    ))
                    .into(),
                )]
            );

            let s: TypedStatement<Bn128Field> = TypedStatement::definition(
                TypedAssignee::select(
                    TypedAssignee::Identifier(Variable::new("a", array_of_array_ty.clone())),
                    UExpression::from(1u32),
                ),
                ArrayExpression::value(vec![
                    FieldElementExpression::value(Bn128Field::from(4)).into(),
                    FieldElementExpression::value(Bn128Field::from(5)).into(),
                ])
                .annotate(ArrayType::new(Type::FieldElement, 2u32))
                .into(),
            );

            assert_eq!(u.fold_statement(s.clone()), vec![s]);
        }
    }

    mod for_loop {
        use super::*;

        #[test]
        fn treat_loop() {
            // def main(field a) -> field {
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

            // expected:
            // def main(field a_0) -> field {
            //     u32 n_0 = 42;
            //     n_1 = n_0;
            //     a_1 = a_0;
            //     for u32 i_0 in n_1..n_1*n_1 {
            //         a_0 = a_0;
            //     }
            //     a_2 = a_1;
            //     for u32 i_0 in n_1..n_1*n_1 {
            //         a_0 = a_0;
            //     }
            //     a_3 = a_2;
            //     return a_3;
            // }

            let f: TypedFunction<Bn128Field> = TypedFunction {
                arguments: vec![DeclarationVariable::field_element("a").into()],
                statements: vec![
                    TypedStatement::definition(
                        Variable::uint("n", UBitwidth::B32).into(),
                        TypedExpression::Uint(42u32.into()),
                    ),
                    TypedStatement::definition(
                        Variable::uint("n", UBitwidth::B32).into(),
                        UExpression::identifier("n".into())
                            .annotate(UBitwidth::B32)
                            .into(),
                    ),
                    TypedStatement::definition(
                        Variable::field_element("a").into(),
                        FieldElementExpression::identifier("a".into()).into(),
                    ),
                    TypedStatement::for_(
                        Variable::uint("i", UBitwidth::B32),
                        UExpression::identifier("n".into()).annotate(UBitwidth::B32),
                        UExpression::identifier("n".into()).annotate(UBitwidth::B32)
                            * UExpression::identifier("n".into()).annotate(UBitwidth::B32),
                        vec![TypedStatement::definition(
                            Variable::field_element("a").into(),
                            FieldElementExpression::identifier("a".into()).into(),
                        )],
                    ),
                    TypedStatement::definition(
                        Variable::field_element("a").into(),
                        FieldElementExpression::identifier("a".into()).into(),
                    ),
                    TypedStatement::for_(
                        Variable::uint("i", UBitwidth::B32),
                        UExpression::identifier("n".into()).annotate(UBitwidth::B32),
                        UExpression::identifier("n".into()).annotate(UBitwidth::B32)
                            * UExpression::identifier("n".into()).annotate(UBitwidth::B32),
                        vec![TypedStatement::definition(
                            Variable::field_element("a").into(),
                            FieldElementExpression::identifier("a".into()).into(),
                        )],
                    ),
                    TypedStatement::definition(
                        Variable::field_element("a").into(),
                        FieldElementExpression::identifier("a".into()).into(),
                    ),
                    TypedStatement::ret(FieldElementExpression::identifier("a".into()).into()),
                ],
                signature: DeclarationSignature::new()
                    .inputs(vec![DeclarationType::FieldElement])
                    .output(DeclarationType::FieldElement),
            };

            let mut ssa = ShallowTransformer::default();

            let expected = TypedFunction {
                arguments: vec![DeclarationVariable::field_element("a").into()],
                statements: vec![
                    TypedStatement::definition(
                        Variable::uint("n", UBitwidth::B32).into(),
                        TypedExpression::Uint(42u32.into()),
                    ),
                    TypedStatement::definition(
                        Variable::uint(Identifier::from("n").version(1), UBitwidth::B32).into(),
                        UExpression::identifier("n".into())
                            .annotate(UBitwidth::B32)
                            .into(),
                    ),
                    TypedStatement::definition(
                        Variable::field_element(Identifier::from("a").version(1)).into(),
                        FieldElementExpression::identifier("a".into()).into(),
                    ),
                    TypedStatement::for_(
                        Variable::uint("i", UBitwidth::B32),
                        UExpression::identifier(Identifier::from("n").version(1))
                            .annotate(UBitwidth::B32),
                        UExpression::identifier(Identifier::from("n").version(1))
                            .annotate(UBitwidth::B32)
                            * UExpression::identifier(Identifier::from("n").version(1))
                                .annotate(UBitwidth::B32),
                        vec![TypedStatement::definition(
                            Variable::field_element("a").into(),
                            FieldElementExpression::identifier("a".into()).into(),
                        )],
                    ),
                    TypedStatement::definition(
                        Variable::field_element(Identifier::from("a").version(2)).into(),
                        FieldElementExpression::identifier(Identifier::from("a").version(1)).into(),
                    ),
                    TypedStatement::for_(
                        Variable::uint("i", UBitwidth::B32),
                        UExpression::identifier(Identifier::from("n").version(1))
                            .annotate(UBitwidth::B32),
                        UExpression::identifier(Identifier::from("n").version(1))
                            .annotate(UBitwidth::B32)
                            * UExpression::identifier(Identifier::from("n").version(1))
                                .annotate(UBitwidth::B32),
                        vec![TypedStatement::definition(
                            Variable::field_element("a").into(),
                            FieldElementExpression::identifier("a".into()).into(),
                        )],
                    ),
                    TypedStatement::definition(
                        Variable::field_element(Identifier::from("a").version(3)).into(),
                        FieldElementExpression::identifier(Identifier::from("a").version(2)).into(),
                    ),
                    TypedStatement::ret(
                        FieldElementExpression::identifier(Identifier::from("a").version(3)).into(),
                    ),
                ],
                signature: DeclarationSignature::new()
                    .inputs(vec![DeclarationType::FieldElement])
                    .output(DeclarationType::FieldElement),
            };

            let res = ssa.fold_function(f);

            assert_eq!(
                ssa.versions.map,
                vec![(
                    0,
                    vec![("n".into(), 1), ("a".into(), 3)].into_iter().collect()
                )]
                .into_iter()
                .collect()
            );

            assert_eq!(res, expected);
        }
    }

    mod shadowing {

        use super::*;

        #[test]
        fn same_scope() {
            // def main(field a) {
            //     field a = 42;
            //     bool a = true
            //     return;
            // }

            // should become (only the field variable is affected as shadowing is taken care of in semantics already)

            // def main(field a_s0_v0) {
            //     field a_s0_v1 = 42;
            //     bool a_s1_v0 = true
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
                        Variable::boolean(CoreIdentifier::from(ShadowedIdentifier::shadow(
                            "a".into(),
                            1,
                        )))
                        .into(),
                        BooleanExpression::value(true).into(),
                    ),
                    TypedStatement::ret(
                        TupleExpression::value(vec![])
                            .annotate(TupleType::new(vec![]))
                            .into(),
                    ),
                ],
                signature: DeclarationSignature::new().inputs(vec![DeclarationType::FieldElement]),
            };

            let expected: TypedFunction<Bn128Field> = TypedFunction {
                arguments: vec![DeclarationVariable::field_element("a").into()],
                statements: vec![
                    TypedStatement::definition(
                        Variable::field_element(Identifier::from("a").version(1)).into(),
                        TypedExpression::Uint(42u32.into()),
                    ),
                    TypedStatement::definition(
                        Variable::boolean(CoreIdentifier::from(ShadowedIdentifier::shadow(
                            "a".into(),
                            1,
                        )))
                        .into(),
                        BooleanExpression::value(true).into(),
                    ),
                    TypedStatement::ret(
                        TupleExpression::value(vec![])
                            .annotate(TupleType::new(vec![]))
                            .into(),
                    ),
                ],
                signature: DeclarationSignature::new().inputs(vec![DeclarationType::FieldElement]),
            };

            let ssa = ShallowTransformer::default().fold_function(f);

            assert_eq!(ssa, expected);
        }
    }

    mod function_call {
        use super::*;
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

            // def main(field a_0) -> field {
            //     a_1 = a_0;
            //     a_2 = foo::<42>(a_1);
            //     a_3 = a_2 * foo::<42>(a_2);
            //     return a_3;
            // }

            let f: TypedFunction<Bn128Field> = TypedFunction {
                arguments: vec![DeclarationVariable::field_element("a").into()],
                statements: vec![
                    TypedStatement::definition(
                        Variable::uint("n", UBitwidth::B32).into(),
                        TypedExpression::Uint(42u32.into()),
                    ),
                    TypedStatement::definition(
                        Variable::uint("n", UBitwidth::B32).into(),
                        UExpression::identifier("n".into())
                            .annotate(UBitwidth::B32)
                            .into(),
                    ),
                    TypedStatement::definition(
                        Variable::field_element("a").into(),
                        FieldElementExpression::identifier("a".into()).into(),
                    ),
                    TypedStatement::definition(
                        Variable::field_element("a").into(),
                        FieldElementExpression::function_call(
                            DeclarationFunctionKey::with_location("main", "foo"),
                            vec![Some(
                                UExpression::identifier("n".into()).annotate(UBitwidth::B32),
                            )],
                            vec![FieldElementExpression::identifier("a".into()).into()],
                        )
                        .into(),
                    ),
                    TypedStatement::definition(
                        Variable::uint("n", UBitwidth::B32).into(),
                        UExpression::identifier("n".into())
                            .annotate(UBitwidth::B32)
                            .into(),
                    ),
                    TypedStatement::definition(
                        Variable::field_element("a").into(),
                        (FieldElementExpression::identifier("a".into())
                            * FieldElementExpression::function_call(
                                DeclarationFunctionKey::with_location("main", "foo"),
                                vec![Some(
                                    UExpression::identifier("n".into()).annotate(UBitwidth::B32),
                                )],
                                vec![FieldElementExpression::identifier("a".into()).into()],
                            ))
                        .into(),
                    ),
                    TypedStatement::ret(FieldElementExpression::identifier("a".into()).into()),
                ],
                signature: DeclarationSignature::new()
                    .generics(vec![Some(
                        GenericIdentifier::with_name("K").with_index(0).into(),
                    )])
                    .inputs(vec![DeclarationType::FieldElement])
                    .output(DeclarationType::FieldElement),
            };

            let expected = TypedFunction {
                arguments: vec![DeclarationVariable::field_element("a").into()],
                statements: vec![
                    TypedStatement::definition(
                        Variable::uint("n", UBitwidth::B32).into(),
                        TypedExpression::Uint(42u32.into()),
                    ),
                    TypedStatement::definition(
                        Variable::uint(Identifier::from("n").version(1), UBitwidth::B32).into(),
                        UExpression::identifier("n".into())
                            .annotate(UBitwidth::B32)
                            .into(),
                    ),
                    TypedStatement::definition(
                        Variable::field_element(Identifier::from("a").version(1)).into(),
                        FieldElementExpression::identifier("a".into()).into(),
                    ),
                    TypedStatement::definition(
                        Variable::field_element(Identifier::from("a").version(2)).into(),
                        FieldElementExpression::function_call(
                            DeclarationFunctionKey::with_location("main", "foo"),
                            vec![Some(
                                UExpression::identifier(Identifier::from("n").version(1))
                                    .annotate(UBitwidth::B32),
                            )],
                            vec![FieldElementExpression::identifier(
                                Identifier::from("a").version(1),
                            )
                            .into()],
                        )
                        .into(),
                    ),
                    TypedStatement::definition(
                        Variable::uint(Identifier::from("n").version(2), UBitwidth::B32).into(),
                        UExpression::identifier(Identifier::from("n").version(1))
                            .annotate(UBitwidth::B32)
                            .into(),
                    ),
                    TypedStatement::definition(
                        Variable::field_element(Identifier::from("a").version(3)).into(),
                        (FieldElementExpression::identifier(Identifier::from("a").version(2))
                            * FieldElementExpression::function_call(
                                DeclarationFunctionKey::with_location("main", "foo"),
                                vec![Some(
                                    UExpression::identifier(Identifier::from("n").version(2))
                                        .annotate(UBitwidth::B32),
                                )],
                                vec![FieldElementExpression::identifier(
                                    Identifier::from("a").version(2),
                                )
                                .into()],
                            ))
                        .into(),
                    ),
                    TypedStatement::ret(
                        FieldElementExpression::identifier(Identifier::from("a").version(3)).into(),
                    ),
                ],
                signature: DeclarationSignature::new()
                    .generics(vec![Some(
                        GenericIdentifier::with_name("K").with_index(0).into(),
                    )])
                    .inputs(vec![DeclarationType::FieldElement])
                    .output(DeclarationType::FieldElement),
            };

            let mut ssa = ShallowTransformer::default();

            let res = ssa.fold_function(f);

            assert_eq!(
                ssa.versions.map,
                vec![(
                    0,
                    vec![("n".into(), 2), ("a".into(), 3), ("K".into(), 0)]
                        .into_iter()
                        .collect()
                )]
                .into_iter()
                .collect()
            );

            assert_eq!(res, expected);
        }
    }
}
