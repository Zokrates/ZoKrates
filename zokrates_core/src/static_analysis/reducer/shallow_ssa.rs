// The SSA transformation leaves gaps in the indices when it hits a for-loop, so that the body of the for-loop can
// modify the variables in scope. The state of the indices before all for-loops is returned to account for that possibility.
// Function calls are also left unvisited
// Saving the indices is not required for function calls, as they cannot modify their environment

// Example:
// def main(field a) -> field:
//		u32 n = 42
//		a = a + 1
//      field b = foo(a)
// 		for u32 i in 0..n:
//			<body>
//		endfor
//		return b

// Should be turned into
// def main(field a_0) -> field:
//		u32 n_0 = 42
//		a_1 = a_0 + 1
//      field b_0 = foo(a_1) // we keep the function call as is
//		# versions: {n: 0, a: 1, b: 0}
// 		for u32 i_0 in 0..n_0:
//			<body> // we keep the loop body as is
//		endfor
//		return b_3 // we leave versions b_1 and b_2 to make b accessible and modifiable inside the for-loop

use crate::typed_absy::folder::*;
use crate::typed_absy::types::ConcreteGenericsAssignment;
use crate::typed_absy::types::Type;
use crate::typed_absy::*;

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

    // increase all versions by 2 and return the old versions
    fn create_version_gap(&mut self) -> Versions<'ast> {
        let ret = self.versions.clone();
        self.versions.values_mut().for_each(|v| *v += 2);
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
            .iter()
            .map(|(g, v)| {
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::with_id_and_type(
                        *g,
                        Type::Uint(UBitwidth::B32),
                    )),
                    UExpression::from(*v as u32).into(),
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
            TypedStatement::Declaration(_) => vec![],
            TypedStatement::Definition(a, e) => {
                let e = self.fold_expression(e);

                let a = match a {
                    TypedAssignee::Identifier(v) => {
                        let v = self.issue_next_ssa_variable(v);
                        TypedAssignee::Identifier(self.fold_variable(v))
                    }
                    a => fold_assignee(self, a),
                };

                vec![TypedStatement::Definition(a, e)]
            }
            TypedStatement::MultipleDefinition(assignees, exprs) => {
                let exprs = self.fold_expression_list(exprs);
                let assignees = assignees
                    .into_iter()
                    .map(|a| match a {
                        TypedAssignee::Identifier(v) => {
                            let v = self.issue_next_ssa_variable(v);
                            TypedAssignee::Identifier(self.fold_variable(v))
                        }
                        a => fold_assignee(self, a),
                    })
                    .collect();

                vec![TypedStatement::MultipleDefinition(assignees, exprs)]
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

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> FieldElementExpression<'ast, T> {
        if let FieldElementExpression::FunctionCall(ref k, _, _) = e {
            if !k.id.starts_with('_') {
                self.blocked = true;
            }
        }

        fold_field_expression(self, e)
    }

    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> BooleanExpression<'ast, T> {
        if let BooleanExpression::FunctionCall(ref k, _, _) = e {
            if !k.id.starts_with('_') {
                self.blocked = true;
            }
        };

        fold_boolean_expression(self, e)
    }

    fn fold_uint_expression_inner(
        &mut self,
        b: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> UExpressionInner<'ast, T> {
        if let UExpressionInner::FunctionCall(ref k, _, _) = e {
            if !k.id.starts_with('_') {
                self.blocked = true;
            }
        };

        fold_uint_expression_inner(self, b, e)
    }

    fn fold_array_expression_inner(
        &mut self,
        ty: &ArrayType<'ast, T>,
        e: ArrayExpressionInner<'ast, T>,
    ) -> ArrayExpressionInner<'ast, T> {
        if let ArrayExpressionInner::FunctionCall(ref k, _, _) = e {
            if !k.id.starts_with('_') {
                self.blocked = true;
            }
        };

        fold_array_expression_inner(self, ty, e)
    }

    fn fold_struct_expression_inner(
        &mut self,
        ty: &StructType<'ast, T>,
        e: StructExpressionInner<'ast, T>,
    ) -> StructExpressionInner<'ast, T> {
        if let StructExpressionInner::FunctionCall(ref k, _, _) = e {
            if !k.id.starts_with('_') {
                self.blocked = true;
            }
        };

        fold_struct_expression_inner(self, ty, e)
    }

    fn fold_expression_list(
        &mut self,
        e: TypedExpressionList<'ast, T>,
    ) -> TypedExpressionList<'ast, T> {
        match e {
            TypedExpressionList::FunctionCall(ref k, _, _, _) => {
                if !k.id.starts_with('_') {
                    self.blocked = true;
                }
            }
            _ => unreachable!(),
        };

        fold_expression_list(self, e)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typed_absy::types::DeclarationSignature;
    use zokrates_field::Bn128Field;
    mod normal {
        use super::*;

        #[test]
        fn detect_non_constant_bound() {
            let loops: Vec<TypedStatement<Bn128Field>> = vec![TypedStatement::For(
                Variable::uint("i", UBitwidth::B32),
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
            let s: TypedStatement<Bn128Field> =
                TypedStatement::Declaration(Variable::field_element("a"));
            assert_eq!(u.fold_statement(s), vec![]);

            let s = TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::field_element("a")),
                FieldElementExpression::Number(Bn128Field::from(5)).into(),
            );
            assert_eq!(
                u.fold_statement(s),
                vec![TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element(
                        Identifier::from("a").version(0)
                    )),
                    FieldElementExpression::Number(Bn128Field::from(5)).into()
                )]
            );

            let s = TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::field_element("a")),
                FieldElementExpression::Number(Bn128Field::from(6)).into(),
            );
            assert_eq!(
                u.fold_statement(s),
                vec![TypedStatement::Definition(
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

            let s: TypedStatement<Bn128Field> =
                TypedStatement::Declaration(Variable::field_element("a"));
            assert_eq!(u.fold_statement(s), vec![]);

            let s = TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::field_element("a")),
                FieldElementExpression::Number(Bn128Field::from(5)).into(),
            );
            assert_eq!(
                u.fold_statement(s),
                vec![TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element(
                        Identifier::from("a").version(0)
                    )),
                    FieldElementExpression::Number(Bn128Field::from(5)).into()
                )]
            );

            let s = TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::field_element("a")),
                FieldElementExpression::Add(
                    box FieldElementExpression::Identifier("a".into()),
                    box FieldElementExpression::Number(Bn128Field::from(1)),
                )
                .into(),
            );
            assert_eq!(
                u.fold_statement(s),
                vec![TypedStatement::Definition(
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
            use crate::typed_absy::types::Type;

            // field a
            // a = 2
            // a = foo(a)

            // should be turned into
            // a_0 = 2
            // a_1 = foo(a_0)

            let mut versions = Versions::new();

            let mut u = ShallowTransformer::with_versions(&mut versions);

            let s: TypedStatement<Bn128Field> =
                TypedStatement::Declaration(Variable::field_element("a"));
            assert_eq!(u.fold_statement(s), vec![]);

            let s = TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::field_element("a")),
                FieldElementExpression::Number(Bn128Field::from(2)).into(),
            );
            assert_eq!(
                u.fold_statement(s),
                vec![TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element(
                        Identifier::from("a").version(0)
                    )),
                    FieldElementExpression::Number(Bn128Field::from(2)).into()
                )]
            );

            let s: TypedStatement<Bn128Field> = TypedStatement::MultipleDefinition(
                vec![Variable::field_element("a").into()],
                TypedExpressionList::FunctionCall(
                    DeclarationFunctionKey::with_location("main", "foo").signature(
                        DeclarationSignature::new()
                            .inputs(vec![DeclarationType::FieldElement])
                            .outputs(vec![DeclarationType::FieldElement]),
                    ),
                    vec![],
                    vec![FieldElementExpression::Identifier("a".into()).into()],
                    vec![Type::FieldElement],
                ),
            );
            assert_eq!(
                u.fold_statement(s),
                vec![TypedStatement::MultipleDefinition(
                    vec![Variable::field_element(Identifier::from("a").version(1)).into()],
                    TypedExpressionList::FunctionCall(
                        DeclarationFunctionKey::with_location("main", "foo").signature(
                            DeclarationSignature::new()
                                .inputs(vec![DeclarationType::FieldElement])
                                .outputs(vec![DeclarationType::FieldElement])
                        ),
                        vec![],
                        vec![
                            FieldElementExpression::Identifier(Identifier::from("a").version(0))
                                .into()
                        ],
                        vec![Type::FieldElement],
                    )
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

            let s: TypedStatement<Bn128Field> =
                TypedStatement::Declaration(Variable::array("a", Type::FieldElement, 2u32));
            assert_eq!(u.fold_statement(s), vec![]);

            let s = TypedStatement::Definition(
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
                vec![TypedStatement::Definition(
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

            let s: TypedStatement<Bn128Field> = TypedStatement::Definition(
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

            let s: TypedStatement<Bn128Field> = TypedStatement::Declaration(
                Variable::with_id_and_type("a", array_of_array_ty.clone()),
            );
            assert_eq!(u.fold_statement(s), vec![]);

            let s = TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::with_id_and_type(
                    "a",
                    array_of_array_ty.clone(),
                )),
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
                vec![TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::with_id_and_type(
                        Identifier::from("a").version(0),
                        array_of_array_ty.clone(),
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

            let s: TypedStatement<Bn128Field> = TypedStatement::Definition(
                TypedAssignee::Select(
                    box TypedAssignee::Identifier(Variable::with_id_and_type(
                        "a",
                        array_of_array_ty.clone(),
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
        use crate::typed_absy::types::GGenericsAssignment;
        #[test]
        fn treat_loop() {
            // def main<K>(field a) -> field:
            //      u32 n = 42
            //      n = n
            //      a = a
            //      for u32 i in n..n*n:
            //          a = a
            //      endfor
            //      a = a
            //      for u32 i in n..n*n:
            //          a = a
            //      endfor
            //      a = a
            //      return a

            // When called with K := 1, expected:
            // def main(field a_0) -> field:
            //      u32 K = 1
            //      u32 n_0 = 42
            //      n_1 = n_0
            //      a_1 = a_0
            //      # versions: {n: 1, a: 1}
            //      for u32 i_0 in n_0..n_0*n_0:
            //          a_0 = a_0
            //      endfor
            //      a_4 = a_3
            //      # versions: {n: 3, a: 4}
            //      for u32 i_0 in n_0..n_0*n_0:
            //          a_0 = a_0
            //      endfor
            //      a_7 = a_6
            //      return a_7
            //      # versions: {n: 5, a: 7}

            let f: TypedFunction<Bn128Field> = TypedFunction {
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
                    TypedStatement::For(
                        Variable::uint("i", UBitwidth::B32),
                        UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32),
                        UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32)
                            * UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32),
                        vec![TypedStatement::Definition(
                            Variable::field_element("a").into(),
                            FieldElementExpression::Identifier("a".into()).into(),
                        )],
                    ),
                    TypedStatement::Definition(
                        Variable::field_element("a").into(),
                        FieldElementExpression::Identifier("a".into()).into(),
                    ),
                    TypedStatement::For(
                        Variable::uint("i", UBitwidth::B32),
                        UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32),
                        UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32)
                            * UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32),
                        vec![TypedStatement::Definition(
                            Variable::field_element("a").into(),
                            FieldElementExpression::Identifier("a".into()).into(),
                        )],
                    ),
                    TypedStatement::Definition(
                        Variable::field_element("a").into(),
                        FieldElementExpression::Identifier("a".into()).into(),
                    ),
                    TypedStatement::Return(vec![
                        FieldElementExpression::Identifier("a".into()).into()
                    ]),
                ],
                signature: DeclarationSignature::new()
                    .generics(vec![Some("K".into())])
                    .inputs(vec![DeclarationType::FieldElement])
                    .outputs(vec![DeclarationType::FieldElement]),
            };

            let mut versions = Versions::default();

            let ssa = ShallowTransformer::transform(
                f,
                &GGenericsAssignment(vec![("K", 1)].into_iter().collect()),
                &mut versions,
            );

            let expected = TypedFunction {
                arguments: vec![DeclarationVariable::field_element("a").into()],
                statements: vec![
                    TypedStatement::Definition(
                        Variable::uint("K", UBitwidth::B32).into(),
                        TypedExpression::Uint(1u32.into()),
                    ),
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
                    TypedStatement::For(
                        Variable::uint("i", UBitwidth::B32),
                        UExpressionInner::Identifier(Identifier::from("n").version(1))
                            .annotate(UBitwidth::B32),
                        UExpressionInner::Identifier(Identifier::from("n").version(1))
                            .annotate(UBitwidth::B32)
                            * UExpressionInner::Identifier(Identifier::from("n").version(1))
                                .annotate(UBitwidth::B32),
                        vec![TypedStatement::Definition(
                            Variable::field_element("a").into(),
                            FieldElementExpression::Identifier("a".into()).into(),
                        )],
                    ),
                    TypedStatement::Definition(
                        Variable::field_element(Identifier::from("a").version(4)).into(),
                        FieldElementExpression::Identifier(Identifier::from("a").version(3)).into(),
                    ),
                    TypedStatement::For(
                        Variable::uint("i", UBitwidth::B32),
                        UExpressionInner::Identifier(Identifier::from("n").version(3))
                            .annotate(UBitwidth::B32),
                        UExpressionInner::Identifier(Identifier::from("n").version(3))
                            .annotate(UBitwidth::B32)
                            * UExpressionInner::Identifier(Identifier::from("n").version(3))
                                .annotate(UBitwidth::B32),
                        vec![TypedStatement::Definition(
                            Variable::field_element("a").into(),
                            FieldElementExpression::Identifier("a".into()).into(),
                        )],
                    ),
                    TypedStatement::Definition(
                        Variable::field_element(Identifier::from("a").version(7)).into(),
                        FieldElementExpression::Identifier(Identifier::from("a").version(6)).into(),
                    ),
                    TypedStatement::Return(vec![FieldElementExpression::Identifier(
                        Identifier::from("a").version(7),
                    )
                    .into()]),
                ],
                signature: DeclarationSignature::new()
                    .generics(vec![Some("K".into())])
                    .inputs(vec![DeclarationType::FieldElement])
                    .outputs(vec![DeclarationType::FieldElement]),
            };

            assert_eq!(
                versions,
                vec![("n".into(), 5), ("a".into(), 7), ("K".into(), 4)]
                    .into_iter()
                    .collect::<Versions>()
            );

            let expected = Output::Incomplete(
                expected,
                vec![
                    vec![("n".into(), 1), ("a".into(), 1), ("K".into(), 0)]
                        .into_iter()
                        .collect::<Versions>(),
                    vec![("n".into(), 3), ("a".into(), 4), ("K".into(), 2)]
                        .into_iter()
                        .collect::<Versions>(),
                ],
            );

            assert_eq!(ssa, expected);
        }
    }

    mod function_call {
        use super::*;
        use crate::typed_absy::types::GGenericsAssignment;
        // test that function calls are left in
        #[test]
        fn treat_calls() {
            // def main<K>(field a) -> field:
            //      u32 n = 42
            //      n = n
            //      a = a
            //      a = foo::<n>(a)
            //      n = n
            //      a = a * foo::<n>(a)
            //      return a

            // When called with K := 1, expected:
            // def main(field a_0) -> field:
            //      K = 1
            //      u32 n_0 = 42
            //      n_1 = n_0
            //      a_1 = a_0
            //      a_2 = foo::<n_1>(a_1)
            //      n_2 = n_1
            //      a_3 = a_2 * foo::<n_2>(a_2)
            //      return a_3
            //      # versions: {n: 2, a: 3}

            let f: TypedFunction<Bn128Field> = TypedFunction {
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
                            DeclarationFunctionKey::with_location("main", "foo"),
                            vec![Some(
                                UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32),
                            )],
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
                    TypedStatement::Definition(
                        Variable::field_element("a").into(),
                        (FieldElementExpression::Identifier("a".into())
                            * FieldElementExpression::FunctionCall(
                                DeclarationFunctionKey::with_location("main", "foo"),
                                vec![Some(
                                    UExpressionInner::Identifier("n".into())
                                        .annotate(UBitwidth::B32),
                                )],
                                vec![FieldElementExpression::Identifier("a".into()).into()],
                            ))
                        .into(),
                    ),
                    TypedStatement::Return(vec![
                        FieldElementExpression::Identifier("a".into()).into()
                    ]),
                ],
                signature: DeclarationSignature::new()
                    .generics(vec![Some("K".into())])
                    .inputs(vec![DeclarationType::FieldElement])
                    .outputs(vec![DeclarationType::FieldElement]),
            };

            let mut versions = Versions::default();

            let ssa = ShallowTransformer::transform(
                f,
                &GGenericsAssignment(vec![("K", 1)].into_iter().collect()),
                &mut versions,
            );

            let expected = TypedFunction {
                arguments: vec![DeclarationVariable::field_element("a").into()],
                statements: vec![
                    TypedStatement::Definition(
                        Variable::uint("K", UBitwidth::B32).into(),
                        TypedExpression::Uint(1u32.into()),
                    ),
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
                    TypedStatement::MultipleDefinition(
                        vec![Variable::field_element(Identifier::from("a").version(2)).into()],
                        TypedExpressionList::FunctionCall(
                            DeclarationFunctionKey::with_location("main", "foo"),
                            vec![Some(
                                UExpressionInner::Identifier(Identifier::from("n").version(1))
                                    .annotate(UBitwidth::B32),
                            )],
                            vec![FieldElementExpression::Identifier(
                                Identifier::from("a").version(1),
                            )
                            .into()],
                            vec![Type::FieldElement],
                        ),
                    ),
                    TypedStatement::Definition(
                        Variable::uint(Identifier::from("n").version(2), UBitwidth::B32).into(),
                        UExpressionInner::Identifier(Identifier::from("n").version(1))
                            .annotate(UBitwidth::B32)
                            .into(),
                    ),
                    TypedStatement::Definition(
                        Variable::field_element(Identifier::from("a").version(3)).into(),
                        (FieldElementExpression::Identifier(Identifier::from("a").version(2))
                            * FieldElementExpression::FunctionCall(
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
                    TypedStatement::Return(vec![FieldElementExpression::Identifier(
                        Identifier::from("a").version(3),
                    )
                    .into()]),
                ],
                signature: DeclarationSignature::new()
                    .generics(vec![Some("K".into())])
                    .inputs(vec![DeclarationType::FieldElement])
                    .outputs(vec![DeclarationType::FieldElement]),
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
