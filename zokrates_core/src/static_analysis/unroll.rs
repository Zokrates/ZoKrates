//! Module containing SSA reduction, including for-loop unrolling
//!
//! @file unroll.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use crate::typed_absy::folder::*;
use crate::typed_absy::types::{MemberId, Type};
use crate::typed_absy::*;
use std::collections::HashMap;
use std::collections::HashSet;
use typed_absy::identifier::CoreIdentifier;
use zokrates_field::Field;

pub enum Output<'ast, T: Field> {
    Complete(TypedProgram<'ast, T>),
    Incomplete(TypedProgram<'ast, T>, usize),
}

pub struct Unroller<'ast> {
    // version index for any variable name
    substitution: HashMap<CoreIdentifier<'ast>, usize>,
    // whether all statements could be unrolled so far. Loops with variable bounds cannot.
    complete: bool,
    statement_count: usize,
}

impl<'ast> Unroller<'ast> {
    fn new() -> Self {
        Unroller {
            substitution: HashMap::new(),
            complete: true,
            statement_count: 0,
        }
    }

    fn issue_next_ssa_variable(&mut self, v: Variable<'ast>) -> Variable<'ast> {
        let res = match self.substitution.get(&v.id.id) {
            Some(i) => Variable {
                id: Identifier {
                    id: v.id.id.clone(),
                    version: i + 1,
                    stack: vec![],
                },
                ..v
            },
            None => Variable { ..v.clone() },
        };

        self.substitution
            .entry(v.id.id)
            .and_modify(|e| *e += 1)
            .or_insert(0);
        res
    }

    pub fn unroll<T: Field>(p: TypedProgram<T>) -> Output<T> {
        let mut unroller = Unroller::new();
        let p = unroller.fold_program(p);

        match unroller.complete {
            true => Output::Complete(p),
            false => Output::Incomplete(p, unroller.statement_count),
        }
    }
}

impl<'ast, T: Field> Folder<'ast, T> for Unroller<'ast> {
    fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        self.statement_count += 1;
        match s {
            TypedStatement::Declaration(_) => vec![],
            TypedStatement::Definition(a, e) => {
                let e = self.fold_expression(e);

                let a = match a {
                    TypedAssignee::Identifier(v) => {
                        TypedAssignee::Identifier(self.issue_next_ssa_variable(v))
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
                            TypedAssignee::Identifier(self.issue_next_ssa_variable(v))
                        }
                        a => fold_assignee(self, a),
                    })
                    .collect();

                vec![TypedStatement::MultipleDefinition(assignees, exprs)]
            }
            TypedStatement::For(v, from, to, stats) => {
                let from = self.fold_field_expression(from);
                let to = self.fold_field_expression(to);

                match (from, to) {
                    (FieldElementExpression::Number(from), FieldElementExpression::Number(to)) => {
                        let mut values: Vec<T> = vec![];
                        let mut current = from;
                        while current < to {
                            values.push(current.clone());
                            current = T::one() + &current;
                        }

                        let res = values
                            .into_iter()
                            .map(|index| {
                                vec![
                                    vec![
                                        TypedStatement::Declaration(v.clone()),
                                        TypedStatement::Definition(
                                            TypedAssignee::Identifier(v.clone()),
                                            FieldElementExpression::Number(index).into(),
                                        ),
                                    ],
                                    stats.clone(),
                                ]
                                .into_iter()
                                .flat_map(|x| x)
                            })
                            .flat_map(|x| x)
                            .flat_map(|x| self.fold_statement(x))
                            .collect();

                        res
                    }
                    (from, to) => {
                        self.complete = false;
                        vec![TypedStatement::For(v, from, to, stats)]
                    }
                }
            }
            s => fold_statement(self, s),
        }
    }

    fn fold_function(&mut self, f: TypedFunction<'ast, T>) -> TypedFunction<'ast, T> {
        self.substitution = HashMap::new();
        for arg in &f.arguments {
            self.substitution.insert(arg.id.id.id.clone(), 0);
        }

        fold_function(self, f)
    }

    fn fold_name(&mut self, n: Identifier<'ast>) -> Identifier<'ast> {
        Identifier {
            version: self.substitution.get(&n.id).unwrap_or(&0).clone(),
            ..n
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::Bn128Field;

    // #[test]
    // fn ssa_array() {
    //     let a0 = ArrayExpressionInner::Identifier("a".into()).annotate(Type::FieldElement, 3);

    //     let e = FieldElementExpression::Number(Bn128Field::from(42)).into();

    //     let index = FieldElementExpression::Number(Bn128Field::from(1));

    //     let a1 = Unroller::choose_many(
    //         a0.clone().into(),
    //         vec![Access::Select(index)],
    //         e,
    //         &mut HashSet::new(),
    //     );

    //     // a[1] = 42
    //     // -> a = [0 == 1 ? 42 : a[0], 1 == 1 ? 42 : a[1], 2 == 1 ? 42 : a[2]]

    //     assert_eq!(
    //         a1,
    //         ArrayExpressionInner::Value(vec![
    //             FieldElementExpression::if_else(
    //                 BooleanExpression::FieldEq(
    //                     box FieldElementExpression::Number(Bn128Field::from(0)),
    //                     box FieldElementExpression::Number(Bn128Field::from(1))
    //                 ),
    //                 FieldElementExpression::Number(Bn128Field::from(42)),
    //                 FieldElementExpression::select(
    //                     a0.clone(),
    //                     FieldElementExpression::Number(Bn128Field::from(0))
    //                 )
    //             )
    //             .into(),
    //             FieldElementExpression::if_else(
    //                 BooleanExpression::FieldEq(
    //                     box FieldElementExpression::Number(Bn128Field::from(1)),
    //                     box FieldElementExpression::Number(Bn128Field::from(1))
    //                 ),
    //                 FieldElementExpression::Number(Bn128Field::from(42)),
    //                 FieldElementExpression::select(
    //                     a0.clone(),
    //                     FieldElementExpression::Number(Bn128Field::from(1))
    //                 )
    //             )
    //             .into(),
    //             FieldElementExpression::if_else(
    //                 BooleanExpression::FieldEq(
    //                     box FieldElementExpression::Number(Bn128Field::from(2)),
    //                     box FieldElementExpression::Number(Bn128Field::from(1))
    //                 ),
    //                 FieldElementExpression::Number(Bn128Field::from(42)),
    //                 FieldElementExpression::select(
    //                     a0.clone(),
    //                     FieldElementExpression::Number(Bn128Field::from(2))
    //                 )
    //             )
    //             .into()
    //         ])
    //         .annotate(Type::FieldElement, 3)
    //         .into()
    //     );

    //     let a0 = ArrayExpressionInner::Identifier("a".into())
    //         .annotate(Type::array(Type::FieldElement, 3), 3);

    //     let e = ArrayExpressionInner::Identifier("b".into()).annotate(Type::FieldElement, 3);

    //     let index = FieldElementExpression::Number(Bn128Field::from(1));

    //     let a1 = Unroller::choose_many(
    //         a0.clone().into(),
    //         vec![Access::Select(index)],
    //         e.clone().into(),
    //         &mut HashSet::new(),
    //     );

    //     // a[0] = b
    //     // -> a = [0 == 1 ? b : a[0], 1 == 1 ? b : a[1], 2 == 1 ? b : a[2]]

    //     assert_eq!(
    //         a1,
    //         ArrayExpressionInner::Value(vec![
    //             ArrayExpression::if_else(
    //                 BooleanExpression::FieldEq(
    //                     box FieldElementExpression::Number(Bn128Field::from(0)),
    //                     box FieldElementExpression::Number(Bn128Field::from(1))
    //                 ),
    //                 e.clone(),
    //                 ArrayExpression::select(
    //                     a0.clone(),
    //                     FieldElementExpression::Number(Bn128Field::from(0))
    //                 )
    //             )
    //             .into(),
    //             ArrayExpression::if_else(
    //                 BooleanExpression::FieldEq(
    //                     box FieldElementExpression::Number(Bn128Field::from(1)),
    //                     box FieldElementExpression::Number(Bn128Field::from(1))
    //                 ),
    //                 e.clone(),
    //                 ArrayExpression::select(
    //                     a0.clone(),
    //                     FieldElementExpression::Number(Bn128Field::from(1))
    //                 )
    //             )
    //             .into(),
    //             ArrayExpression::if_else(
    //                 BooleanExpression::FieldEq(
    //                     box FieldElementExpression::Number(Bn128Field::from(2)),
    //                     box FieldElementExpression::Number(Bn128Field::from(1))
    //                 ),
    //                 e.clone(),
    //                 ArrayExpression::select(
    //                     a0.clone(),
    //                     FieldElementExpression::Number(Bn128Field::from(2))
    //                 )
    //             )
    //             .into()
    //         ])
    //         .annotate(Type::array(Type::FieldElement, 3), 3)
    //         .into()
    //     );

    //     let a0 = ArrayExpressionInner::Identifier("a".into())
    //         .annotate(Type::array(Type::FieldElement, 2), 2);

    //     let e = FieldElementExpression::Number(Bn128Field::from(42));

    //     let indices = vec![
    //         Access::Select(FieldElementExpression::Number(Bn128Field::from(0))),
    //         Access::Select(FieldElementExpression::Number(Bn128Field::from(0))),
    //     ];

    //     let a1 = Unroller::choose_many(
    //         a0.clone().into(),
    //         indices,
    //         e.clone().into(),
    //         &mut HashSet::new(),
    //     );

    //     // a[0][0] = 42
    //     // -> a = [0 == 0 ? [0 == 0 ? 42 : a[0][0], 1 == 0 ? 42 : a[0][1]] : a[0], 1 == 0 ? [0 == 0 ? 42 : a[1][0], 1 == 0 ? 42 : a[1][1]] : a[1]]

    //     assert_eq!(
    //         a1,
    //         ArrayExpressionInner::Value(vec![
    //             ArrayExpression::if_else(
    //                 BooleanExpression::FieldEq(
    //                     box FieldElementExpression::Number(Bn128Field::from(0)),
    //                     box FieldElementExpression::Number(Bn128Field::from(0))
    //                 ),
    //                 ArrayExpressionInner::Value(vec![
    //                     FieldElementExpression::if_else(
    //                         BooleanExpression::FieldEq(
    //                             box FieldElementExpression::Number(Bn128Field::from(0)),
    //                             box FieldElementExpression::Number(Bn128Field::from(0))
    //                         ),
    //                         e.clone(),
    //                         FieldElementExpression::select(
    //                             ArrayExpression::select(
    //                                 a0.clone(),
    //                                 FieldElementExpression::Number(Bn128Field::from(0))
    //                             ),
    //                             FieldElementExpression::Number(Bn128Field::from(0))
    //                         )
    //                     )
    //                     .into(),
    //                     FieldElementExpression::if_else(
    //                         BooleanExpression::FieldEq(
    //                             box FieldElementExpression::Number(Bn128Field::from(1)),
    //                             box FieldElementExpression::Number(Bn128Field::from(0))
    //                         ),
    //                         e.clone(),
    //                         FieldElementExpression::select(
    //                             ArrayExpression::select(
    //                                 a0.clone(),
    //                                 FieldElementExpression::Number(Bn128Field::from(0))
    //                             ),
    //                             FieldElementExpression::Number(Bn128Field::from(1))
    //                         )
    //                     )
    //                     .into()
    //                 ])
    //                 .annotate(Type::FieldElement, 2),
    //                 ArrayExpression::select(
    //                     a0.clone(),
    //                     FieldElementExpression::Number(Bn128Field::from(0))
    //                 )
    //             )
    //             .into(),
    //             ArrayExpression::if_else(
    //                 BooleanExpression::FieldEq(
    //                     box FieldElementExpression::Number(Bn128Field::from(1)),
    //                     box FieldElementExpression::Number(Bn128Field::from(0))
    //                 ),
    //                 ArrayExpressionInner::Value(vec![
    //                     FieldElementExpression::if_else(
    //                         BooleanExpression::FieldEq(
    //                             box FieldElementExpression::Number(Bn128Field::from(0)),
    //                             box FieldElementExpression::Number(Bn128Field::from(0))
    //                         ),
    //                         e.clone(),
    //                         FieldElementExpression::select(
    //                             ArrayExpression::select(
    //                                 a0.clone(),
    //                                 FieldElementExpression::Number(Bn128Field::from(1))
    //                             ),
    //                             FieldElementExpression::Number(Bn128Field::from(0))
    //                         )
    //                     )
    //                     .into(),
    //                     FieldElementExpression::if_else(
    //                         BooleanExpression::FieldEq(
    //                             box FieldElementExpression::Number(Bn128Field::from(1)),
    //                             box FieldElementExpression::Number(Bn128Field::from(0))
    //                         ),
    //                         e.clone(),
    //                         FieldElementExpression::select(
    //                             ArrayExpression::select(
    //                                 a0.clone(),
    //                                 FieldElementExpression::Number(Bn128Field::from(1))
    //                             ),
    //                             FieldElementExpression::Number(Bn128Field::from(1))
    //                         )
    //                     )
    //                     .into()
    //                 ])
    //                 .annotate(Type::FieldElement, 2),
    //                 ArrayExpression::select(
    //                     a0.clone(),
    //                     FieldElementExpression::Number(Bn128Field::from(1))
    //                 )
    //             )
    //             .into(),
    //         ])
    //         .annotate(Type::array(Type::FieldElement, 2), 2)
    //         .into()
    //     );
    // }

    #[cfg(test)]
    mod statement {
        use super::*;
        use crate::typed_absy::types::{FunctionKey, Signature};

        #[test]
        fn for_loop() {
            // for field i in 2..5
            //		field foo = i

            // should be unrolled to
            // i_0 = 2
            // foo_0 = i_0
            // i_1 = 3
            // foo_1 = i_1
            // i_2 = 4
            // foo_2 = i_2

            let s = TypedStatement::For(
                Variable::field_element("i"),
                FieldElementExpression::Number(Bn128Field::from(2)),
                FieldElementExpression::Number(Bn128Field::from(5)),
                vec![
                    TypedStatement::Declaration(Variable::field_element("foo")),
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::field_element("foo")),
                        FieldElementExpression::Identifier("i".into()).into(),
                    ),
                ],
            );

            let expected = vec![
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element(
                        Identifier::from("i").version(0),
                    )),
                    FieldElementExpression::Number(Bn128Field::from(2)).into(),
                ),
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element(
                        Identifier::from("foo").version(0),
                    )),
                    FieldElementExpression::Identifier(Identifier::from("i").version(0)).into(),
                ),
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element(
                        Identifier::from("i").version(1),
                    )),
                    FieldElementExpression::Number(Bn128Field::from(3)).into(),
                ),
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element(
                        Identifier::from("foo").version(1),
                    )),
                    FieldElementExpression::Identifier(Identifier::from("i").version(1)).into(),
                ),
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element(
                        Identifier::from("i").version(2),
                    )),
                    FieldElementExpression::Number(Bn128Field::from(4)).into(),
                ),
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element(
                        Identifier::from("foo").version(2),
                    )),
                    FieldElementExpression::Identifier(Identifier::from("i").version(2)).into(),
                ),
            ];

            let mut u = Unroller::new();

            assert_eq!(u.fold_statement(s), expected);
        }

        #[test]
        fn idempotence() {
            // an already unrolled program should not be modified by unrolling again

            // a = 5
            // a_1 = 6
            // a_2 = 7

            // should be turned into
            // a = 5
            // a_1 = 6
            // a_2 = 7

            let mut u = Unroller::new();

            let s = TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::field_element(
                    Identifier::from("a").version(0),
                )),
                FieldElementExpression::Number(Bn128Field::from(5)).into(),
            );
            assert_eq!(u.fold_statement(s.clone()), vec![s]);

            let s = TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::field_element(
                    Identifier::from("a").version(1),
                )),
                FieldElementExpression::Number(Bn128Field::from(6)).into(),
            );
            assert_eq!(u.fold_statement(s.clone()), vec![s]);

            let s = TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::field_element(
                    Identifier::from("a").version(2),
                )),
                FieldElementExpression::Number(Bn128Field::from(7)).into(),
            );
            assert_eq!(u.fold_statement(s.clone()), vec![s]);
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

            let mut u = Unroller::new();

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

            let mut u = Unroller::new();

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

            let mut u = Unroller::new();

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
                    FunctionKey::with_id("foo").signature(
                        Signature::new()
                            .inputs(vec![Type::FieldElement])
                            .outputs(vec![Type::FieldElement]),
                    ),
                    vec![FieldElementExpression::Identifier("a".into()).into()],
                    vec![Type::FieldElement],
                ),
            );
            assert_eq!(
                u.fold_statement(s),
                vec![TypedStatement::MultipleDefinition(
                    vec![Variable::field_element(Identifier::from("a").version(1)).into()],
                    TypedExpressionList::FunctionCall(
                        FunctionKey::with_id("foo").signature(
                            Signature::new()
                                .inputs(vec![Type::FieldElement])
                                .outputs(vec![Type::FieldElement])
                        ),
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
            // a_1 = [if 0 == 1 then 2 else a_0[0], if 1 == 1 then 2 else a_0[1]]

            let mut u = Unroller::new();

            let s: TypedStatement<Bn128Field> =
                TypedStatement::Declaration(Variable::field_array("a", 2));
            assert_eq!(u.fold_statement(s), vec![]);

            let s = TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::field_array("a", 2)),
                ArrayExpressionInner::Value(vec![
                    FieldElementExpression::Number(Bn128Field::from(1)).into(),
                    FieldElementExpression::Number(Bn128Field::from(1)).into(),
                ])
                .annotate(Type::FieldElement, 2)
                .into(),
            );

            assert_eq!(
                u.fold_statement(s),
                vec![TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_array(
                        Identifier::from("a").version(0),
                        2
                    )),
                    ArrayExpressionInner::Value(vec![
                        FieldElementExpression::Number(Bn128Field::from(1)).into(),
                        FieldElementExpression::Number(Bn128Field::from(1)).into()
                    ])
                    .annotate(Type::FieldElement, 2)
                    .into()
                )]
            );

            let s: TypedStatement<Bn128Field> = TypedStatement::Definition(
                TypedAssignee::Select(
                    box TypedAssignee::Identifier(Variable::field_array("a", 2)),
                    box FieldElementExpression::Number(Bn128Field::from(1)),
                ),
                FieldElementExpression::Number(Bn128Field::from(2)).into(),
            );

            assert_eq!(
                u.fold_statement(s),
                vec![
                    TypedStatement::Assertion(
                        BooleanExpression::Lt(
                            box FieldElementExpression::Number(Bn128Field::from(1)),
                            box FieldElementExpression::Number(Bn128Field::from(2))
                        )
                        .into(),
                    ),
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::field_array(
                            Identifier::from("a").version(1),
                            2
                        )),
                        ArrayExpressionInner::Value(vec![
                            FieldElementExpression::IfElse(
                                box BooleanExpression::FieldEq(
                                    box FieldElementExpression::Number(Bn128Field::from(0)),
                                    box FieldElementExpression::Number(Bn128Field::from(1))
                                ),
                                box FieldElementExpression::Number(Bn128Field::from(2)),
                                box FieldElementExpression::Select(
                                    box ArrayExpressionInner::Identifier(
                                        Identifier::from("a").version(0)
                                    )
                                    .annotate(Type::FieldElement, 2),
                                    box FieldElementExpression::Number(Bn128Field::from(0))
                                ),
                            )
                            .into(),
                            FieldElementExpression::IfElse(
                                box BooleanExpression::FieldEq(
                                    box FieldElementExpression::Number(Bn128Field::from(1)),
                                    box FieldElementExpression::Number(Bn128Field::from(1))
                                ),
                                box FieldElementExpression::Number(Bn128Field::from(2)),
                                box FieldElementExpression::Select(
                                    box ArrayExpressionInner::Identifier(
                                        Identifier::from("a").version(0)
                                    )
                                    .annotate(Type::FieldElement, 2),
                                    box FieldElementExpression::Number(Bn128Field::from(1))
                                ),
                            )
                            .into(),
                        ])
                        .annotate(Type::FieldElement, 2)
                        .into()
                    )
                ]
            );
        }

        #[test]
        fn incremental_array_of_arrays_definition() {
            // field[2][2] a = [[0, 1], [2, 3]]
            // a[1] = [4, 5]

            // should be turned into
            // a_0 = [[0, 1], [2, 3]]
            // a_1 = [if 0 == 1 then [4, 5] else a_0[0], if 1 == 1 then [4, 5] else a_0[1]]

            let mut u = Unroller::new();

            let array_of_array_ty = Type::array(Type::array(Type::FieldElement, 2), 2);

            let s: TypedStatement<Bn128Field> = TypedStatement::Declaration(
                Variable::with_id_and_type("a", array_of_array_ty.clone()),
            );
            assert_eq!(u.fold_statement(s), vec![]);

            let s = TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::with_id_and_type(
                    "a",
                    array_of_array_ty.clone(),
                )),
                ArrayExpressionInner::Value(vec![
                    ArrayExpressionInner::Value(vec![
                        FieldElementExpression::Number(Bn128Field::from(0)).into(),
                        FieldElementExpression::Number(Bn128Field::from(1)).into(),
                    ])
                    .annotate(Type::FieldElement, 2)
                    .into(),
                    ArrayExpressionInner::Value(vec![
                        FieldElementExpression::Number(Bn128Field::from(2)).into(),
                        FieldElementExpression::Number(Bn128Field::from(3)).into(),
                    ])
                    .annotate(Type::FieldElement, 2)
                    .into(),
                ])
                .annotate(Type::array(Type::FieldElement, 2), 2)
                .into(),
            );

            assert_eq!(
                u.fold_statement(s),
                vec![TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::with_id_and_type(
                        Identifier::from("a").version(0),
                        array_of_array_ty.clone(),
                    )),
                    ArrayExpressionInner::Value(vec![
                        ArrayExpressionInner::Value(vec![
                            FieldElementExpression::Number(Bn128Field::from(0)).into(),
                            FieldElementExpression::Number(Bn128Field::from(1)).into(),
                        ])
                        .annotate(Type::FieldElement, 2)
                        .into(),
                        ArrayExpressionInner::Value(vec![
                            FieldElementExpression::Number(Bn128Field::from(2)).into(),
                            FieldElementExpression::Number(Bn128Field::from(3)).into(),
                        ])
                        .annotate(Type::FieldElement, 2)
                        .into(),
                    ])
                    .annotate(Type::array(Type::FieldElement, 2), 2)
                    .into(),
                )]
            );

            let s: TypedStatement<Bn128Field> = TypedStatement::Definition(
                TypedAssignee::Select(
                    box TypedAssignee::Identifier(Variable::with_id_and_type(
                        "a",
                        array_of_array_ty.clone(),
                    )),
                    box FieldElementExpression::Number(Bn128Field::from(1)),
                ),
                ArrayExpressionInner::Value(vec![
                    FieldElementExpression::Number(Bn128Field::from(4)).into(),
                    FieldElementExpression::Number(Bn128Field::from(5)).into(),
                ])
                .annotate(Type::FieldElement, 2)
                .into(),
            );

            assert_eq!(
                u.fold_statement(s),
                vec![
                    TypedStatement::Assertion(
                        BooleanExpression::Lt(
                            box FieldElementExpression::Number(Bn128Field::from(1)),
                            box FieldElementExpression::Number(Bn128Field::from(2))
                        )
                        .into(),
                    ),
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::with_id_and_type(
                            Identifier::from("a").version(1),
                            array_of_array_ty.clone()
                        )),
                        ArrayExpressionInner::Value(vec![
                            ArrayExpressionInner::IfElse(
                                box BooleanExpression::FieldEq(
                                    box FieldElementExpression::Number(Bn128Field::from(0)),
                                    box FieldElementExpression::Number(Bn128Field::from(1))
                                ),
                                box ArrayExpressionInner::Value(vec![
                                    FieldElementExpression::Number(Bn128Field::from(4)).into(),
                                    FieldElementExpression::Number(Bn128Field::from(5)).into(),
                                ])
                                .annotate(Type::FieldElement, 2)
                                .into(),
                                box ArrayExpressionInner::Select(
                                    box ArrayExpressionInner::Identifier(
                                        Identifier::from("a").version(0)
                                    )
                                    .annotate(Type::array(Type::FieldElement, 2), 2),
                                    box FieldElementExpression::Number(Bn128Field::from(0))
                                )
                                .annotate(Type::FieldElement, 2),
                            )
                            .annotate(Type::FieldElement, 2)
                            .into(),
                            ArrayExpressionInner::IfElse(
                                box BooleanExpression::FieldEq(
                                    box FieldElementExpression::Number(Bn128Field::from(1)),
                                    box FieldElementExpression::Number(Bn128Field::from(1))
                                ),
                                box ArrayExpressionInner::Value(vec![
                                    FieldElementExpression::Number(Bn128Field::from(4)).into(),
                                    FieldElementExpression::Number(Bn128Field::from(5)).into(),
                                ])
                                .annotate(Type::FieldElement, 2)
                                .into(),
                                box ArrayExpressionInner::Select(
                                    box ArrayExpressionInner::Identifier(
                                        Identifier::from("a").version(0)
                                    )
                                    .annotate(Type::array(Type::FieldElement, 2), 2),
                                    box FieldElementExpression::Number(Bn128Field::from(1))
                                )
                                .annotate(Type::FieldElement, 2),
                            )
                            .annotate(Type::FieldElement, 2)
                            .into(),
                        ])
                        .annotate(Type::array(Type::FieldElement, 2), 2)
                        .into()
                    )
                ]
            );
        }
    }
}
