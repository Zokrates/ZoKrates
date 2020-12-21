//! Module containing SSA reduction, including for-loop unrolling
//!
//! @file unroll.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use crate::typed_absy::folder::*;
use crate::typed_absy::identifier::CoreIdentifier;
use crate::typed_absy::*;
use std::collections::HashMap;
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

                        values
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
                                .flatten()
                            })
                            .flatten()
                            .flat_map(|x| self.fold_statement(x))
                            .collect()
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
            version: *self.substitution.get(&n.id).unwrap_or(&0),
            ..n
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::Bn128Field;

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

            // b = [5]
            // b[0] = 1
            // a = 5
            // a_1 = 6
            // a_2 = 7

            // should be turned into
            // b = [5]
            // b[0] = 1
            // a = 5
            // a_1 = 6
            // a_2 = 7

            let mut u = Unroller::new();

            let s = TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::array(
                    Identifier::from("b").version(0),
                    Type::FieldElement,
                    1,
                )),
                ArrayExpressionInner::Value(vec![FieldElementExpression::from(Bn128Field::from(
                    5,
                ))
                .into()])
                .annotate(Type::FieldElement, 1)
                .into(),
            );
            assert_eq!(u.fold_statement(s.clone()), vec![s]);

            let s = TypedStatement::Definition(
                TypedAssignee::Select(
                    box Variable::field_element(Identifier::from("b").version(0)).into(),
                    box FieldElementExpression::Number(Bn128Field::from(0)),
                ),
                FieldElementExpression::Number(Bn128Field::from(1)).into(),
            );
            assert_eq!(u.fold_statement(s.clone()), vec![s]);

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
    }
}
