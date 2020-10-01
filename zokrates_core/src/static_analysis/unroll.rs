//! Module containing SSA reduction, including for-loop unrolling
//!
//! @file unroll.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use crate::typed_absy::folder::*;
use crate::typed_absy::types::{ConcreteFunctionKey, MemberId, Type};
use crate::typed_absy::*;
use std::collections::HashMap;
use std::collections::HashSet;
use typed_absy::identifier::CoreIdentifier;
use zokrates_field::Field;

use static_analysis::propagate_unroll::{Blocked, Output};

pub struct Unroller<'ast> {
    // version index for any variable name
    substitution: HashMap<
        (
            CoreIdentifier<'ast>,
            Vec<(TypedModuleId, ConcreteFunctionKey<'ast>, usize)>,
        ),
        usize,
    >,
    // whether all statements could be unrolled so far. Loops with variable bounds cannot.
    blocked: Option<Blocked>,
    made_progress: bool,
}

impl<'ast> Unroller<'ast> {
    fn new() -> Self {
        Unroller {
            substitution: HashMap::new(),
            blocked: None,
            made_progress: false,
        }
    }

    fn issue_next_ssa_variable<T: Field>(&mut self, v: Variable<'ast, T>) -> Variable<'ast, T> {
        // let res = match self
        //     .substitution
        //     .get(&(v.id.id.clone(), v.id.stack.clone()))
        // {
        //     Some(i) => Variable {
        //         id: Identifier {
        //             version: i + 1,
        //             ..v.id.clone()
        //         },
        //         ..v
        //     },
        //     None => Variable { ..v.clone() },
        // };

        let version = *self
            .substitution
            .entry((v.id.id.clone(), v.id.stack.clone()))
            .and_modify(|e| *e += 1) // if it was already declared, we increment
            .or_insert(v.id.version); // otherwise, we start from this version

        Variable {
            id: Identifier { version, ..v.id },
            ..v
        }
    }

    pub fn unroll<T: Field>(p: TypedProgram<T>) -> Output<T> {
        let mut unroller = Unroller::new();

        let main_module_id = p.main;

        // get the main module
        let main_module = p.modules.get(&main_module_id).unwrap().clone();

        // get the main function in the main module
        let functions = main_module
            .functions
            .into_iter()
            .map(|(k, f)| {
                if k.id == "main" {
                    // unroll the main function
                    let main = unroller.fold_function_symbol(f);
                    (k, main)
                } else {
                    (k, f)
                }
            })
            .collect();

        let mut modules = p.modules;

        modules.insert("main".into(), TypedModule { functions });

        let p = TypedProgram {
            main: "main".into(),
            modules,
        };

        match unroller.blocked {
            None => Output::Complete(p),
            Some(blocked) => Output::Blocked(p, blocked, unroller.made_progress),
        }
    }

    fn choose_many<T: Field>(
        base: TypedExpression<'ast, T>,
        indices: Vec<Access<'ast, T>>,
        new_expression: TypedExpression<'ast, T>,
        statements: &mut HashSet<TypedStatement<'ast, T>>,
    ) -> TypedExpression<'ast, T> {
        let mut indices = indices;

        match indices.len() {
            0 => new_expression,
            _ => match base {
                TypedExpression::Array(base) => {
                    let inner_ty = base.inner_type();
                    let size = base.size();

                    let head = indices.remove(0);
                    let tail = indices;

                    match head {
                        Access::Select(head) => {
                            statements.insert(TypedStatement::Assertion(
                                BooleanExpression::UintLt(box head.clone(), box size.clone())
                                    .into(),
                            ));

                            match size.into_inner() {
                                UExpressionInner::Value(size) => ArrayExpressionInner::Value(
                                    (0..size as u32)
                                        .map(|i| match inner_ty {
                                            Type::Array(..) => ArrayExpression::if_else(
                                                BooleanExpression::UintEq(
                                                    box i.into(),
                                                    box head.clone(),
                                                ),
                                                match Self::choose_many(
                                                    ArrayExpression::select(base.clone(), i).into(),
                                                    tail.clone(),
                                                    new_expression.clone(),
                                                    statements,
                                                ) {
                                                    TypedExpression::Array(e) => e,
                                                    e => unreachable!(
                                            "the interior was expected to be an array, was {}",
                                            e.get_type()
                                        ),
                                                },
                                                ArrayExpression::select(base.clone(), i),
                                            )
                                            .into(),
                                            Type::Struct(..) => StructExpression::if_else(
                                                BooleanExpression::UintEq(
                                                    box i.into(),
                                                    box head.clone(),
                                                ),
                                                match Self::choose_many(
                                                    StructExpression::select(base.clone(), i)
                                                        .into(),
                                                    tail.clone(),
                                                    new_expression.clone(),
                                                    statements,
                                                ) {
                                                    TypedExpression::Struct(e) => e,
                                                    e => unreachable!(
                                            "the interior was expected to be a struct, was {}",
                                            e.get_type()
                                        ),
                                                },
                                                StructExpression::select(base.clone(), i),
                                            )
                                            .into(),
                                            Type::FieldElement => FieldElementExpression::if_else(
                                                BooleanExpression::UintEq(
                                                    box i.into(),
                                                    box head.clone(),
                                                ),
                                                match Self::choose_many(
                                                    FieldElementExpression::select(base.clone(), i)
                                                        .into(),
                                                    tail.clone(),
                                                    new_expression.clone(),
                                                    statements,
                                                ) {
                                                    TypedExpression::FieldElement(e) => e,
                                                    e => unreachable!(
                                            "the interior was expected to be a field, was {}",
                                            e.get_type()
                                        ),
                                                },
                                                FieldElementExpression::select(base.clone(), i),
                                            )
                                            .into(),
                                            Type::Boolean => BooleanExpression::if_else(
                                                BooleanExpression::UintEq(
                                                    box i.into(),
                                                    box head.clone(),
                                                ),
                                                match Self::choose_many(
                                                    BooleanExpression::select(base.clone(), i)
                                                        .into(),
                                                    tail.clone(),
                                                    new_expression.clone(),
                                                    statements,
                                                ) {
                                                    TypedExpression::Boolean(e) => e,
                                                    e => unreachable!(
                                            "the interior was expected to be a boolean, was {}",
                                            e.get_type()
                                        ),
                                                },
                                                BooleanExpression::select(base.clone(), i),
                                            )
                                            .into(),
                                            Type::Uint(..) => UExpression::if_else(
                                                BooleanExpression::UintEq(
                                                    box i.into(),
                                                    box head.clone(),
                                                ),
                                                match Self::choose_many(
                                                    UExpression::select(base.clone(), i).into(),
                                                    tail.clone(),
                                                    new_expression.clone(),
                                                    statements,
                                                ) {
                                                    TypedExpression::Uint(e) => e,
                                                    e => unreachable!(
                                            "the interior was expected to be a uint, was {}",
                                            e.get_type()
                                        ),
                                                },
                                                UExpression::select(base.clone(), i),
                                            )
                                            .into(),
                                            Type::Int => unreachable!(),
                                        })
                                        .collect(),
                                )
                                .annotate(inner_ty.clone(), size as u32)
                                .into(),
                                _ => unimplemented!(),
                            }
                        }
                        Access::Member(..) => unreachable!("can't get a member from an array"),
                    }
                }
                TypedExpression::Struct(base) => {
                    let members = match base.get_type() {
                        Type::Struct(members) => members.clone(),
                        _ => unreachable!(),
                    };

                    let head = indices.remove(0);
                    let tail = indices;

                    match head {
                        Access::Member(head) => StructExpressionInner::Value(
                            members
                                .clone()
                                .into_iter()
                                .map(|member| match *member.ty {
                                    Type::Int => unreachable!(),
                                    Type::FieldElement => {
                                        if member.id == head {
                                            Self::choose_many(
                                                FieldElementExpression::member(
                                                    base.clone(),
                                                    head.clone(),
                                                )
                                                .into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                            )
                                        } else {
                                            FieldElementExpression::member(
                                                base.clone(),
                                                member.id.clone(),
                                            )
                                            .into()
                                        }
                                    }
                                    Type::Uint(..) => {
                                        if member.id == head {
                                            Self::choose_many(
                                                UExpression::member(base.clone(), head.clone())
                                                    .into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                            )
                                        } else {
                                            UExpression::member(base.clone(), member.id.clone())
                                                .into()
                                        }
                                    }
                                    Type::Boolean => {
                                        if member.id == head {
                                            Self::choose_many(
                                                BooleanExpression::member(
                                                    base.clone(),
                                                    head.clone(),
                                                )
                                                .into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                            )
                                        } else {
                                            BooleanExpression::member(
                                                base.clone(),
                                                member.id.clone(),
                                            )
                                            .into()
                                        }
                                    }
                                    Type::Array(..) => {
                                        if member.id == head {
                                            Self::choose_many(
                                                ArrayExpression::member(base.clone(), head.clone())
                                                    .into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                            )
                                        } else {
                                            ArrayExpression::member(base.clone(), member.id.clone())
                                                .into()
                                        }
                                    }
                                    Type::Struct(..) => {
                                        if member.id == head {
                                            Self::choose_many(
                                                StructExpression::member(
                                                    base.clone(),
                                                    head.clone(),
                                                )
                                                .into(),
                                                tail.clone(),
                                                new_expression.clone(),
                                                statements,
                                            )
                                        } else {
                                            StructExpression::member(
                                                base.clone(),
                                                member.id.clone(),
                                            )
                                            .into()
                                        }
                                    }
                                })
                                .collect(),
                        )
                        .annotate(members)
                        .into(),
                        Access::Select(..) => unreachable!("can't get a element from a struct"),
                    }
                }
                e => unreachable!("can't make an access on a {}", e.get_type()),
            },
        }
    }
}

#[derive(Clone, Debug)]
enum Access<'ast, T: Field> {
    Select(UExpression<'ast, T>),
    Member(MemberId),
}
/// Turn an assignee into its representation as a base variable and a list accesses
/// a[2][3][4] -> (a, [2, 3, 4])
fn linear<'ast, T: Field>(a: TypedAssignee<'ast, T>) -> (Variable<'ast, T>, Vec<Access<'ast, T>>) {
    match a {
        TypedAssignee::Identifier(v) => (v, vec![]),
        TypedAssignee::Select(box array, box index) => {
            let (v, mut indices) = linear(array);
            indices.push(Access::Select(index));
            (v, indices)
        }
        TypedAssignee::Member(box s, m) => {
            let (v, mut indices) = linear(s);
            indices.push(Access::Member(m));
            (v, indices)
        }
    }
}

impl<'ast, T: Field> Folder<'ast, T> for Unroller<'ast> {
    fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        match s {
            TypedStatement::Declaration(_) => vec![],
            TypedStatement::Definition(assignee, expr) => {
                let expr = self.fold_expression(expr);

                let (variable, indices) = linear(assignee);

                let base = match variable.get_type() {
                    Type::Int => unreachable!(),
                    Type::FieldElement => {
                        FieldElementExpression::Identifier(variable.id.clone().into()).into()
                    }
                    Type::Boolean => {
                        BooleanExpression::Identifier(variable.id.clone().into()).into()
                    }
                    Type::Uint(bitwidth) => {
                        UExpressionInner::Identifier(variable.id.clone().into())
                            .annotate(bitwidth)
                            .into()
                    }
                    Type::Array(array_type) => {
                        ArrayExpressionInner::Identifier(variable.id.clone().into())
                            .annotate(*array_type.ty, array_type.size)
                            .into()
                    }
                    Type::Struct(members) => {
                        StructExpressionInner::Identifier(variable.id.clone().into())
                            .annotate(members)
                            .into()
                    }
                };

                let base = self.fold_expression(base);

                let indices = indices
                    .into_iter()
                    .map(|a| match a {
                        Access::Select(i) => Access::Select(self.fold_uint_expression(i)),
                        a => a,
                    })
                    .collect();

                let mut range_checks = HashSet::new();
                let e = Self::choose_many(base, indices, expr, &mut range_checks);

                range_checks
                    .into_iter()
                    .chain(std::iter::once(TypedStatement::Definition(
                        TypedAssignee::Identifier(self.issue_next_ssa_variable(variable)),
                        e,
                    )))
                    .collect()
            }
            TypedStatement::MultipleDefinition(variables, exprs) => {
                let exprs = self.fold_expression_list(exprs);
                let variables = variables
                    .into_iter()
                    .map(|v| self.issue_next_ssa_variable(v))
                    .collect();

                vec![TypedStatement::MultipleDefinition(variables, exprs)]
            }
            TypedStatement::For(v, from, to, stats) => {
                let from = self.fold_uint_expression(from);
                let to = self.fold_uint_expression(to);

                match (from.into_inner(), to.into_inner()) {
                    (UExpressionInner::Value(from), UExpressionInner::Value(to)) => {
                        // if we execute this, it means that we made progress
                        self.made_progress = true;

                        let mut values: Vec<u128> = vec![];
                        let mut current = from;
                        while current < to {
                            values.push(current);
                            current = 1 + current;
                        }

                        let res = values
                            .into_iter()
                            .map(|index| {
                                vec![
                                    vec![
                                        TypedStatement::Declaration(v.clone()),
                                        TypedStatement::Definition(
                                            TypedAssignee::Identifier(v.clone()),
                                            UExpressionInner::Value(index)
                                                .annotate(UBitwidth::B32)
                                                .into(),
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
                        self.blocked = Some(Blocked::Unroll);
                        vec![TypedStatement::For(
                            v,
                            from.annotate(UBitwidth::B32),
                            to.annotate(UBitwidth::B32),
                            stats,
                        )]
                    }
                }
            }
            s => fold_statement(self, s),
        }
    }

    fn fold_function(&mut self, f: TypedFunction<'ast, T>) -> TypedFunction<'ast, T> {
        self.substitution = HashMap::new();
        for arg in &f.arguments {
            assert!(self
                .substitution
                .insert((arg.id.id.id.clone(), arg.id.id.stack.clone()), 0)
                .is_none());
        }

        fold_function(self, f)
    }

    fn fold_name(&mut self, n: Identifier<'ast>) -> Identifier<'ast> {
        let res = Identifier {
            version: self
                .substitution
                .get(&(n.id.clone(), n.stack.clone()))
                .unwrap_or(&0)
                .clone(),
            ..n
        };
        res
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> FieldElementExpression<'ast, T> {
        match e {
            FieldElementExpression::FunctionCall(ref k, _) => {
                if !k.id.starts_with("_") {
                    self.blocked = Some(Blocked::Inline);
                }
            }
            _ => {}
        };

        fold_field_expression(self, e)
    }

    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> BooleanExpression<'ast, T> {
        match e {
            BooleanExpression::FunctionCall(ref k, _) => {
                if !k.id.starts_with("_") {
                    self.blocked = Some(Blocked::Inline);
                }
            }
            _ => {}
        };

        fold_boolean_expression(self, e)
    }

    fn fold_uint_expression_inner(
        &mut self,
        b: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> UExpressionInner<'ast, T> {
        match e {
            UExpressionInner::FunctionCall(ref k, _) => {
                if !k.id.starts_with("_") {
                    self.blocked = Some(Blocked::Inline);
                }
            }
            _ => {}
        };

        fold_uint_expression_inner(self, b, e)
    }

    fn fold_array_expression_inner(
        &mut self,
        ty: &Type<'ast, T>,
        size: UExpression<'ast, T>,
        e: ArrayExpressionInner<'ast, T>,
    ) -> ArrayExpressionInner<'ast, T> {
        match e {
            ArrayExpressionInner::FunctionCall(ref k, _) => {
                if !k.id.starts_with("_") {
                    self.blocked = Some(Blocked::Inline);
                }
            }
            _ => {}
        };

        fold_array_expression_inner(self, ty, size, e)
    }

    fn fold_struct_expression_inner(
        &mut self,
        ty: &StructType<'ast, T>,
        e: StructExpressionInner<'ast, T>,
    ) -> StructExpressionInner<'ast, T> {
        match e {
            StructExpressionInner::FunctionCall(ref k, _) => {
                if !k.id.starts_with("_") {
                    self.blocked = Some(Blocked::Inline);
                }
            }
            _ => {}
        };

        fold_struct_expression_inner(self, ty, e)
    }

    fn fold_expression_list(
        &mut self,
        e: TypedExpressionList<'ast, T>,
    ) -> TypedExpressionList<'ast, T> {
        match e {
            TypedExpressionList::FunctionCall(ref k, _, _) => {
                if !k.id.starts_with("_") {
                    self.blocked = Some(Blocked::Inline);
                }
            }
        };

        fold_expression_list(self, e)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::Bn128Field;

    #[test]
    fn ssa_array() {
        let a0 = ArrayExpressionInner::Identifier("a".into()).annotate(Type::FieldElement, 3u32);

        let e = FieldElementExpression::Number(Bn128Field::from(42)).into();

        let index = 1u32.into();

        let a1 = Unroller::choose_many(
            a0.clone().into(),
            vec![Access::Select(index)],
            e,
            &mut HashSet::new(),
        );

        // a[1] = 42
        // -> a = [0 == 1 ? 42 : a[0], 1 == 1 ? 42 : a[1], 2 == 1 ? 42 : a[2]]

        assert_eq!(
            a1,
            ArrayExpressionInner::Value(vec![
                FieldElementExpression::if_else(
                    BooleanExpression::UintEq(box 0u32.into(), box 1u32.into()),
                    FieldElementExpression::Number(Bn128Field::from(42)),
                    FieldElementExpression::select(a0.clone(), 0u32)
                )
                .into(),
                FieldElementExpression::if_else(
                    BooleanExpression::UintEq(box 1u32.into(), box 1u32.into()),
                    FieldElementExpression::Number(Bn128Field::from(42)),
                    FieldElementExpression::select(a0.clone(), 1u32)
                )
                .into(),
                FieldElementExpression::if_else(
                    BooleanExpression::UintEq(box 2u32.into(), box 1u32.into()),
                    FieldElementExpression::Number(Bn128Field::from(42)),
                    FieldElementExpression::select(a0.clone(), 2u32)
                )
                .into()
            ])
            .annotate(Type::FieldElement, 3u32)
            .into()
        );

        let a0: ArrayExpression<Bn128Field> = ArrayExpressionInner::Identifier("a".into())
            .annotate(Type::array(Type::FieldElement, 3u32), 3u32);

        let e = ArrayExpressionInner::Identifier("b".into()).annotate(Type::FieldElement, 3u32);

        let index = 1u32.into();

        let a1 = Unroller::choose_many(
            a0.clone().into(),
            vec![Access::Select(index)],
            e.clone().into(),
            &mut HashSet::new(),
        );

        // a[0] = b
        // -> a = [0 == 1 ? b : a[0], 1 == 1 ? b : a[1], 2 == 1 ? b : a[2]]

        assert_eq!(
            a1,
            ArrayExpressionInner::Value(vec![
                ArrayExpression::if_else(
                    BooleanExpression::UintEq(box 0u32.into(), box 1u32.into()),
                    e.clone(),
                    ArrayExpression::select(a0.clone(), 0u32)
                )
                .into(),
                ArrayExpression::if_else(
                    BooleanExpression::UintEq(box 1u32.into(), box 1u32.into()),
                    e.clone(),
                    ArrayExpression::select(a0.clone(), 1u32)
                )
                .into(),
                ArrayExpression::if_else(
                    BooleanExpression::UintEq(box 2u32.into(), box 1u32.into()),
                    e.clone(),
                    ArrayExpression::select(a0.clone(), 2u32)
                )
                .into()
            ])
            .annotate(Type::array(Type::FieldElement, 3u32), 3u32)
            .into()
        );

        let a0 = ArrayExpressionInner::Identifier("a".into())
            .annotate(Type::array(Type::FieldElement, 2u32), 2u32);

        let e = FieldElementExpression::Number(Bn128Field::from(42));

        let indices = vec![Access::Select(0u32.into()), Access::Select(0u32.into())];

        let a1 = Unroller::choose_many(
            a0.clone().into(),
            indices,
            e.clone().into(),
            &mut HashSet::new(),
        );

        // a[0][0] = 42
        // -> a = [0 == 0 ? [0 == 0 ? 42 : a[0][0], 1 == 0 ? 42 : a[0][1]] : a[0], 1 == 0 ? [0 == 0 ? 42 : a[1][0], 1 == 0 ? 42 : a[1][1]] : a[1]]

        assert_eq!(
            a1,
            ArrayExpressionInner::Value(vec![
                ArrayExpression::if_else(
                    BooleanExpression::UintEq(box 0u32.into(), box 0u32.into()),
                    ArrayExpressionInner::Value(vec![
                        FieldElementExpression::if_else(
                            BooleanExpression::UintEq(box 0u32.into(), box 0u32.into()),
                            e.clone(),
                            FieldElementExpression::select(
                                ArrayExpression::select(a0.clone(), 0u32),
                                0u32
                            )
                        )
                        .into(),
                        FieldElementExpression::if_else(
                            BooleanExpression::UintEq(box 1u32.into(), box 0u32.into()),
                            e.clone(),
                            FieldElementExpression::select(
                                ArrayExpression::select(a0.clone(), 0u32),
                                1u32
                            )
                        )
                        .into()
                    ])
                    .annotate(Type::FieldElement, 2u32),
                    ArrayExpression::select(a0.clone(), 0u32)
                )
                .into(),
                ArrayExpression::if_else(
                    BooleanExpression::UintEq(box 1u32.into(), box 0u32.into()),
                    ArrayExpressionInner::Value(vec![
                        FieldElementExpression::if_else(
                            BooleanExpression::UintEq(box 0u32.into(), box 0u32.into()),
                            e.clone(),
                            FieldElementExpression::select(
                                ArrayExpression::select(a0.clone(), 1u32),
                                0u32
                            )
                        )
                        .into(),
                        FieldElementExpression::if_else(
                            BooleanExpression::UintEq(box 1u32.into(), box 0u32.into()),
                            e.clone(),
                            FieldElementExpression::select(
                                ArrayExpression::select(a0.clone(), 1u32),
                                1u32
                            )
                        )
                        .into()
                    ])
                    .annotate(Type::FieldElement, 2u32),
                    ArrayExpression::select(a0.clone(), 1u32)
                )
                .into(),
            ])
            .annotate(Type::array(Type::FieldElement, 2u32), 2u32)
            .into()
        );
    }

    #[cfg(test)]
    mod statement {
        use super::*;
        use crate::typed_absy::types::{FunctionKey, Signature};
        use typed_absy::types::{DeclarationFunctionKey, DeclarationSignature};

        #[test]
        fn detect_non_constant_bound() {
            let loops: Vec<TypedStatement<Bn128Field>> = vec![TypedStatement::For(
                Variable::uint("i", UBitwidth::B32),
                UExpressionInner::Identifier("i".into()).annotate(UBitwidth::B32),
                2u32.into(),
                vec![],
            )];

            let statements = loops;

            let p = TypedProgram {
                modules: vec![(
                    "main".into(),
                    TypedModule {
                        functions: vec![(
                            DeclarationFunctionKey::with_id("main"),
                            TypedFunctionSymbol::Here(TypedFunction {
                                arguments: vec![],
                                signature: DeclarationSignature::new(),
                                statements,
                            }),
                        )]
                        .into_iter()
                        .collect(),
                    },
                )]
                .into_iter()
                .collect(),
                main: "main".into(),
            };

            match Unroller::unroll(p) {
                Output::Blocked(_, b, made_progress) => {
                    assert_eq!(b, Blocked::Unroll);
                    assert_eq!(made_progress, false);
                }
                _ => unreachable!(),
            };
        }

        #[test]
        fn for_loop() {
            // for u32 i in 2..5
            //		u32 foo = i

            // should be unrolled to
            // i_0 = 2
            // foo_0 = i_0
            // i_1 = 3
            // foo_1 = i_1
            // i_2 = 4
            // foo_2 = i_2

            let s: TypedStatement<Bn128Field> = TypedStatement::For(
                Variable::uint("i", UBitwidth::B32),
                2u32.into(),
                5u32.into(),
                vec![
                    TypedStatement::Declaration(Variable::uint("foo", UBitwidth::B32)),
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::uint("foo", UBitwidth::B32)),
                        UExpressionInner::Identifier("i".into())
                            .annotate(UBitwidth::B32)
                            .into(),
                    ),
                ],
            );

            let expected = vec![
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::uint(
                        Identifier::from("i").version(0),
                        UBitwidth::B32,
                    )),
                    UExpression::from(2u32).into(),
                ),
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::uint(
                        Identifier::from("foo").version(0),
                        UBitwidth::B32,
                    )),
                    UExpressionInner::Identifier(Identifier::from("i").version(0))
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::uint(
                        Identifier::from("i").version(1),
                        UBitwidth::B32,
                    )),
                    UExpression::from(3u32).into(),
                ),
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::uint(
                        Identifier::from("foo").version(1),
                        UBitwidth::B32,
                    )),
                    UExpressionInner::Identifier(Identifier::from("i").version(1))
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::uint(
                        Identifier::from("i").version(2),
                        UBitwidth::B32,
                    )),
                    UExpression::from(4u32).into(),
                ),
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::uint(
                        Identifier::from("foo").version(2),
                        UBitwidth::B32,
                    )),
                    UExpressionInner::Identifier(Identifier::from("i").version(2))
                        .annotate(UBitwidth::B32)
                        .into(),
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
                vec![Variable::field_element("a")],
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
                    vec![Variable::field_element(Identifier::from("a").version(1))],
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
                TypedStatement::Declaration(Variable::field_array("a", 2u32.into()));
            assert_eq!(u.fold_statement(s), vec![]);

            let s = TypedStatement::Definition(
                TypedAssignee::Identifier(Variable::field_array("a", 2u32.into())),
                ArrayExpressionInner::Value(vec![
                    FieldElementExpression::Number(Bn128Field::from(1)).into(),
                    FieldElementExpression::Number(Bn128Field::from(1)).into(),
                ])
                .annotate(Type::FieldElement, 2u32)
                .into(),
            );

            assert_eq!(
                u.fold_statement(s),
                vec![TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_array(
                        Identifier::from("a").version(0),
                        2u32.into()
                    )),
                    ArrayExpressionInner::Value(vec![
                        FieldElementExpression::Number(Bn128Field::from(1)).into(),
                        FieldElementExpression::Number(Bn128Field::from(1)).into()
                    ])
                    .annotate(Type::FieldElement, 2u32)
                    .into()
                )]
            );

            let s: TypedStatement<Bn128Field> = TypedStatement::Definition(
                TypedAssignee::Select(
                    box TypedAssignee::Identifier(Variable::field_array("a", 2u32.into())),
                    box 1u32.into(),
                ),
                FieldElementExpression::Number(Bn128Field::from(2)).into(),
            );

            assert_eq!(
                u.fold_statement(s),
                vec![
                    TypedStatement::Assertion(
                        BooleanExpression::UintLt(box 1u32.into(), box 2u32.into()).into(),
                    ),
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::field_array(
                            Identifier::from("a").version(1),
                            2u32.into()
                        )),
                        ArrayExpressionInner::Value(vec![
                            FieldElementExpression::IfElse(
                                box BooleanExpression::UintEq(box 0u32.into(), box 1u32.into()),
                                box FieldElementExpression::Number(Bn128Field::from(2)),
                                box FieldElementExpression::Select(
                                    box ArrayExpressionInner::Identifier(
                                        Identifier::from("a").version(0)
                                    )
                                    .annotate(Type::FieldElement, 2u32),
                                    box 0u32.into()
                                ),
                            )
                            .into(),
                            FieldElementExpression::IfElse(
                                box BooleanExpression::UintEq(box 1u32.into(), box 1u32.into()),
                                box FieldElementExpression::Number(Bn128Field::from(2)),
                                box FieldElementExpression::Select(
                                    box ArrayExpressionInner::Identifier(
                                        Identifier::from("a").version(0)
                                    )
                                    .annotate(Type::FieldElement, 2u32),
                                    box 1u32.into()
                                ),
                            )
                            .into(),
                        ])
                        .annotate(Type::FieldElement, 2u32)
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

            let array_of_array_ty = Type::array(Type::array(Type::FieldElement, 2u32), 2u32);

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
                    .annotate(Type::FieldElement, 2u32)
                    .into(),
                    ArrayExpressionInner::Value(vec![
                        FieldElementExpression::Number(Bn128Field::from(2)).into(),
                        FieldElementExpression::Number(Bn128Field::from(3)).into(),
                    ])
                    .annotate(Type::FieldElement, 2u32)
                    .into(),
                ])
                .annotate(Type::array(Type::FieldElement, 2u32), 2u32)
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
                        .annotate(Type::FieldElement, 2u32)
                        .into(),
                        ArrayExpressionInner::Value(vec![
                            FieldElementExpression::Number(Bn128Field::from(2)).into(),
                            FieldElementExpression::Number(Bn128Field::from(3)).into(),
                        ])
                        .annotate(Type::FieldElement, 2u32)
                        .into(),
                    ])
                    .annotate(Type::array(Type::FieldElement, 2u32), 2u32)
                    .into(),
                )]
            );

            let s: TypedStatement<Bn128Field> = TypedStatement::Definition(
                TypedAssignee::Select(
                    box TypedAssignee::Identifier(Variable::with_id_and_type(
                        "a",
                        array_of_array_ty.clone(),
                    )),
                    box 1u32.into(),
                ),
                ArrayExpressionInner::Value(vec![
                    FieldElementExpression::Number(Bn128Field::from(4)).into(),
                    FieldElementExpression::Number(Bn128Field::from(5)).into(),
                ])
                .annotate(Type::FieldElement, 2u32)
                .into(),
            );

            assert_eq!(
                u.fold_statement(s),
                vec![
                    TypedStatement::Assertion(
                        BooleanExpression::UintLt(box 1u32.into(), box 2u32.into()).into(),
                    ),
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::with_id_and_type(
                            Identifier::from("a").version(1),
                            array_of_array_ty.clone()
                        )),
                        ArrayExpressionInner::Value(vec![
                            ArrayExpressionInner::IfElse(
                                box BooleanExpression::UintEq(box 0u32.into(), box 1u32.into()),
                                box ArrayExpressionInner::Value(vec![
                                    FieldElementExpression::Number(Bn128Field::from(4)).into(),
                                    FieldElementExpression::Number(Bn128Field::from(5)).into(),
                                ])
                                .annotate(Type::FieldElement, 2u32)
                                .into(),
                                box ArrayExpressionInner::Select(
                                    box ArrayExpressionInner::Identifier(
                                        Identifier::from("a").version(0)
                                    )
                                    .annotate(Type::array(Type::FieldElement, 2u32), 2u32),
                                    box 0u32.into()
                                )
                                .annotate(Type::FieldElement, 2u32),
                            )
                            .annotate(Type::FieldElement, 2u32)
                            .into(),
                            ArrayExpressionInner::IfElse(
                                box BooleanExpression::UintEq(box 1u32.into(), box 1u32.into()),
                                box ArrayExpressionInner::Value(vec![
                                    FieldElementExpression::Number(Bn128Field::from(4)).into(),
                                    FieldElementExpression::Number(Bn128Field::from(5)).into(),
                                ])
                                .annotate(Type::FieldElement, 2u32)
                                .into(),
                                box ArrayExpressionInner::Select(
                                    box ArrayExpressionInner::Identifier(
                                        Identifier::from("a").version(0)
                                    )
                                    .annotate(Type::array(Type::FieldElement, 2u32), 2u32),
                                    box 1u32.into()
                                )
                                .annotate(Type::FieldElement, 2u32),
                            )
                            .annotate(Type::FieldElement, 2u32)
                            .into(),
                        ])
                        .annotate(Type::array(Type::FieldElement, 2u32), 2u32)
                        .into()
                    )
                ]
            );
        }
    }
}
