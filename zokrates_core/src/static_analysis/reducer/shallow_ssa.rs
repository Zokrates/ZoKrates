// Our SSA transformation leaves gaps in the indices when it hits a for-loop, so that the body of the for-loop can
// modify the variables in scope. The state of the indices is saved in an internal statement to account for that possibility.
// Function calls are also left unvisited
// Such a mechanism is not required for function calls, as they cannot modify their environment

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
//      field b_0 = foo(a_1) // we keep the function call
//		# versions: {n: 0, a: 1, b: 0}
// 		for u32 i_0 in 0..n_0:
//			<body> // we keep the loop body
//		endfor
//		return b_3 // we leave versions b_1 and b_2 to make b accessible and modifiable inside the for-loop

use crate::typed_absy::folder::*;
use crate::typed_absy::types::{MemberId, Type};
use crate::typed_absy::*;
use std::collections::HashMap;
use std::collections::HashSet;
use zokrates_field::Field;

use super::{Output, Versions};

pub struct ShallowTransformer<'ast> {
    // version index for any variable name
    versions: Versions<'ast>,
    // A backup of the versions before each for-loop
    for_loop_backups: Vec<Versions<'ast>>,
    // whether all statements could be unrolled so far. Loops with variable bounds cannot.
    blocked: bool,
}

impl<'ast> ShallowTransformer<'ast> {
    fn new() -> Self {
        ShallowTransformer {
            versions: Versions::default(),
            for_loop_backups: vec![],
            blocked: false,
        }
    }

    // increase all versions by 2 and return the old versions
    fn create_version_gap(&mut self) -> Versions<'ast> {
        let ret = self.versions.clone();
        self.versions.values_mut().for_each(|v| *v = *v + 2);
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

    pub fn transform<T: Field>(f: TypedFunction<T>) -> Output<T> {
        let mut unroller = ShallowTransformer::new();

        let f = unroller.fold_function(f);

        match unroller.blocked {
            false => Output::Complete(f),
            true => Output::Incomplete(f, unroller.for_loop_backups, unroller.versions),
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

impl<'ast, T: Field> Folder<'ast, T> for ShallowTransformer<'ast> {
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
                self.blocked = true;
                let versions_before_loop = self.create_version_gap();
                self.for_loop_backups.push(versions_before_loop);
                vec![TypedStatement::For(v, from, to, stats)]
            }
            s => fold_statement(self, s),
        }
    }

    fn fold_function(&mut self, f: TypedFunction<'ast, T>) -> TypedFunction<'ast, T> {
        self.versions = HashMap::new();
        for arg in &f.arguments {
            assert!(self.versions.insert(arg.id.id.id.clone(), 0).is_none());
        }

        fold_function(self, f)
    }

    fn fold_name(&mut self, n: Identifier<'ast>) -> Identifier<'ast> {
        let res = Identifier {
            version: self.versions.get(&(n.id.clone())).unwrap_or(&0).clone(),
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
                    self.blocked = true;
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
                    self.blocked = true;
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
                    self.blocked = true;
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
                    self.blocked = true;
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
                    self.blocked = true;
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
                    self.blocked = true;
                }
            }
        };

        fold_expression_list(self, e)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typed_absy::types::{FunctionKey, Signature};
    use typed_absy::types::DeclarationSignature;
    use zokrates_field::Bn128Field;
    mod normal {
        use super::*;

        #[test]
        fn ssa_array() {
            let a0 =
                ArrayExpressionInner::Identifier("a".into()).annotate(Type::FieldElement, 3u32);

            let e = FieldElementExpression::Number(Bn128Field::from(42)).into();

            let index = 1u32.into();

            let a1 = ShallowTransformer::choose_many(
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

            let a1 = ShallowTransformer::choose_many(
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

            let a1 = ShallowTransformer::choose_many(
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

            match ShallowTransformer::transform(f) {
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

            let mut u = ShallowTransformer::new();

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

            let mut u = ShallowTransformer::new();

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

            let mut u = ShallowTransformer::new();

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

            let mut u = ShallowTransformer::new();

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

            let mut u = ShallowTransformer::new();

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

    mod for_loop {
        use super::*;
        #[test]
        fn treat_loop() {
            // def main(field a) -> field:
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

            // Expected
            // def main(field a_0) -> field:
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
                        UExpressionInner::Identifier("n".into())
                            .annotate(UBitwidth::B32)
                            .into(),
                        UExpression::mult(
                            UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32),
                            UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32),
                        )
                        .into(),
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
                        UExpressionInner::Identifier("n".into())
                            .annotate(UBitwidth::B32)
                            .into(),
                        UExpression::mult(
                            UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32),
                            UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32),
                        )
                        .into(),
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
                    .inputs(vec![DeclarationType::FieldElement])
                    .outputs(vec![DeclarationType::FieldElement]),
            };

            let ssa = ShallowTransformer::transform(f);

            let expected = TypedFunction {
                arguments: vec![DeclarationVariable::field_element("a").into()],
                statements: vec![
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
                        UExpressionInner::Identifier("n".into())
                            .annotate(UBitwidth::B32)
                            .into(),
                        UExpression::mult(
                            UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32),
                            UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32),
                        )
                        .into(),
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
                        UExpressionInner::Identifier("n".into())
                            .annotate(UBitwidth::B32)
                            .into(),
                        UExpression::mult(
                            UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32),
                            UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32),
                        )
                        .into(),
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
                    .inputs(vec![DeclarationType::FieldElement])
                    .outputs(vec![DeclarationType::FieldElement]),
            };

            assert_eq!(
                ssa,
                Output::Incomplete(
                    expected,
                    vec![
                        vec![("n".into(), 1), ("a".into(), 1)]
                            .into_iter()
                            .collect::<Versions>(),
                        vec![("n".into(), 3), ("a".into(), 4)]
                            .into_iter()
                            .collect::<Versions>()
                    ],
                    vec![("n".into(), 5), ("a".into(), 7)]
                        .into_iter()
                        .collect::<Versions>()
                )
            );
        }
    }

    mod function_call {
        use super::*;
        // test that function calls are left in
        #[test]
        fn treat_calls() {
            // def main(field a) -> field:
            //      u32 n = 42
            //      n = n
            //      a = a
            //      a = foo::<n>(a)
            //      n = n
            //      a = a * foo::<n>(a)
            //      return a

            // Expected
            // def main(field a_0) -> field:
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
                            FunctionKey::with_id("foo"),
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
                        FieldElementExpression::mult(
                            FieldElementExpression::Identifier("a".into()),
                            FieldElementExpression::FunctionCall(
                                FunctionKey::with_id("foo"),
                                vec![FieldElementExpression::Identifier("a".into()).into()],
                            ),
                        )
                        .into(),
                    ),
                    TypedStatement::Return(vec![
                        FieldElementExpression::Identifier("a".into()).into()
                    ]),
                ],
                signature: DeclarationSignature::new()
                    .inputs(vec![DeclarationType::FieldElement])
                    .outputs(vec![DeclarationType::FieldElement]),
            };

            let ssa = ShallowTransformer::transform(f);

            let expected = TypedFunction {
                arguments: vec![DeclarationVariable::field_element("a").into()],
                statements: vec![
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
                            FunctionKey::with_id("foo"),
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
                        FieldElementExpression::mult(
                            FieldElementExpression::Identifier(Identifier::from("a").version(2)),
                            FieldElementExpression::FunctionCall(
                                FunctionKey::with_id("foo"),
                                vec![FieldElementExpression::Identifier(
                                    Identifier::from("a").version(2),
                                )
                                .into()],
                            ),
                        )
                        .into(),
                    ),
                    TypedStatement::Return(vec![FieldElementExpression::Identifier(
                        Identifier::from("a").version(3),
                    )
                    .into()]),
                ],
                signature: DeclarationSignature::new()
                    .inputs(vec![DeclarationType::FieldElement])
                    .outputs(vec![DeclarationType::FieldElement]),
            };

            assert_eq!(
                ssa,
                Output::Incomplete(
                    expected,
                    vec![],
                    vec![("n".into(), 2), ("a".into(), 3)]
                        .into_iter()
                        .collect::<Versions>()
                )
            );
        }
    }
}
