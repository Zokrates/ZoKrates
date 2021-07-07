use crate::typed_absy::types::UBitwidth;
use crate::typed_absy::{self, Expr};
use crate::zir;
use std::marker::PhantomData;
use zokrates_field::Field;

use std::convert::{TryFrom, TryInto};

#[derive(Default)]
pub struct Flattener<T: Field> {
    phantom: PhantomData<T>,
}

fn flatten_identifier_rec<'ast>(
    id: zir::SourceIdentifier<'ast>,
    ty: &typed_absy::types::ConcreteType,
) -> Vec<zir::Variable<'ast>> {
    match ty {
        typed_absy::ConcreteType::Int => unreachable!(),
        typed_absy::ConcreteType::FieldElement => vec![zir::Variable {
            id: zir::Identifier::Source(id),
            _type: zir::Type::FieldElement,
        }],
        typed_absy::types::ConcreteType::Boolean => vec![zir::Variable {
            id: zir::Identifier::Source(id),
            _type: zir::Type::Boolean,
        }],
        typed_absy::types::ConcreteType::Uint(bitwidth) => vec![zir::Variable {
            id: zir::Identifier::Source(id),
            _type: zir::Type::uint(bitwidth.to_usize()),
        }],
        typed_absy::types::ConcreteType::Array(array_type) => (0..array_type.size)
            .flat_map(|i| {
                flatten_identifier_rec(
                    zir::SourceIdentifier::Select(box id.clone(), i),
                    &array_type.ty,
                )
            })
            .collect(),
        typed_absy::types::ConcreteType::Struct(members) => members
            .iter()
            .flat_map(|struct_member| {
                flatten_identifier_rec(
                    zir::SourceIdentifier::Member(box id.clone(), struct_member.id.clone()),
                    &struct_member.ty,
                )
            })
            .collect(),
    }
}

trait Flatten<'ast, T: Field> {
    fn flatten(
        self,
        f: &mut Flattener<T>,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    ) -> Vec<zir::ZirExpression<'ast, T>>;
}

impl<'ast, T: Field> Flatten<'ast, T> for typed_absy::FieldElementExpression<'ast, T> {
    fn flatten(
        self,
        f: &mut Flattener<T>,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        vec![f.fold_field_expression(statements_buffer, self).into()]
    }
}

impl<'ast, T: Field> Flatten<'ast, T> for typed_absy::BooleanExpression<'ast, T> {
    fn flatten(
        self,
        f: &mut Flattener<T>,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        vec![f.fold_boolean_expression(statements_buffer, self).into()]
    }
}

impl<'ast, T: Field> Flatten<'ast, T> for typed_absy::UExpression<'ast, T> {
    fn flatten(
        self,
        f: &mut Flattener<T>,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        vec![f.fold_uint_expression(statements_buffer, self).into()]
    }
}

impl<'ast, T: Field> Flatten<'ast, T> for typed_absy::ArrayExpression<'ast, T> {
    fn flatten(
        self,
        f: &mut Flattener<T>,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        f.fold_array_expression(statements_buffer, self)
    }
}

impl<'ast, T: Field> Flatten<'ast, T> for typed_absy::StructExpression<'ast, T> {
    fn flatten(
        self,
        f: &mut Flattener<T>,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        f.fold_struct_expression(statements_buffer, self)
    }
}

impl<'ast, T: Field> Flattener<T> {
    pub fn flatten(p: typed_absy::TypedProgram<T>) -> zir::ZirProgram<T> {
        let mut f = Flattener::default();
        f.fold_program(p)
    }

    fn fold_program(&mut self, p: typed_absy::TypedProgram<'ast, T>) -> zir::ZirProgram<'ast, T> {
        fold_program(self, p)
    }

    fn fold_function(
        &mut self,
        f: typed_absy::TypedFunction<'ast, T>,
    ) -> zir::ZirFunction<'ast, T> {
        fold_function(self, f)
    }

    fn fold_declaration_parameter(
        &mut self,
        p: typed_absy::DeclarationParameter<'ast>,
    ) -> Vec<zir::Parameter<'ast>> {
        let private = p.private;
        self.fold_variable(p.id.try_into().unwrap())
            .into_iter()
            .map(|v| zir::Parameter { id: v, private })
            .collect()
    }

    fn fold_name(&mut self, n: typed_absy::Identifier<'ast>) -> zir::SourceIdentifier<'ast> {
        zir::SourceIdentifier::Basic(n)
    }

    fn fold_variable(&mut self, v: typed_absy::Variable<'ast, T>) -> Vec<zir::Variable<'ast>> {
        let ty = v.get_type();
        let id = self.fold_name(v.id);

        let ty = typed_absy::types::ConcreteType::try_from(ty).unwrap();

        flatten_identifier_rec(id, &ty)
    }

    fn fold_assignee(
        &mut self,
        a: typed_absy::TypedAssignee<'ast, T>,
    ) -> Vec<zir::ZirAssignee<'ast>> {
        match a {
            typed_absy::TypedAssignee::Identifier(v) => self.fold_variable(v),
            typed_absy::TypedAssignee::Select(box a, box i) => {
                use typed_absy::Typed;
                let count = match typed_absy::ConcreteType::try_from(a.get_type()).unwrap() {
                    typed_absy::ConcreteType::Array(array_ty) => array_ty.ty.get_primitive_count(),
                    _ => unreachable!(),
                };
                let a = self.fold_assignee(a);

                match i.as_inner() {
                    typed_absy::UExpressionInner::Value(index) => {
                        a[*index as usize * count..(*index as usize + 1) * count].to_vec()
                    }
                    i => unreachable!("index {:?} not allowed, should be a constant", i),
                }
            }
            typed_absy::TypedAssignee::Member(box a, m) => {
                use typed_absy::Typed;

                let (offset, size) = match typed_absy::ConcreteType::try_from(a.get_type()).unwrap()
                {
                    typed_absy::ConcreteType::Struct(struct_type) => struct_type
                        .members
                        .iter()
                        .fold((0, None), |(offset, size), member| match size {
                            Some(_) => (offset, size),
                            None => match m == member.id {
                                true => (offset, Some(member.ty.get_primitive_count())),
                                false => (offset + member.ty.get_primitive_count(), None),
                            },
                        }),
                    _ => unreachable!(),
                };

                let size = size.unwrap();

                let a = self.fold_assignee(a);

                a[offset..offset + size].to_vec()
            }
        }
    }

    fn fold_statement(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        s: typed_absy::TypedStatement<'ast, T>,
    ) {
        fold_statement(self, statements_buffer, s)
    }

    fn fold_expression_or_spread(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        e: typed_absy::TypedExpressionOrSpread<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        match e {
            typed_absy::TypedExpressionOrSpread::Expression(e) => {
                self.fold_expression(statements_buffer, e)
            }
            typed_absy::TypedExpressionOrSpread::Spread(s) => {
                self.fold_array_expression(statements_buffer, s.array)
            }
        }
    }

    fn fold_expression(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        e: typed_absy::TypedExpression<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        match e {
            typed_absy::TypedExpression::FieldElement(e) => {
                vec![self.fold_field_expression(statements_buffer, e).into()]
            }
            typed_absy::TypedExpression::Boolean(e) => {
                vec![self.fold_boolean_expression(statements_buffer, e).into()]
            }
            typed_absy::TypedExpression::Uint(e) => {
                vec![self.fold_uint_expression(statements_buffer, e).into()]
            }
            typed_absy::TypedExpression::Array(e) => {
                self.fold_array_expression(statements_buffer, e)
            }
            typed_absy::TypedExpression::Struct(e) => {
                self.fold_struct_expression(statements_buffer, e)
            }
            typed_absy::TypedExpression::Int(_) => unreachable!(),
        }
    }

    fn fold_identifier_expression<E: Expr<'ast, T>>(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        ty: &E::ConcreteTy,
        e: typed_absy::IdentifierExpression<'ast, E>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_identifier_expression::<T, E>(self, statements_buffer, ty, e)
    }

    fn fold_array_expression(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        e: typed_absy::ArrayExpression<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_array_expression(self, statements_buffer, e)
    }

    fn fold_struct_expression(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,

        e: typed_absy::StructExpression<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_struct_expression(self, statements_buffer, e)
    }

    fn fold_expression_list(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        es: typed_absy::TypedExpressionList<'ast, T>,
    ) -> zir::ZirExpressionList<'ast, T> {
        match es.into_inner() {
            typed_absy::TypedExpressionListInner::EmbedCall(embed, generics, arguments) => {
                zir::ZirExpressionList::EmbedCall(
                    embed,
                    generics,
                    arguments
                        .into_iter()
                        .flat_map(|a| self.fold_expression(statements_buffer, a))
                        .collect(),
                )
            }
            _ => unreachable!("should have been inlined"),
        }
    }

    fn fold_if_else_expression<E: Flatten<'ast, T>>(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        c: typed_absy::IfElseExpression<'ast, T, E>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_if_else_expression(self, statements_buffer, c)
    }

    fn fold_member_expression<E>(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        m: typed_absy::MemberExpression<'ast, T, E>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_member_expression(self, statements_buffer, m)
    }

    fn fold_select_expression<E>(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        select: typed_absy::SelectExpression<'ast, T, E>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_select_expression(self, statements_buffer, select)
    }

    fn fold_field_expression(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        e: typed_absy::FieldElementExpression<'ast, T>,
    ) -> zir::FieldElementExpression<'ast, T> {
        fold_field_expression(self, statements_buffer, e)
    }
    fn fold_boolean_expression(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        e: typed_absy::BooleanExpression<'ast, T>,
    ) -> zir::BooleanExpression<'ast, T> {
        fold_boolean_expression(self, statements_buffer, e)
    }
    fn fold_uint_expression(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        e: typed_absy::UExpression<'ast, T>,
    ) -> zir::UExpression<'ast, T> {
        fold_uint_expression(self, statements_buffer, e)
    }

    fn fold_uint_expression_inner(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        bitwidth: UBitwidth,
        e: typed_absy::UExpressionInner<'ast, T>,
    ) -> zir::UExpressionInner<'ast, T> {
        fold_uint_expression_inner(self, statements_buffer, bitwidth, e)
    }

    fn fold_array_expression_inner(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        ty: &typed_absy::types::ConcreteArrayType,
        e: typed_absy::ArrayExpressionInner<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_array_expression_inner(self, statements_buffer, ty, e)
    }
    fn fold_struct_expression_inner(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        ty: &typed_absy::types::ConcreteStructType,
        e: typed_absy::StructExpressionInner<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_struct_expression_inner(self, statements_buffer, ty, e)
    }
}

fn fold_statement<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    s: typed_absy::TypedStatement<'ast, T>,
) {
    let res = match s {
        typed_absy::TypedStatement::Return(expressions) => vec![zir::ZirStatement::Return(
            expressions
                .into_iter()
                .flat_map(|e| f.fold_expression(statements_buffer, e))
                .collect(),
        )],
        typed_absy::TypedStatement::Definition(a, e) => {
            let a = f.fold_assignee(a);
            let e = f.fold_expression(statements_buffer, e);
            assert_eq!(a.len(), e.len());
            a.into_iter()
                .zip(e.into_iter())
                .map(|(a, e)| zir::ZirStatement::Definition(a, e))
                .collect()
        }
        typed_absy::TypedStatement::Declaration(..) => {
            unreachable!()
        }
        typed_absy::TypedStatement::Assertion(e) => {
            let e = f.fold_boolean_expression(statements_buffer, e);
            vec![zir::ZirStatement::Assertion(e)]
        }
        typed_absy::TypedStatement::For(..) => unreachable!(),
        typed_absy::TypedStatement::MultipleDefinition(variables, elist) => {
            vec![zir::ZirStatement::MultipleDefinition(
                variables
                    .into_iter()
                    .flat_map(|v| f.fold_assignee(v))
                    .collect(),
                f.fold_expression_list(statements_buffer, elist),
            )]
        }
        typed_absy::TypedStatement::PushCallLog(..) => vec![],
        typed_absy::TypedStatement::PopCallLog => vec![],
    };

    statements_buffer.extend(res);
}

fn fold_array_expression_inner<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    ty: &typed_absy::types::ConcreteArrayType,
    array: typed_absy::ArrayExpressionInner<'ast, T>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    match array {
        typed_absy::ArrayExpressionInner::Block(block) => {
            block
                .statements
                .into_iter()
                .for_each(|s| f.fold_statement(statements_buffer, s));
            f.fold_array_expression(statements_buffer, *block.value)
        }
        typed_absy::ArrayExpressionInner::Identifier(id) => {
            f.fold_identifier_expression(statements_buffer, ty, id)
        }
        typed_absy::ArrayExpressionInner::Value(exprs) => {
            let exprs: Vec<_> = exprs
                .into_iter()
                .flat_map(|e| f.fold_expression_or_spread(statements_buffer, e))
                .collect();

            assert_eq!(exprs.len(), ty.size * ty.ty.get_primitive_count());

            exprs
        }
        typed_absy::ArrayExpressionInner::FunctionCall(..) => unreachable!(),
        typed_absy::ArrayExpressionInner::IfElse(c) => {
            f.fold_if_else_expression(statements_buffer, c)
        }
        typed_absy::ArrayExpressionInner::Member(m) => {
            f.fold_member_expression(statements_buffer, m)
        }
        typed_absy::ArrayExpressionInner::Select(select) => {
            f.fold_select_expression(statements_buffer, select)
        }
        typed_absy::ArrayExpressionInner::Slice(box array, box from, box to) => {
            let array = f.fold_array_expression(statements_buffer, array);
            let from = f.fold_uint_expression(statements_buffer, from);
            let to = f.fold_uint_expression(statements_buffer, to);

            match (from.into_inner(), to.into_inner()) {
                (zir::UExpressionInner::Value(from), zir::UExpressionInner::Value(to)) => {
                    assert_eq!(ty.size, to.saturating_sub(from) as usize);

                    let element_size = ty.ty.get_primitive_count();
                    let start = from as usize * element_size;
                    let end = to as usize * element_size;
                    array[start..end].to_vec()
                }
                _ => unreachable!(),
            }
        }
        typed_absy::ArrayExpressionInner::Repeat(box e, box count) => {
            let e = f.fold_expression(statements_buffer, e);
            let count = f.fold_uint_expression(statements_buffer, count);

            match count.into_inner() {
                zir::UExpressionInner::Value(count) => {
                    vec![e; count as usize].into_iter().flatten().collect()
                }
                _ => unreachable!(),
            }
        }
    }
}

fn fold_struct_expression_inner<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    ty: &typed_absy::types::ConcreteStructType,
    struc: typed_absy::StructExpressionInner<'ast, T>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    match struc {
        typed_absy::StructExpressionInner::Block(block) => {
            block
                .statements
                .into_iter()
                .for_each(|s| f.fold_statement(statements_buffer, s));
            f.fold_struct_expression(statements_buffer, *block.value)
        }
        typed_absy::StructExpressionInner::Identifier(id) => {
            f.fold_identifier_expression(statements_buffer, ty, id)
        }
        typed_absy::StructExpressionInner::Value(exprs) => exprs
            .into_iter()
            .flat_map(|e| f.fold_expression(statements_buffer, e))
            .collect(),
        typed_absy::StructExpressionInner::FunctionCall(..) => unreachable!(),
        typed_absy::StructExpressionInner::IfElse(c) => {
            f.fold_if_else_expression(statements_buffer, c)
        }
        typed_absy::StructExpressionInner::Member(m) => {
            f.fold_member_expression(statements_buffer, m)
        }
        typed_absy::StructExpressionInner::Select(select) => {
            f.fold_select_expression(statements_buffer, select)
        }
    }
}

fn fold_member_expression<'ast, T: Field, E>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    m: typed_absy::MemberExpression<'ast, T, E>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    let s = *m.struc;
    let id = m.id;

    let members = s.ty();

    let size = typed_absy::types::ConcreteType::try_from(
        *members
            .iter()
            .find(|member| member.id == id)
            .unwrap()
            .ty
            .clone(),
    )
    .unwrap()
    .get_primitive_count();

    let offset: usize = members
        .iter()
        .take_while(|member| member.id != id)
        .map(|member| {
            typed_absy::types::ConcreteType::try_from(*member.ty.clone())
                .unwrap()
                .get_primitive_count()
        })
        .sum();

    let s = f.fold_struct_expression(statements_buffer, s);

    s[offset..offset + size].to_vec()
}

fn fold_select_expression<'ast, T: Field, E>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    select: typed_absy::SelectExpression<'ast, T, E>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    let size = typed_absy::types::ConcreteType::try_from(*select.array.ty().ty)
        .unwrap()
        .get_primitive_count();

    let array = f.fold_array_expression(statements_buffer, *select.array);
    let index = f.fold_uint_expression(statements_buffer, *select.index);

    match index.as_inner() {
        zir::UExpressionInner::Value(v) => {
            let v = *v as usize;

            array[v * size..(v + 1) * size].to_vec()
        }
        _ => array
            .chunks(size)
            .fold(vec![vec![]; size], |mut acc, e| {
                acc = acc
                    .into_iter()
                    .zip(e)
                    .map(|(mut a, e)| {
                        a.push(e);
                        a
                    })
                    .collect();
                acc
            })
            .into_iter()
            .map(|a| {
                use crate::zir::Typed;

                let ty = a[0].get_type();

                match ty {
                    zir::Type::Boolean => zir::BooleanExpression::Select(
                        a.into_iter()
                            .map(|e| match e {
                                zir::ZirExpression::Boolean(e) => e.clone(),
                                _ => unreachable!(),
                            })
                            .collect(),
                        box index.clone(),
                    )
                    .into(),
                    zir::Type::FieldElement => zir::FieldElementExpression::Select(
                        a.into_iter()
                            .map(|e| match e {
                                zir::ZirExpression::FieldElement(e) => e.clone(),
                                _ => unreachable!(),
                            })
                            .collect(),
                        box index.clone(),
                    )
                    .into(),
                    zir::Type::Uint(bitwidth) => zir::UExpressionInner::Select(
                        a.into_iter()
                            .map(|e| match e {
                                zir::ZirExpression::Uint(e) => e.clone(),
                                _ => unreachable!(),
                            })
                            .collect(),
                        box index.clone(),
                    )
                    .annotate(bitwidth)
                    .into(),
                }
            })
            .collect(),
    }
}

fn fold_if_else_expression<'ast, T: Field, E: Flatten<'ast, T>>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    c: typed_absy::IfElseExpression<'ast, T, E>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    let mut consequence_statements = vec![];
    let mut alternative_statements = vec![];

    let condition = f.fold_boolean_expression(statements_buffer, *c.condition);
    let consequence = c.consequence.flatten(f, &mut consequence_statements);
    let alternative = c.alternative.flatten(f, &mut alternative_statements);

    assert_eq!(consequence.len(), alternative.len());

    if !consequence_statements.is_empty() || !alternative_statements.is_empty() {
        statements_buffer.push(zir::ZirStatement::IfElse(
            condition.clone(),
            consequence_statements,
            alternative_statements,
        ));
    }

    use crate::zir::IfElse;

    consequence
        .into_iter()
        .zip(alternative.into_iter())
        .map(|(c, a)| match (c, a) {
            (zir::ZirExpression::FieldElement(c), zir::ZirExpression::FieldElement(a)) => {
                zir::FieldElementExpression::if_else(condition.clone(), c, a).into()
            }
            (zir::ZirExpression::Boolean(c), zir::ZirExpression::Boolean(a)) => {
                zir::BooleanExpression::if_else(condition.clone(), c, a).into()
            }
            (zir::ZirExpression::Uint(c), zir::ZirExpression::Uint(a)) => {
                zir::UExpression::if_else(condition.clone(), c, a).into()
            }
            _ => unreachable!(),
        })
        .collect()
}

fn fold_identifier_expression<'ast, T: Field, E: Expr<'ast, T>>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    ty: &E::ConcreteTy,
    e: typed_absy::IdentifierExpression<'ast, E>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    unimplemented!()
    // flatten_identifier_rec(
    //     f.fold_name(e.id),
    //     ty.clone(),
    // )
}

fn fold_field_expression<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    e: typed_absy::FieldElementExpression<'ast, T>,
) -> zir::FieldElementExpression<'ast, T> {
    match e {
        typed_absy::FieldElementExpression::Number(n) => zir::FieldElementExpression::Number(n),
        typed_absy::FieldElementExpression::Identifier(id) => f
            .fold_identifier_expression(
                statements_buffer,
                &typed_absy::ConcreteType::FieldElement,
                id,
            )
            .pop()
            .unwrap()
            .try_into()
            .unwrap(),
        typed_absy::FieldElementExpression::Add(box e1, box e2) => {
            let e1 = f.fold_field_expression(statements_buffer, e1);
            let e2 = f.fold_field_expression(statements_buffer, e2);
            zir::FieldElementExpression::Add(box e1, box e2)
        }
        typed_absy::FieldElementExpression::Sub(box e1, box e2) => {
            let e1 = f.fold_field_expression(statements_buffer, e1);
            let e2 = f.fold_field_expression(statements_buffer, e2);
            zir::FieldElementExpression::Sub(box e1, box e2)
        }
        typed_absy::FieldElementExpression::Mult(box e1, box e2) => {
            let e1 = f.fold_field_expression(statements_buffer, e1);
            let e2 = f.fold_field_expression(statements_buffer, e2);
            zir::FieldElementExpression::Mult(box e1, box e2)
        }
        typed_absy::FieldElementExpression::Div(box e1, box e2) => {
            let e1 = f.fold_field_expression(statements_buffer, e1);
            let e2 = f.fold_field_expression(statements_buffer, e2);
            zir::FieldElementExpression::Div(box e1, box e2)
        }
        typed_absy::FieldElementExpression::Pow(box e1, box e2) => {
            let e1 = f.fold_field_expression(statements_buffer, e1);
            let e2 = f.fold_uint_expression(statements_buffer, e2);
            zir::FieldElementExpression::Pow(box e1, box e2)
        }
        typed_absy::FieldElementExpression::Neg(box e) => {
            let e = f.fold_field_expression(statements_buffer, e);

            zir::FieldElementExpression::Sub(
                box zir::FieldElementExpression::Number(T::zero()),
                box e,
            )
        }
        typed_absy::FieldElementExpression::Pos(box e) => {
            f.fold_field_expression(statements_buffer, e)
        }
        typed_absy::FieldElementExpression::IfElse(c) => f
            .fold_if_else_expression(statements_buffer, c)
            .pop()
            .unwrap()
            .try_into()
            .unwrap(),
        typed_absy::FieldElementExpression::FunctionCall(..) => unreachable!(""),
        typed_absy::FieldElementExpression::Select(select) => f
            .fold_select_expression(statements_buffer, select)
            .pop()
            .unwrap()
            .try_into()
            .unwrap(),
        typed_absy::FieldElementExpression::Member(m) => f
            .fold_member_expression(statements_buffer, m)
            .pop()
            .unwrap()
            .try_into()
            .unwrap(),
        typed_absy::FieldElementExpression::Block(block) => {
            block
                .statements
                .into_iter()
                .for_each(|s| f.fold_statement(statements_buffer, s));
            f.fold_field_expression(statements_buffer, *block.value)
        }
    }
}

fn fold_boolean_expression<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    e: typed_absy::BooleanExpression<'ast, T>,
) -> zir::BooleanExpression<'ast, T> {
    match e {
        typed_absy::BooleanExpression::Block(block) => {
            block
                .statements
                .into_iter()
                .for_each(|s| f.fold_statement(statements_buffer, s));
            f.fold_boolean_expression(statements_buffer, *block.value)
        }
        typed_absy::BooleanExpression::Value(v) => zir::BooleanExpression::Value(v),
        typed_absy::BooleanExpression::Identifier(id) => f
            .fold_identifier_expression(statements_buffer, &typed_absy::ConcreteType::Boolean, id)
            .pop()
            .unwrap()
            .try_into()
            .unwrap(),
        typed_absy::BooleanExpression::FieldEq(box e1, box e2) => {
            let e1 = f.fold_field_expression(statements_buffer, e1);
            let e2 = f.fold_field_expression(statements_buffer, e2);
            zir::BooleanExpression::FieldEq(box e1, box e2)
        }
        typed_absy::BooleanExpression::BoolEq(box e1, box e2) => {
            let e1 = f.fold_boolean_expression(statements_buffer, e1);
            let e2 = f.fold_boolean_expression(statements_buffer, e2);
            zir::BooleanExpression::BoolEq(box e1, box e2)
        }
        typed_absy::BooleanExpression::ArrayEq(box e1, box e2) => {
            let e1 = f.fold_array_expression(statements_buffer, e1);
            let e2 = f.fold_array_expression(statements_buffer, e2);

            assert_eq!(e1.len(), e2.len());

            e1.into_iter().zip(e2.into_iter()).fold(
                zir::BooleanExpression::Value(true),
                |acc, (e1, e2)| {
                    zir::BooleanExpression::And(
                        box acc,
                        box match (e1, e2) {
                            (
                                zir::ZirExpression::FieldElement(e1),
                                zir::ZirExpression::FieldElement(e2),
                            ) => zir::BooleanExpression::FieldEq(box e1, box e2),
                            (zir::ZirExpression::Boolean(e1), zir::ZirExpression::Boolean(e2)) => {
                                zir::BooleanExpression::BoolEq(box e1, box e2)
                            }
                            (zir::ZirExpression::Uint(e1), zir::ZirExpression::Uint(e2)) => {
                                zir::BooleanExpression::UintEq(box e1, box e2)
                            }
                            _ => unreachable!(),
                        },
                    )
                },
            )
        }
        typed_absy::BooleanExpression::StructEq(box e1, box e2) => {
            let e1 = f.fold_struct_expression(statements_buffer, e1);
            let e2 = f.fold_struct_expression(statements_buffer, e2);

            assert_eq!(e1.len(), e2.len());

            e1.into_iter().zip(e2.into_iter()).fold(
                zir::BooleanExpression::Value(true),
                |acc, (e1, e2)| {
                    zir::BooleanExpression::And(
                        box acc,
                        box match (e1, e2) {
                            (
                                zir::ZirExpression::FieldElement(e1),
                                zir::ZirExpression::FieldElement(e2),
                            ) => zir::BooleanExpression::FieldEq(box e1, box e2),
                            (zir::ZirExpression::Boolean(e1), zir::ZirExpression::Boolean(e2)) => {
                                zir::BooleanExpression::BoolEq(box e1, box e2)
                            }
                            (zir::ZirExpression::Uint(e1), zir::ZirExpression::Uint(e2)) => {
                                zir::BooleanExpression::UintEq(box e1, box e2)
                            }
                            _ => unreachable!(),
                        },
                    )
                },
            )
        }
        typed_absy::BooleanExpression::UintEq(box e1, box e2) => {
            let e1 = f.fold_uint_expression(statements_buffer, e1);
            let e2 = f.fold_uint_expression(statements_buffer, e2);

            zir::BooleanExpression::UintEq(box e1, box e2)
        }
        typed_absy::BooleanExpression::FieldLt(box e1, box e2) => {
            let e1 = f.fold_field_expression(statements_buffer, e1);
            let e2 = f.fold_field_expression(statements_buffer, e2);
            zir::BooleanExpression::FieldLt(box e1, box e2)
        }
        typed_absy::BooleanExpression::FieldLe(box e1, box e2) => {
            let e1 = f.fold_field_expression(statements_buffer, e1);
            let e2 = f.fold_field_expression(statements_buffer, e2);
            zir::BooleanExpression::FieldLe(box e1, box e2)
        }
        typed_absy::BooleanExpression::FieldGt(box e1, box e2) => {
            let e1 = f.fold_field_expression(statements_buffer, e1);
            let e2 = f.fold_field_expression(statements_buffer, e2);
            zir::BooleanExpression::FieldGt(box e1, box e2)
        }
        typed_absy::BooleanExpression::FieldGe(box e1, box e2) => {
            let e1 = f.fold_field_expression(statements_buffer, e1);
            let e2 = f.fold_field_expression(statements_buffer, e2);
            zir::BooleanExpression::FieldGe(box e1, box e2)
        }
        typed_absy::BooleanExpression::UintLt(box e1, box e2) => {
            let e1 = f.fold_uint_expression(statements_buffer, e1);
            let e2 = f.fold_uint_expression(statements_buffer, e2);
            zir::BooleanExpression::UintLt(box e1, box e2)
        }
        typed_absy::BooleanExpression::UintLe(box e1, box e2) => {
            let e1 = f.fold_uint_expression(statements_buffer, e1);
            let e2 = f.fold_uint_expression(statements_buffer, e2);
            zir::BooleanExpression::UintLe(box e1, box e2)
        }
        typed_absy::BooleanExpression::UintGt(box e1, box e2) => {
            let e1 = f.fold_uint_expression(statements_buffer, e1);
            let e2 = f.fold_uint_expression(statements_buffer, e2);
            zir::BooleanExpression::UintGt(box e1, box e2)
        }
        typed_absy::BooleanExpression::UintGe(box e1, box e2) => {
            let e1 = f.fold_uint_expression(statements_buffer, e1);
            let e2 = f.fold_uint_expression(statements_buffer, e2);
            zir::BooleanExpression::UintGe(box e1, box e2)
        }
        typed_absy::BooleanExpression::Or(box e1, box e2) => {
            let e1 = f.fold_boolean_expression(statements_buffer, e1);
            let e2 = f.fold_boolean_expression(statements_buffer, e2);
            zir::BooleanExpression::Or(box e1, box e2)
        }
        typed_absy::BooleanExpression::And(box e1, box e2) => {
            let e1 = f.fold_boolean_expression(statements_buffer, e1);
            let e2 = f.fold_boolean_expression(statements_buffer, e2);
            zir::BooleanExpression::And(box e1, box e2)
        }
        typed_absy::BooleanExpression::Not(box e) => {
            let e = f.fold_boolean_expression(statements_buffer, e);
            zir::BooleanExpression::Not(box e)
        }
        typed_absy::BooleanExpression::IfElse(c) => f
            .fold_if_else_expression(statements_buffer, c)
            .pop()
            .unwrap()
            .try_into()
            .unwrap(),
        typed_absy::BooleanExpression::FunctionCall(..) => unreachable!(),
        typed_absy::BooleanExpression::Select(select) => f
            .fold_select_expression(statements_buffer, select)
            .pop()
            .unwrap()
            .try_into()
            .unwrap(),
        typed_absy::BooleanExpression::Member(m) => f
            .fold_member_expression(statements_buffer, m)
            .pop()
            .unwrap()
            .try_into()
            .unwrap(),
    }
}

fn fold_uint_expression<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    e: typed_absy::UExpression<'ast, T>,
) -> zir::UExpression<'ast, T> {
    f.fold_uint_expression_inner(statements_buffer, e.bitwidth, e.inner)
        .annotate(e.bitwidth.to_usize())
}

fn fold_uint_expression_inner<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    bitwidth: UBitwidth,
    e: typed_absy::UExpressionInner<'ast, T>,
) -> zir::UExpressionInner<'ast, T> {
    match e {
        typed_absy::UExpressionInner::Block(block) => {
            block
                .statements
                .into_iter()
                .for_each(|s| f.fold_statement(statements_buffer, s));
            f.fold_uint_expression(statements_buffer, *block.value)
                .into_inner()
        }
        typed_absy::UExpressionInner::Value(v) => zir::UExpressionInner::Value(v),
        typed_absy::UExpressionInner::Identifier(id) => zir::UExpression::try_from(
            f.fold_identifier_expression(statements_buffer, &bitwidth, id)
                .pop()
                .unwrap(),
        )
        .unwrap()
        .into_inner(),
        typed_absy::UExpressionInner::Add(box left, box right) => {
            let left = f.fold_uint_expression(statements_buffer, left);
            let right = f.fold_uint_expression(statements_buffer, right);

            zir::UExpressionInner::Add(box left, box right)
        }
        typed_absy::UExpressionInner::Sub(box left, box right) => {
            let left = f.fold_uint_expression(statements_buffer, left);
            let right = f.fold_uint_expression(statements_buffer, right);

            zir::UExpressionInner::Sub(box left, box right)
        }
        typed_absy::UExpressionInner::FloorSub(..) => unreachable!(),
        typed_absy::UExpressionInner::Mult(box left, box right) => {
            let left = f.fold_uint_expression(statements_buffer, left);
            let right = f.fold_uint_expression(statements_buffer, right);

            zir::UExpressionInner::Mult(box left, box right)
        }
        typed_absy::UExpressionInner::Div(box left, box right) => {
            let left = f.fold_uint_expression(statements_buffer, left);
            let right = f.fold_uint_expression(statements_buffer, right);

            zir::UExpressionInner::Div(box left, box right)
        }
        typed_absy::UExpressionInner::Rem(box left, box right) => {
            let left = f.fold_uint_expression(statements_buffer, left);
            let right = f.fold_uint_expression(statements_buffer, right);

            zir::UExpressionInner::Rem(box left, box right)
        }
        typed_absy::UExpressionInner::Xor(box left, box right) => {
            let left = f.fold_uint_expression(statements_buffer, left);
            let right = f.fold_uint_expression(statements_buffer, right);

            zir::UExpressionInner::Xor(box left, box right)
        }
        typed_absy::UExpressionInner::And(box left, box right) => {
            let left = f.fold_uint_expression(statements_buffer, left);
            let right = f.fold_uint_expression(statements_buffer, right);

            zir::UExpressionInner::And(box left, box right)
        }
        typed_absy::UExpressionInner::Or(box left, box right) => {
            let left = f.fold_uint_expression(statements_buffer, left);
            let right = f.fold_uint_expression(statements_buffer, right);

            zir::UExpressionInner::Or(box left, box right)
        }
        typed_absy::UExpressionInner::LeftShift(box e, box by) => {
            let e = f.fold_uint_expression(statements_buffer, e);

            let by = match by.as_inner() {
                typed_absy::UExpressionInner::Value(by) => by,
                _ => unreachable!("static analysis should have made sure that this is constant"),
            };

            zir::UExpressionInner::LeftShift(box e, *by as u32)
        }
        typed_absy::UExpressionInner::RightShift(box e, box by) => {
            let e = f.fold_uint_expression(statements_buffer, e);

            let by = match by.as_inner() {
                typed_absy::UExpressionInner::Value(by) => by,
                _ => unreachable!("static analysis should have made sure that this is constant"),
            };

            zir::UExpressionInner::RightShift(box e, *by as u32)
        }
        typed_absy::UExpressionInner::Not(box e) => {
            let e = f.fold_uint_expression(statements_buffer, e);

            zir::UExpressionInner::Not(box e)
        }
        typed_absy::UExpressionInner::Neg(box e) => {
            let bitwidth = e.bitwidth();

            f.fold_uint_expression(
                statements_buffer,
                typed_absy::UExpressionInner::Value(0).annotate(bitwidth) - e,
            )
            .into_inner()
        }

        typed_absy::UExpressionInner::Pos(box e) => {
            let e = f.fold_uint_expression(statements_buffer, e);

            e.into_inner()
        }
        typed_absy::UExpressionInner::FunctionCall(..) => {
            unreachable!("function calls should have been removed")
        }
        typed_absy::UExpressionInner::Select(select) => zir::UExpression::try_from(
            f.fold_select_expression(statements_buffer, select)
                .pop()
                .unwrap(),
        )
        .unwrap()
        .into_inner(),
        typed_absy::UExpressionInner::Member(m) => zir::UExpression::try_from(
            f.fold_member_expression(statements_buffer, m)
                .pop()
                .unwrap(),
        )
        .unwrap()
        .into_inner(),
        typed_absy::UExpressionInner::IfElse(c) => zir::UExpression::try_from(
            f.fold_if_else_expression(statements_buffer, c)
                .pop()
                .unwrap(),
        )
        .unwrap()
        .into_inner(),
    }
}

fn fold_function<'ast, T: Field>(
    f: &mut Flattener<T>,
    fun: typed_absy::TypedFunction<'ast, T>,
) -> zir::ZirFunction<'ast, T> {
    let mut main_statements_buffer = vec![];

    fun.statements
        .into_iter()
        .for_each(|s| f.fold_statement(&mut main_statements_buffer, s));

    zir::ZirFunction {
        arguments: fun
            .arguments
            .into_iter()
            .flat_map(|a| f.fold_declaration_parameter(a))
            .collect(),
        statements: main_statements_buffer,
        signature: typed_absy::types::ConcreteSignature::try_from(
            typed_absy::types::Signature::<T>::try_from(fun.signature).unwrap(),
        )
        .unwrap()
        .into(),
    }
}

fn fold_array_expression<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    e: typed_absy::ArrayExpression<'ast, T>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    let size = match e.size().into_inner() {
        typed_absy::UExpressionInner::Value(v) => v,
        _ => unreachable!(),
    } as usize;
    f.fold_array_expression_inner(
        statements_buffer,
        &typed_absy::types::ConcreteArrayType::try_from(e.ty().clone()).unwrap(),
        e.into_inner(),
    )
}

fn fold_struct_expression<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    e: typed_absy::StructExpression<'ast, T>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    f.fold_struct_expression_inner(
        statements_buffer,
        &typed_absy::types::ConcreteStructType::try_from(e.ty().clone()).unwrap(),
        e.into_inner(),
    )
}

fn fold_program<'ast, T: Field>(
    f: &mut Flattener<T>,
    mut p: typed_absy::TypedProgram<'ast, T>,
) -> zir::ZirProgram<'ast, T> {
    let main_module = p.modules.remove(&p.main).unwrap();

    let main_function = main_module
        .functions
        .into_iter()
        .find(|(key, _)| key.id == "main")
        .unwrap()
        .1;

    let main_function = match main_function {
        typed_absy::TypedFunctionSymbol::Here(f) => f,
        _ => unreachable!(),
    };

    zir::ZirProgram {
        main: f.fold_function(main_function),
    }
}
