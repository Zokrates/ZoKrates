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
        typed_absy::types::ConcreteType::Tuple(tuple_ty) => tuple_ty
            .elements
            .iter()
            .enumerate()
            .flat_map(|(i, ty)| {
                flatten_identifier_rec(zir::SourceIdentifier::Element(box id.clone(), i as u32), ty)
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

impl<'ast, T: Field> Flatten<'ast, T> for typed_absy::TupleExpression<'ast, T> {
    fn flatten(
        self,
        f: &mut Flattener<T>,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        f.fold_tuple_expression(statements_buffer, self)
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
        p: typed_absy::DeclarationParameter<'ast, T>,
    ) -> Vec<zir::Parameter<'ast>> {
        let private = p.private;
        self.fold_variable(crate::typed_absy::variable::try_from_g_variable(p.id).unwrap())
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
            typed_absy::TypedAssignee::Element(box a, index) => {
                use typed_absy::Typed;

                let tuple_ty = typed_absy::ConcreteTupleType::try_from(
                    typed_absy::ConcreteType::try_from(a.get_type()).unwrap(),
                )
                .unwrap();

                let offset = tuple_ty
                    .elements
                    .iter()
                    .take(index as usize)
                    .map(|ty| ty.get_primitive_count())
                    .sum();

                let size = &tuple_ty.elements[index as usize].get_primitive_count();

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
            typed_absy::TypedExpression::Tuple(e) => {
                self.fold_tuple_expression(statements_buffer, e)
            }
            typed_absy::TypedExpression::Int(_) => unreachable!(),
        }
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

    fn fold_tuple_expression(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        e: typed_absy::TupleExpression<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_tuple_expression(self, statements_buffer, e)
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

    fn fold_conditional_expression<E: Flatten<'ast, T>>(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        c: typed_absy::ConditionalExpression<'ast, T, E>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_conditional_expression(self, statements_buffer, c)
    }

    fn fold_member_expression<E>(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        m: typed_absy::MemberExpression<'ast, T, E>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_member_expression(self, statements_buffer, m)
    }

    fn fold_element_expression<E>(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        e: typed_absy::ElementExpression<'ast, T, E>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_element_expression(self, statements_buffer, e)
    }

    fn fold_select_expression<E>(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        select: typed_absy::SelectExpression<'ast, T, E>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_select_expression(self, statements_buffer, select)
    }

    fn fold_eq_expression<E: Flatten<'ast, T>>(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        eq: typed_absy::EqExpression<E>,
    ) -> zir::BooleanExpression<'ast, T> {
        fold_eq_expression(self, statements_buffer, eq)
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
        ty: &typed_absy::types::ConcreteType,
        size: u32,
        e: typed_absy::ArrayExpressionInner<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_array_expression_inner(self, statements_buffer, ty, size, e)
    }

    fn fold_struct_expression_inner(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        ty: &typed_absy::types::ConcreteStructType,
        e: typed_absy::StructExpressionInner<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_struct_expression_inner(self, statements_buffer, ty, e)
    }

    fn fold_tuple_expression_inner(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        ty: &typed_absy::types::ConcreteTupleType,
        e: typed_absy::TupleExpressionInner<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_tuple_expression_inner(self, statements_buffer, ty, e)
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
        typed_absy::TypedStatement::Assertion(e, error) => {
            let e = f.fold_boolean_expression(statements_buffer, e);
            let error = match error {
                typed_absy::RuntimeError::SourceAssertion(metadata) => {
                    zir::RuntimeError::SourceAssertion(metadata.to_string())
                }
                typed_absy::RuntimeError::SelectRangeCheck => zir::RuntimeError::SelectRangeCheck,
            };
            vec![zir::ZirStatement::Assertion(e, error)]
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
    ty: &typed_absy::types::ConcreteType,
    size: u32,
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
            let variables = flatten_identifier_rec(
                f.fold_name(id),
                &typed_absy::types::ConcreteType::array((ty.clone(), size)),
            );
            variables
                .into_iter()
                .map(|v| match v._type {
                    zir::Type::FieldElement => zir::FieldElementExpression::Identifier(v.id).into(),
                    zir::Type::Boolean => zir::BooleanExpression::Identifier(v.id).into(),
                    zir::Type::Uint(bitwidth) => zir::UExpressionInner::Identifier(v.id)
                        .annotate(bitwidth)
                        .into(),
                })
                .collect()
        }
        typed_absy::ArrayExpressionInner::Value(exprs) => {
            let exprs: Vec<_> = exprs
                .into_iter()
                .flat_map(|e| f.fold_expression_or_spread(statements_buffer, e))
                .collect();

            assert_eq!(exprs.len(), size as usize * ty.get_primitive_count());

            exprs
        }
        typed_absy::ArrayExpressionInner::FunctionCall(..) => unreachable!(),
        typed_absy::ArrayExpressionInner::Conditional(c) => {
            f.fold_conditional_expression(statements_buffer, c)
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
                    assert_eq!(size, to.saturating_sub(from) as u32);

                    let element_size = ty.get_primitive_count();
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
        typed_absy::ArrayExpressionInner::Element(element) => {
            f.fold_element_expression(statements_buffer, element)
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
            let variables = flatten_identifier_rec(
                f.fold_name(id),
                &typed_absy::types::ConcreteType::struc(ty.clone()),
            );
            variables
                .into_iter()
                .map(|v| match v._type {
                    zir::Type::FieldElement => zir::FieldElementExpression::Identifier(v.id).into(),
                    zir::Type::Boolean => zir::BooleanExpression::Identifier(v.id).into(),
                    zir::Type::Uint(bitwidth) => zir::UExpressionInner::Identifier(v.id)
                        .annotate(bitwidth)
                        .into(),
                })
                .collect()
        }
        typed_absy::StructExpressionInner::Value(exprs) => exprs
            .into_iter()
            .flat_map(|e| f.fold_expression(statements_buffer, e))
            .collect(),
        typed_absy::StructExpressionInner::FunctionCall(..) => unreachable!(),
        typed_absy::StructExpressionInner::Conditional(c) => {
            f.fold_conditional_expression(statements_buffer, c)
        }
        typed_absy::StructExpressionInner::Member(m) => {
            f.fold_member_expression(statements_buffer, m)
        }
        typed_absy::StructExpressionInner::Select(select) => {
            f.fold_select_expression(statements_buffer, select)
        }
        typed_absy::StructExpressionInner::Element(element) => {
            f.fold_element_expression(statements_buffer, element)
        }
    }
}

fn fold_tuple_expression_inner<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    ty: &typed_absy::types::ConcreteTupleType,
    tuple: typed_absy::TupleExpressionInner<'ast, T>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    match tuple {
        typed_absy::TupleExpressionInner::Block(block) => {
            block
                .statements
                .into_iter()
                .for_each(|s| f.fold_statement(statements_buffer, s));
            f.fold_tuple_expression(statements_buffer, *block.value)
        }
        typed_absy::TupleExpressionInner::Identifier(id) => {
            let variables = flatten_identifier_rec(
                f.fold_name(id),
                &typed_absy::types::ConcreteType::tuple(ty.clone()),
            );
            variables
                .into_iter()
                .map(|v| match v._type {
                    zir::Type::FieldElement => zir::FieldElementExpression::Identifier(v.id).into(),
                    zir::Type::Boolean => zir::BooleanExpression::Identifier(v.id).into(),
                    zir::Type::Uint(bitwidth) => zir::UExpressionInner::Identifier(v.id)
                        .annotate(bitwidth)
                        .into(),
                })
                .collect()
        }
        typed_absy::TupleExpressionInner::Value(exprs) => exprs
            .into_iter()
            .flat_map(|e| f.fold_expression(statements_buffer, e))
            .collect(),
        typed_absy::TupleExpressionInner::FunctionCall(..) => unreachable!(),
        typed_absy::TupleExpressionInner::Conditional(c) => {
            f.fold_conditional_expression(statements_buffer, c)
        }
        typed_absy::TupleExpressionInner::Member(m) => {
            f.fold_member_expression(statements_buffer, m)
        }
        typed_absy::TupleExpressionInner::Select(select) => {
            f.fold_select_expression(statements_buffer, select)
        }
        typed_absy::TupleExpressionInner::Element(element) => {
            f.fold_element_expression(statements_buffer, element)
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

fn fold_element_expression<'ast, T: Field, E>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    e: typed_absy::ElementExpression<'ast, T, E>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    let t = *e.tuple;
    let id = e.index;

    let tuple_ty = t.ty();

    let size = typed_absy::types::ConcreteType::try_from(
        tuple_ty
            .elements
            .iter()
            .enumerate()
            .find(|(i, _)| *i as u32 == id)
            .unwrap()
            .1
            .clone(),
    )
    .unwrap()
    .get_primitive_count();

    let offset: usize = tuple_ty
        .elements
        .iter()
        .take(id as usize)
        .map(|ty| {
            typed_absy::types::ConcreteType::try_from(ty.clone())
                .unwrap()
                .get_primitive_count()
        })
        .sum();

    let t = f.fold_tuple_expression(statements_buffer, t);

    t[offset..offset + size].to_vec()
}

fn fold_select_expression<'ast, T: Field, E>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    select: typed_absy::SelectExpression<'ast, T, E>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    let size = typed_absy::types::ConcreteType::try_from(*select.array.ty().clone().ty)
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

fn fold_conditional_expression<'ast, T: Field, E: Flatten<'ast, T>>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    c: typed_absy::ConditionalExpression<'ast, T, E>,
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

fn fold_field_expression<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    e: typed_absy::FieldElementExpression<'ast, T>,
) -> zir::FieldElementExpression<'ast, T> {
    match e {
        typed_absy::FieldElementExpression::Number(n) => zir::FieldElementExpression::Number(n),
        typed_absy::FieldElementExpression::Identifier(id) => {
            zir::FieldElementExpression::Identifier(
                flatten_identifier_rec(
                    f.fold_name(id),
                    &typed_absy::types::ConcreteType::FieldElement,
                )
                .pop()
                .unwrap()
                .id,
            )
        }
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
        typed_absy::FieldElementExpression::Conditional(c) => f
            .fold_conditional_expression(statements_buffer, c)
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
        typed_absy::FieldElementExpression::Element(element) => f
            .fold_element_expression(statements_buffer, element)
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

// util function to output a boolean expression representing the equality of two lists of ZirExpression.
// the two list are checked to have the same size
// we build a binary tree with internal nodes `And(left, right)` and leaves `Eq(left, right)`
fn conjunction_tree<'ast, T: Field>(
    v: &[zir::ZirExpression<'ast, T>],
    w: &[zir::ZirExpression<'ast, T>],
) -> zir::BooleanExpression<'ast, T> {
    assert_eq!(v.len(), w.len());

    match v.len() {
        0 => zir::BooleanExpression::Value(true),
        1 => match (v[0].clone(), w[0].clone()) {
            (zir::ZirExpression::Boolean(v), zir::ZirExpression::Boolean(w)) => {
                zir::BooleanExpression::BoolEq(box v, box w)
            }
            (zir::ZirExpression::FieldElement(v), zir::ZirExpression::FieldElement(w)) => {
                zir::BooleanExpression::FieldEq(box v, box w)
            }
            (zir::ZirExpression::Uint(v), zir::ZirExpression::Uint(w)) => {
                zir::BooleanExpression::UintEq(box v, box w)
            }
            _ => unreachable!(),
        },
        n => {
            let (x0, y0) = v.split_at(n / 2);
            let (x1, y1) = w.split_at(n / 2);
            zir::BooleanExpression::And(box conjunction_tree(x0, x1), box conjunction_tree(y0, y1))
        }
    }
}

fn fold_eq_expression<'ast, T: Field, E: Flatten<'ast, T>>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    e: typed_absy::EqExpression<E>,
) -> zir::BooleanExpression<'ast, T> {
    let left = e.left.flatten(f, statements_buffer);
    let right = e.right.flatten(f, statements_buffer);
    conjunction_tree(&left, &right)
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
        typed_absy::BooleanExpression::Identifier(id) => zir::BooleanExpression::Identifier(
            flatten_identifier_rec(f.fold_name(id), &typed_absy::types::ConcreteType::Boolean)
                .pop()
                .unwrap()
                .id,
        ),
        typed_absy::BooleanExpression::FieldEq(e) => f.fold_eq_expression(statements_buffer, e),
        typed_absy::BooleanExpression::BoolEq(e) => f.fold_eq_expression(statements_buffer, e),
        typed_absy::BooleanExpression::ArrayEq(e) => f.fold_eq_expression(statements_buffer, e),
        typed_absy::BooleanExpression::StructEq(e) => f.fold_eq_expression(statements_buffer, e),
        typed_absy::BooleanExpression::TupleEq(e) => f.fold_eq_expression(statements_buffer, e),
        typed_absy::BooleanExpression::UintEq(e) => f.fold_eq_expression(statements_buffer, e),
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
        typed_absy::BooleanExpression::Conditional(c) => f
            .fold_conditional_expression(statements_buffer, c)
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
        typed_absy::BooleanExpression::Element(m) => f
            .fold_element_expression(statements_buffer, m)
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
        typed_absy::UExpressionInner::Identifier(id) => zir::UExpressionInner::Identifier(
            flatten_identifier_rec(
                f.fold_name(id),
                &typed_absy::types::ConcreteType::Uint(bitwidth),
            )
            .pop()
            .unwrap()
            .id,
        ),
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
        typed_absy::UExpressionInner::Element(m) => zir::UExpression::try_from(
            f.fold_element_expression(statements_buffer, m)
                .pop()
                .unwrap(),
        )
        .unwrap()
        .into_inner(),
        typed_absy::UExpressionInner::Conditional(c) => zir::UExpression::try_from(
            f.fold_conditional_expression(statements_buffer, c)
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
            crate::typed_absy::types::try_from_g_signature::<
                crate::typed_absy::types::DeclarationConstant<'ast, T>,
                crate::typed_absy::UExpression<'ast, T>,
            >(fun.signature)
            .unwrap(),
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
    let size: u32 = e.size().try_into().unwrap();
    f.fold_array_expression_inner(
        statements_buffer,
        &typed_absy::types::ConcreteType::try_from(e.inner_type().clone()).unwrap(),
        size,
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

fn fold_tuple_expression<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    e: typed_absy::TupleExpression<'ast, T>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    f.fold_tuple_expression_inner(
        statements_buffer,
        &typed_absy::types::ConcreteTupleType::try_from(e.ty().clone()).unwrap(),
        e.into_inner(),
    )
}

fn fold_program<'ast, T: Field>(
    f: &mut Flattener<T>,
    mut p: typed_absy::TypedProgram<'ast, T>,
) -> zir::ZirProgram<'ast, T> {
    let main_module = p.modules.remove(&p.main).unwrap();

    let main_function = main_module
        .into_functions_iter()
        .find(|d| d.key.id == "main")
        .unwrap()
        .symbol;
    let main_function = match main_function {
        typed_absy::TypedFunctionSymbol::Here(main) => main,
        _ => unreachable!(),
    };

    zir::ZirProgram {
        main: f.fold_function(main_function),
    }
}
