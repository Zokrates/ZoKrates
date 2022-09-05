use std::marker::PhantomData;
use zokrates_ast::typed::types::UBitwidth;
use zokrates_ast::typed::{self, Expr, Typed};
use zokrates_ast::zir::{self, Select};
use zokrates_field::Field;

use std::convert::{TryFrom, TryInto};

#[derive(Default)]
pub struct Flattener<T: Field> {
    phantom: PhantomData<T>,
}

fn flatten_identifier_rec<'ast>(
    id: zir::SourceIdentifier<'ast>,
    ty: &typed::types::ConcreteType,
) -> Vec<zir::Variable<'ast>> {
    match ty {
        typed::ConcreteType::Int => unreachable!(),
        typed::ConcreteType::FieldElement => vec![zir::Variable {
            id: zir::Identifier::Source(id),
            _type: zir::Type::FieldElement,
        }],
        typed::types::ConcreteType::Boolean => vec![zir::Variable {
            id: zir::Identifier::Source(id),
            _type: zir::Type::Boolean,
        }],
        typed::types::ConcreteType::Uint(bitwidth) => vec![zir::Variable {
            id: zir::Identifier::Source(id),
            _type: zir::Type::uint(bitwidth.to_usize()),
        }],
        typed::types::ConcreteType::Array(array_type) => (0..*array_type.size)
            .flat_map(|i| {
                flatten_identifier_rec(
                    zir::SourceIdentifier::Select(box id.clone(), i),
                    &array_type.ty,
                )
            })
            .collect(),
        typed::types::ConcreteType::Struct(members) => members
            .iter()
            .flat_map(|struct_member| {
                flatten_identifier_rec(
                    zir::SourceIdentifier::Member(box id.clone(), struct_member.id.clone()),
                    &struct_member.ty,
                )
            })
            .collect(),
        typed::types::ConcreteType::Tuple(tuple_ty) => tuple_ty
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

impl<'ast, T: Field> Flatten<'ast, T> for typed::FieldElementExpression<'ast, T> {
    fn flatten(
        self,
        f: &mut Flattener<T>,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        vec![f.fold_field_expression(statements_buffer, self).into()]
    }
}

impl<'ast, T: Field> Flatten<'ast, T> for typed::BooleanExpression<'ast, T> {
    fn flatten(
        self,
        f: &mut Flattener<T>,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        vec![f.fold_boolean_expression(statements_buffer, self).into()]
    }
}

impl<'ast, T: Field> Flatten<'ast, T> for typed::UExpression<'ast, T> {
    fn flatten(
        self,
        f: &mut Flattener<T>,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        vec![f.fold_uint_expression(statements_buffer, self).into()]
    }
}

impl<'ast, T: Field> Flatten<'ast, T> for typed::ArrayExpression<'ast, T> {
    fn flatten(
        self,
        f: &mut Flattener<T>,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        f.fold_array_expression(statements_buffer, self)
    }
}

impl<'ast, T: Field> Flatten<'ast, T> for typed::StructExpression<'ast, T> {
    fn flatten(
        self,
        f: &mut Flattener<T>,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        f.fold_struct_expression(statements_buffer, self)
    }
}

impl<'ast, T: Field> Flatten<'ast, T> for typed::TupleExpression<'ast, T> {
    fn flatten(
        self,
        f: &mut Flattener<T>,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        f.fold_tuple_expression(statements_buffer, self)
    }
}

impl<'ast, T: Field> Flattener<T> {
    pub fn flatten(p: typed::TypedProgram<T>) -> zir::ZirProgram<T> {
        let mut f = Flattener::default();
        f.fold_program(p)
    }

    fn fold_program(&mut self, p: typed::TypedProgram<'ast, T>) -> zir::ZirProgram<'ast, T> {
        fold_program(self, p)
    }

    fn fold_function(&mut self, f: typed::TypedFunction<'ast, T>) -> zir::ZirFunction<'ast, T> {
        fold_function(self, f)
    }

    fn fold_declaration_parameter(
        &mut self,
        p: typed::DeclarationParameter<'ast, T>,
    ) -> Vec<zir::Parameter<'ast>> {
        let private = p.private;
        self.fold_variable(zokrates_ast::typed::variable::try_from_g_variable(p.id).unwrap())
            .into_iter()
            .map(|v| zir::Parameter { id: v, private })
            .collect()
    }

    fn fold_name(&mut self, n: typed::Identifier<'ast>) -> zir::SourceIdentifier<'ast> {
        zir::SourceIdentifier::Basic(n)
    }

    fn fold_variable(&mut self, v: typed::Variable<'ast, T>) -> Vec<zir::Variable<'ast>> {
        let ty = v.get_type();
        let id = self.fold_name(v.id);

        let ty = typed::types::ConcreteType::try_from(ty).unwrap();

        flatten_identifier_rec(id, &ty)
    }

    fn fold_assignee(&mut self, a: typed::TypedAssignee<'ast, T>) -> Vec<zir::ZirAssignee<'ast>> {
        match a {
            typed::TypedAssignee::Identifier(v) => self.fold_variable(v),
            typed::TypedAssignee::Select(box a, box i) => {
                let count = match typed::ConcreteType::try_from(a.get_type()).unwrap() {
                    typed::ConcreteType::Array(array_ty) => array_ty.ty.get_primitive_count(),
                    _ => unreachable!(),
                };
                let a = self.fold_assignee(a);

                match i.as_inner() {
                    typed::UExpressionInner::Value(index) => {
                        a[*index as usize * count..(*index as usize + 1) * count].to_vec()
                    }
                    i => unreachable!("index {:?} not allowed, should be a constant", i),
                }
            }
            typed::TypedAssignee::Member(box a, m) => {
                let (offset, size) =
                    match typed::ConcreteType::try_from(a.get_type()).unwrap() {
                        typed::ConcreteType::Struct(struct_type) => struct_type
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
            typed::TypedAssignee::Element(box a, index) => {
                let tuple_ty = typed::ConcreteTupleType::try_from(
                    typed::ConcreteType::try_from(a.get_type()).unwrap(),
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
        s: typed::TypedStatement<'ast, T>,
    ) {
        fold_statement(self, statements_buffer, s)
    }

    fn fold_expression_or_spread(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        e: typed::TypedExpressionOrSpread<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        match e {
            typed::TypedExpressionOrSpread::Expression(e) => {
                self.fold_expression(statements_buffer, e)
            }
            typed::TypedExpressionOrSpread::Spread(s) => {
                self.fold_array_expression(statements_buffer, s.array)
            }
        }
    }

    fn fold_expression(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        e: typed::TypedExpression<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        match e {
            typed::TypedExpression::FieldElement(e) => {
                vec![self.fold_field_expression(statements_buffer, e).into()]
            }
            typed::TypedExpression::Boolean(e) => {
                vec![self.fold_boolean_expression(statements_buffer, e).into()]
            }
            typed::TypedExpression::Uint(e) => {
                vec![self.fold_uint_expression(statements_buffer, e).into()]
            }
            typed::TypedExpression::Array(e) => self.fold_array_expression(statements_buffer, e),
            typed::TypedExpression::Struct(e) => self.fold_struct_expression(statements_buffer, e),
            typed::TypedExpression::Tuple(e) => self.fold_tuple_expression(statements_buffer, e),
            typed::TypedExpression::Int(_) => unreachable!(),
        }
    }

    fn fold_array_expression(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        e: typed::ArrayExpression<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_array_expression(self, statements_buffer, e)
    }

    fn fold_struct_expression(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        e: typed::StructExpression<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_struct_expression(self, statements_buffer, e)
    }

    fn fold_tuple_expression(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        e: typed::TupleExpression<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_tuple_expression(self, statements_buffer, e)
    }

    fn fold_conditional_expression<E: Flatten<'ast, T>>(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        c: typed::ConditionalExpression<'ast, T, E>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_conditional_expression(self, statements_buffer, c)
    }

    fn fold_member_expression<E>(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        m: typed::MemberExpression<'ast, T, E>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_member_expression(self, statements_buffer, m)
    }

    fn fold_element_expression<E>(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        e: typed::ElementExpression<'ast, T, E>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_element_expression(self, statements_buffer, e)
    }

    fn fold_select_expression<E>(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        select: typed::SelectExpression<'ast, T, E>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_select_expression(self, statements_buffer, select)
    }

    fn fold_eq_expression<E: Flatten<'ast, T>>(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        eq: typed::EqExpression<E>,
    ) -> zir::BooleanExpression<'ast, T> {
        fold_eq_expression(self, statements_buffer, eq)
    }

    fn fold_field_expression(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        e: typed::FieldElementExpression<'ast, T>,
    ) -> zir::FieldElementExpression<'ast, T> {
        fold_field_expression(self, statements_buffer, e)
    }
    fn fold_boolean_expression(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        e: typed::BooleanExpression<'ast, T>,
    ) -> zir::BooleanExpression<'ast, T> {
        fold_boolean_expression(self, statements_buffer, e)
    }
    fn fold_uint_expression(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        e: typed::UExpression<'ast, T>,
    ) -> zir::UExpression<'ast, T> {
        fold_uint_expression(self, statements_buffer, e)
    }

    fn fold_uint_expression_inner(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        bitwidth: UBitwidth,
        e: typed::UExpressionInner<'ast, T>,
    ) -> zir::UExpressionInner<'ast, T> {
        fold_uint_expression_inner(self, statements_buffer, bitwidth, e)
    }

    fn fold_array_expression_inner(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        ty: &typed::types::ConcreteType,
        size: u32,
        e: typed::ArrayExpressionInner<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_array_expression_inner(self, statements_buffer, ty, size, e)
    }

    fn fold_struct_expression_inner(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        ty: &typed::types::ConcreteStructType,
        e: typed::StructExpressionInner<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_struct_expression_inner(self, statements_buffer, ty, e)
    }

    fn fold_tuple_expression_inner(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        ty: &typed::types::ConcreteTupleType,
        e: typed::TupleExpressionInner<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_tuple_expression_inner(self, statements_buffer, ty, e)
    }
}

fn fold_statement<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    s: typed::TypedStatement<'ast, T>,
) {
    let res = match s {
        typed::TypedStatement::Return(expression) => vec![zir::ZirStatement::Return(
            f.fold_expression(statements_buffer, expression),
        )],
        typed::TypedStatement::Definition(a, typed::DefinitionRhs::Expression(e)) => {
            let a = f.fold_assignee(a);
            let e = f.fold_expression(statements_buffer, e);
            assert_eq!(a.len(), e.len());
            a.into_iter()
                .zip(e.into_iter())
                .map(|(a, e)| zir::ZirStatement::Definition(a, e))
                .collect()
        }
        typed::TypedStatement::Assertion(e, error) => {
            let e = f.fold_boolean_expression(statements_buffer, e);
            let error = match error {
                typed::RuntimeError::SourceAssertion(metadata) => {
                    zir::RuntimeError::SourceAssertion(metadata.to_string())
                }
                typed::RuntimeError::SelectRangeCheck => zir::RuntimeError::SelectRangeCheck,
                typed::RuntimeError::DivisionByZero => zir::RuntimeError::DivisionByZero,
            };
            vec![zir::ZirStatement::Assertion(e, error)]
        }
        typed::TypedStatement::Definition(
            assignee,
            typed::DefinitionRhs::EmbedCall(embed_call),
        ) => {
            vec![zir::ZirStatement::MultipleDefinition(
                f.fold_assignee(assignee),
                zir::ZirExpressionList::EmbedCall(
                    embed_call.embed,
                    embed_call.generics,
                    embed_call
                        .arguments
                        .into_iter()
                        .flat_map(|a| f.fold_expression(statements_buffer, a))
                        .collect(),
                ),
            )]
        }
        typed::TypedStatement::Log(l, e) => vec![zir::ZirStatement::Log(
            l,
            e.into_iter()
                .map(|e| {
                    (
                        e.get_type().try_into().unwrap(),
                        f.fold_expression(statements_buffer, e),
                    )
                })
                .collect(),
        )],
        typed::TypedStatement::PushCallLog(..) => vec![],
        typed::TypedStatement::PopCallLog => vec![],
        typed::TypedStatement::For(..) => unreachable!(),
    };

    statements_buffer.extend(res);
}

fn fold_array_expression_inner<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    ty: &typed::types::ConcreteType,
    size: u32,
    array: typed::ArrayExpressionInner<'ast, T>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    match array {
        typed::ArrayExpressionInner::Block(block) => {
            block
                .statements
                .into_iter()
                .for_each(|s| f.fold_statement(statements_buffer, s));
            f.fold_array_expression(statements_buffer, *block.value)
        }
        typed::ArrayExpressionInner::Identifier(id) => {
            let variables = flatten_identifier_rec(
                f.fold_name(id),
                &typed::types::ConcreteType::array((ty.clone(), size)),
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
        typed::ArrayExpressionInner::Value(exprs) => {
            let exprs: Vec<_> = exprs
                .into_iter()
                .flat_map(|e| f.fold_expression_or_spread(statements_buffer, e))
                .collect();

            assert_eq!(exprs.len(), size as usize * ty.get_primitive_count());

            exprs
        }
        typed::ArrayExpressionInner::FunctionCall(..) => unreachable!(),
        typed::ArrayExpressionInner::Conditional(c) => {
            f.fold_conditional_expression(statements_buffer, c)
        }
        typed::ArrayExpressionInner::Member(m) => f.fold_member_expression(statements_buffer, m),
        typed::ArrayExpressionInner::Select(select) => {
            f.fold_select_expression(statements_buffer, select)
        }
        typed::ArrayExpressionInner::Slice(box array, box from, box to) => {
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
        typed::ArrayExpressionInner::Repeat(box e, box count) => {
            let e = f.fold_expression(statements_buffer, e);
            let count = f.fold_uint_expression(statements_buffer, count);

            match count.into_inner() {
                zir::UExpressionInner::Value(count) => {
                    vec![e; count as usize].into_iter().flatten().collect()
                }
                _ => unreachable!(),
            }
        }
        typed::ArrayExpressionInner::Element(element) => {
            f.fold_element_expression(statements_buffer, element)
        }
    }
}

fn fold_struct_expression_inner<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    ty: &typed::types::ConcreteStructType,
    struc: typed::StructExpressionInner<'ast, T>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    match struc {
        typed::StructExpressionInner::Block(block) => {
            block
                .statements
                .into_iter()
                .for_each(|s| f.fold_statement(statements_buffer, s));
            f.fold_struct_expression(statements_buffer, *block.value)
        }
        typed::StructExpressionInner::Identifier(id) => {
            let variables = flatten_identifier_rec(
                f.fold_name(id),
                &typed::types::ConcreteType::struc(ty.clone()),
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
        typed::StructExpressionInner::Value(exprs) => exprs
            .into_iter()
            .flat_map(|e| f.fold_expression(statements_buffer, e))
            .collect(),
        typed::StructExpressionInner::FunctionCall(..) => unreachable!(),
        typed::StructExpressionInner::Conditional(c) => {
            f.fold_conditional_expression(statements_buffer, c)
        }
        typed::StructExpressionInner::Member(m) => f.fold_member_expression(statements_buffer, m),
        typed::StructExpressionInner::Select(select) => {
            f.fold_select_expression(statements_buffer, select)
        }
        typed::StructExpressionInner::Element(element) => {
            f.fold_element_expression(statements_buffer, element)
        }
    }
}

fn fold_tuple_expression_inner<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    ty: &typed::types::ConcreteTupleType,
    tuple: typed::TupleExpressionInner<'ast, T>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    match tuple {
        typed::TupleExpressionInner::Block(block) => {
            block
                .statements
                .into_iter()
                .for_each(|s| f.fold_statement(statements_buffer, s));
            f.fold_tuple_expression(statements_buffer, *block.value)
        }
        typed::TupleExpressionInner::Identifier(id) => {
            let variables = flatten_identifier_rec(
                f.fold_name(id),
                &typed::types::ConcreteType::tuple(ty.clone()),
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
        typed::TupleExpressionInner::Value(exprs) => exprs
            .into_iter()
            .flat_map(|e| f.fold_expression(statements_buffer, e))
            .collect(),
        typed::TupleExpressionInner::FunctionCall(..) => unreachable!(),
        typed::TupleExpressionInner::Conditional(c) => {
            f.fold_conditional_expression(statements_buffer, c)
        }
        typed::TupleExpressionInner::Member(m) => f.fold_member_expression(statements_buffer, m),
        typed::TupleExpressionInner::Select(select) => {
            f.fold_select_expression(statements_buffer, select)
        }
        typed::TupleExpressionInner::Element(element) => {
            f.fold_element_expression(statements_buffer, element)
        }
    }
}

fn fold_member_expression<'ast, T: Field, E>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    m: typed::MemberExpression<'ast, T, E>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    let s = *m.struc;
    let id = m.id;

    let members = s.ty();

    let size = typed::types::ConcreteType::try_from(
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
            typed::types::ConcreteType::try_from(*member.ty.clone())
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
    e: typed::ElementExpression<'ast, T, E>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    let t = *e.tuple;
    let id = e.index;

    let tuple_ty = t.ty();

    let size = typed::types::ConcreteType::try_from(
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
            typed::types::ConcreteType::try_from(ty.clone())
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
    select: typed::SelectExpression<'ast, T, E>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    let size = typed::types::ConcreteType::try_from(*select.array.ty().clone().ty)
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
                use zokrates_ast::zir::Typed;

                let ty = a[0].get_type();

                match ty {
                    zir::Type::Boolean => zir::BooleanExpression::select(
                        a.into_iter()
                            .map(|e| match e {
                                zir::ZirExpression::Boolean(e) => e.clone(),
                                _ => unreachable!(),
                            })
                            .collect(),
                        index.clone(),
                    )
                    .into(),
                    zir::Type::FieldElement => zir::FieldElementExpression::select(
                        a.into_iter()
                            .map(|e| match e {
                                zir::ZirExpression::FieldElement(e) => e.clone(),
                                _ => unreachable!(),
                            })
                            .collect(),
                        index.clone(),
                    )
                    .into(),
                    zir::Type::Uint(_) => zir::UExpression::select(
                        a.into_iter()
                            .map(|e| match e {
                                zir::ZirExpression::Uint(e) => e.clone(),
                                _ => unreachable!(),
                            })
                            .collect(),
                        index.clone(),
                    )
                    .into(),
                }
            })
            .collect(),
    }
}

fn fold_conditional_expression<'ast, T: Field, E: Flatten<'ast, T>>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    c: typed::ConditionalExpression<'ast, T, E>,
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

    use zokrates_ast::zir::Conditional;

    consequence
        .into_iter()
        .zip(alternative.into_iter())
        .map(|(c, a)| match (c, a) {
            (zir::ZirExpression::FieldElement(c), zir::ZirExpression::FieldElement(a)) => {
                zir::FieldElementExpression::conditional(condition.clone(), c, a).into()
            }
            (zir::ZirExpression::Boolean(c), zir::ZirExpression::Boolean(a)) => {
                zir::BooleanExpression::conditional(condition.clone(), c, a).into()
            }
            (zir::ZirExpression::Uint(c), zir::ZirExpression::Uint(a)) => {
                zir::UExpression::conditional(condition.clone(), c, a).into()
            }
            _ => unreachable!(),
        })
        .collect()
}

fn fold_field_expression<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    e: typed::FieldElementExpression<'ast, T>,
) -> zir::FieldElementExpression<'ast, T> {
    match e {
        typed::FieldElementExpression::Number(n) => zir::FieldElementExpression::Number(n),
        typed::FieldElementExpression::Identifier(id) => zir::FieldElementExpression::Identifier(
            flatten_identifier_rec(f.fold_name(id), &typed::types::ConcreteType::FieldElement)
                .pop()
                .unwrap()
                .id,
        ),
        typed::FieldElementExpression::Add(box e1, box e2) => {
            let e1 = f.fold_field_expression(statements_buffer, e1);
            let e2 = f.fold_field_expression(statements_buffer, e2);
            zir::FieldElementExpression::Add(box e1, box e2)
        }
        typed::FieldElementExpression::Sub(box e1, box e2) => {
            let e1 = f.fold_field_expression(statements_buffer, e1);
            let e2 = f.fold_field_expression(statements_buffer, e2);
            zir::FieldElementExpression::Sub(box e1, box e2)
        }
        typed::FieldElementExpression::Mult(box e1, box e2) => {
            let e1 = f.fold_field_expression(statements_buffer, e1);
            let e2 = f.fold_field_expression(statements_buffer, e2);
            zir::FieldElementExpression::Mult(box e1, box e2)
        }
        typed::FieldElementExpression::Div(box e1, box e2) => {
            let e1 = f.fold_field_expression(statements_buffer, e1);
            let e2 = f.fold_field_expression(statements_buffer, e2);
            zir::FieldElementExpression::Div(box e1, box e2)
        }
        typed::FieldElementExpression::Pow(box e1, box e2) => {
            let e1 = f.fold_field_expression(statements_buffer, e1);
            let e2 = f.fold_uint_expression(statements_buffer, e2);
            zir::FieldElementExpression::Pow(box e1, box e2)
        }
        typed::FieldElementExpression::Neg(box e) => {
            let e = f.fold_field_expression(statements_buffer, e);

            zir::FieldElementExpression::Sub(
                box zir::FieldElementExpression::Number(T::zero()),
                box e,
            )
        }
        typed::FieldElementExpression::Pos(box e) => f.fold_field_expression(statements_buffer, e),
        typed::FieldElementExpression::Conditional(c) => f
            .fold_conditional_expression(statements_buffer, c)
            .pop()
            .unwrap()
            .try_into()
            .unwrap(),
        typed::FieldElementExpression::FunctionCall(..) => unreachable!(""),
        typed::FieldElementExpression::Select(select) => f
            .fold_select_expression(statements_buffer, select)
            .pop()
            .unwrap()
            .try_into()
            .unwrap(),
        typed::FieldElementExpression::Member(m) => f
            .fold_member_expression(statements_buffer, m)
            .pop()
            .unwrap()
            .try_into()
            .unwrap(),
        typed::FieldElementExpression::Element(element) => f
            .fold_element_expression(statements_buffer, element)
            .pop()
            .unwrap()
            .try_into()
            .unwrap(),
        typed::FieldElementExpression::Block(block) => {
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
    e: typed::EqExpression<E>,
) -> zir::BooleanExpression<'ast, T> {
    let left = e.left.flatten(f, statements_buffer);
    let right = e.right.flatten(f, statements_buffer);
    conjunction_tree(&left, &right)
}

fn fold_boolean_expression<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    e: typed::BooleanExpression<'ast, T>,
) -> zir::BooleanExpression<'ast, T> {
    match e {
        typed::BooleanExpression::Block(block) => {
            block
                .statements
                .into_iter()
                .for_each(|s| f.fold_statement(statements_buffer, s));
            f.fold_boolean_expression(statements_buffer, *block.value)
        }
        typed::BooleanExpression::Value(v) => zir::BooleanExpression::Value(v),
        typed::BooleanExpression::Identifier(id) => zir::BooleanExpression::Identifier(
            flatten_identifier_rec(f.fold_name(id), &typed::types::ConcreteType::Boolean)
                .pop()
                .unwrap()
                .id,
        ),
        typed::BooleanExpression::FieldEq(e) => f.fold_eq_expression(statements_buffer, e),
        typed::BooleanExpression::BoolEq(e) => f.fold_eq_expression(statements_buffer, e),
        typed::BooleanExpression::ArrayEq(e) => f.fold_eq_expression(statements_buffer, e),
        typed::BooleanExpression::StructEq(e) => f.fold_eq_expression(statements_buffer, e),
        typed::BooleanExpression::TupleEq(e) => f.fold_eq_expression(statements_buffer, e),
        typed::BooleanExpression::UintEq(e) => f.fold_eq_expression(statements_buffer, e),
        typed::BooleanExpression::FieldLt(box e1, box e2) => {
            let e1 = f.fold_field_expression(statements_buffer, e1);
            let e2 = f.fold_field_expression(statements_buffer, e2);
            zir::BooleanExpression::FieldLt(box e1, box e2)
        }
        typed::BooleanExpression::FieldLe(box e1, box e2) => {
            let e1 = f.fold_field_expression(statements_buffer, e1);
            let e2 = f.fold_field_expression(statements_buffer, e2);
            zir::BooleanExpression::FieldLe(box e1, box e2)
        }
        typed::BooleanExpression::FieldGt(box e1, box e2) => {
            let e1 = f.fold_field_expression(statements_buffer, e1);
            let e2 = f.fold_field_expression(statements_buffer, e2);
            zir::BooleanExpression::FieldLt(box e2, box e1)
        }
        typed::BooleanExpression::FieldGe(box e1, box e2) => {
            let e1 = f.fold_field_expression(statements_buffer, e1);
            let e2 = f.fold_field_expression(statements_buffer, e2);
            zir::BooleanExpression::FieldLe(box e2, box e1)
        }
        typed::BooleanExpression::UintLt(box e1, box e2) => {
            let e1 = f.fold_uint_expression(statements_buffer, e1);
            let e2 = f.fold_uint_expression(statements_buffer, e2);
            zir::BooleanExpression::UintLt(box e1, box e2)
        }
        typed::BooleanExpression::UintLe(box e1, box e2) => {
            let e1 = f.fold_uint_expression(statements_buffer, e1);
            let e2 = f.fold_uint_expression(statements_buffer, e2);
            zir::BooleanExpression::UintLe(box e1, box e2)
        }
        typed::BooleanExpression::UintGt(box e1, box e2) => {
            let e1 = f.fold_uint_expression(statements_buffer, e1);
            let e2 = f.fold_uint_expression(statements_buffer, e2);
            zir::BooleanExpression::UintLt(box e2, box e1)
        }
        typed::BooleanExpression::UintGe(box e1, box e2) => {
            let e1 = f.fold_uint_expression(statements_buffer, e1);
            let e2 = f.fold_uint_expression(statements_buffer, e2);
            zir::BooleanExpression::UintLe(box e2, box e1)
        }
        typed::BooleanExpression::Or(box e1, box e2) => {
            let e1 = f.fold_boolean_expression(statements_buffer, e1);
            let e2 = f.fold_boolean_expression(statements_buffer, e2);
            zir::BooleanExpression::Or(box e1, box e2)
        }
        typed::BooleanExpression::And(box e1, box e2) => {
            let e1 = f.fold_boolean_expression(statements_buffer, e1);
            let e2 = f.fold_boolean_expression(statements_buffer, e2);
            zir::BooleanExpression::And(box e1, box e2)
        }
        typed::BooleanExpression::Not(box e) => {
            let e = f.fold_boolean_expression(statements_buffer, e);
            zir::BooleanExpression::Not(box e)
        }
        typed::BooleanExpression::Conditional(c) => f
            .fold_conditional_expression(statements_buffer, c)
            .pop()
            .unwrap()
            .try_into()
            .unwrap(),
        typed::BooleanExpression::FunctionCall(..) => unreachable!(),
        typed::BooleanExpression::Select(select) => f
            .fold_select_expression(statements_buffer, select)
            .pop()
            .unwrap()
            .try_into()
            .unwrap(),
        typed::BooleanExpression::Member(m) => f
            .fold_member_expression(statements_buffer, m)
            .pop()
            .unwrap()
            .try_into()
            .unwrap(),
        typed::BooleanExpression::Element(m) => f
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
    e: typed::UExpression<'ast, T>,
) -> zir::UExpression<'ast, T> {
    f.fold_uint_expression_inner(statements_buffer, e.bitwidth, e.inner)
        .annotate(e.bitwidth.to_usize())
}

fn fold_uint_expression_inner<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    bitwidth: UBitwidth,
    e: typed::UExpressionInner<'ast, T>,
) -> zir::UExpressionInner<'ast, T> {
    match e {
        typed::UExpressionInner::Block(block) => {
            block
                .statements
                .into_iter()
                .for_each(|s| f.fold_statement(statements_buffer, s));
            f.fold_uint_expression(statements_buffer, *block.value)
                .into_inner()
        }
        typed::UExpressionInner::Value(v) => zir::UExpressionInner::Value(v),
        typed::UExpressionInner::Identifier(id) => zir::UExpressionInner::Identifier(
            flatten_identifier_rec(f.fold_name(id), &typed::types::ConcreteType::Uint(bitwidth))
                .pop()
                .unwrap()
                .id,
        ),
        typed::UExpressionInner::Add(box left, box right) => {
            let left = f.fold_uint_expression(statements_buffer, left);
            let right = f.fold_uint_expression(statements_buffer, right);

            zir::UExpressionInner::Add(box left, box right)
        }
        typed::UExpressionInner::Sub(box left, box right) => {
            let left = f.fold_uint_expression(statements_buffer, left);
            let right = f.fold_uint_expression(statements_buffer, right);

            zir::UExpressionInner::Sub(box left, box right)
        }
        typed::UExpressionInner::FloorSub(..) => unreachable!(),
        typed::UExpressionInner::Mult(box left, box right) => {
            let left = f.fold_uint_expression(statements_buffer, left);
            let right = f.fold_uint_expression(statements_buffer, right);

            zir::UExpressionInner::Mult(box left, box right)
        }
        typed::UExpressionInner::Div(box left, box right) => {
            let left = f.fold_uint_expression(statements_buffer, left);
            let right = f.fold_uint_expression(statements_buffer, right);

            zir::UExpressionInner::Div(box left, box right)
        }
        typed::UExpressionInner::Rem(box left, box right) => {
            let left = f.fold_uint_expression(statements_buffer, left);
            let right = f.fold_uint_expression(statements_buffer, right);

            zir::UExpressionInner::Rem(box left, box right)
        }
        typed::UExpressionInner::Xor(box left, box right) => {
            let left = f.fold_uint_expression(statements_buffer, left);
            let right = f.fold_uint_expression(statements_buffer, right);

            zir::UExpressionInner::Xor(box left, box right)
        }
        typed::UExpressionInner::And(box left, box right) => {
            let left = f.fold_uint_expression(statements_buffer, left);
            let right = f.fold_uint_expression(statements_buffer, right);

            zir::UExpressionInner::And(box left, box right)
        }
        typed::UExpressionInner::Or(box left, box right) => {
            let left = f.fold_uint_expression(statements_buffer, left);
            let right = f.fold_uint_expression(statements_buffer, right);

            zir::UExpressionInner::Or(box left, box right)
        }
        typed::UExpressionInner::LeftShift(box e, box by) => {
            let e = f.fold_uint_expression(statements_buffer, e);

            let by = match by.as_inner() {
                typed::UExpressionInner::Value(by) => by,
                _ => unreachable!("static analysis should have made sure that this is constant"),
            };

            zir::UExpressionInner::LeftShift(box e, *by as u32)
        }
        typed::UExpressionInner::RightShift(box e, box by) => {
            let e = f.fold_uint_expression(statements_buffer, e);

            let by = match by.as_inner() {
                typed::UExpressionInner::Value(by) => by,
                _ => unreachable!("static analysis should have made sure that this is constant"),
            };

            zir::UExpressionInner::RightShift(box e, *by as u32)
        }
        typed::UExpressionInner::Not(box e) => {
            let e = f.fold_uint_expression(statements_buffer, e);

            zir::UExpressionInner::Not(box e)
        }
        typed::UExpressionInner::Neg(box e) => {
            let bitwidth = e.bitwidth();

            f.fold_uint_expression(
                statements_buffer,
                typed::UExpressionInner::Value(0).annotate(bitwidth) - e,
            )
            .into_inner()
        }

        typed::UExpressionInner::Pos(box e) => {
            let e = f.fold_uint_expression(statements_buffer, e);

            e.into_inner()
        }
        typed::UExpressionInner::FunctionCall(..) => {
            unreachable!("function calls should have been removed")
        }
        typed::UExpressionInner::Select(select) => zir::UExpression::try_from(
            f.fold_select_expression(statements_buffer, select)
                .pop()
                .unwrap(),
        )
        .unwrap()
        .into_inner(),
        typed::UExpressionInner::Member(m) => zir::UExpression::try_from(
            f.fold_member_expression(statements_buffer, m)
                .pop()
                .unwrap(),
        )
        .unwrap()
        .into_inner(),
        typed::UExpressionInner::Element(m) => zir::UExpression::try_from(
            f.fold_element_expression(statements_buffer, m)
                .pop()
                .unwrap(),
        )
        .unwrap()
        .into_inner(),
        typed::UExpressionInner::Conditional(c) => zir::UExpression::try_from(
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
    fun: typed::TypedFunction<'ast, T>,
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
        signature: typed::types::ConcreteSignature::try_from(
            zokrates_ast::typed::types::try_from_g_signature::<
                zokrates_ast::typed::types::DeclarationConstant<'ast, T>,
                zokrates_ast::typed::UExpression<'ast, T>,
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
    e: typed::ArrayExpression<'ast, T>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    let size: u32 = e.size().try_into().unwrap();
    f.fold_array_expression_inner(
        statements_buffer,
        &typed::types::ConcreteType::try_from(e.inner_type().clone()).unwrap(),
        size,
        e.into_inner(),
    )
}

fn fold_struct_expression<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    e: typed::StructExpression<'ast, T>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    f.fold_struct_expression_inner(
        statements_buffer,
        &typed::types::ConcreteStructType::try_from(e.ty().clone()).unwrap(),
        e.into_inner(),
    )
}

fn fold_tuple_expression<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    e: typed::TupleExpression<'ast, T>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    f.fold_tuple_expression_inner(
        statements_buffer,
        &typed::types::ConcreteTupleType::try_from(e.ty().clone()).unwrap(),
        e.into_inner(),
    )
}

fn fold_program<'ast, T: Field>(
    f: &mut Flattener<T>,
    mut p: typed::TypedProgram<'ast, T>,
) -> zir::ZirProgram<'ast, T> {
    let main_module = p.modules.remove(&p.main).unwrap();

    let main_function = main_module
        .into_functions_iter()
        .find(|d| d.key.id == "main")
        .unwrap()
        .symbol;
    let main_function = match main_function {
        typed::TypedFunctionSymbol::Here(main) => main,
        _ => unreachable!(),
    };

    zir::ZirProgram {
        main: f.fold_function(main_function),
    }
}
