use std::collections::BTreeMap;
use std::convert::{TryFrom, TryInto};
use std::marker::PhantomData;
use std::ops::*;
use zokrates_ast::common::expressions::{BinaryExpression, ValueExpression};
use zokrates_ast::common::operators::OpEq;
use zokrates_ast::common::statements::LogStatement;
use zokrates_ast::common::{Span, WithSpan};
use zokrates_ast::typed::types::{ConcreteArrayType, IntoType, UBitwidth};
use zokrates_ast::typed::{self, Basic, Expr, Typed};
use zokrates_ast::zir::{self, Expr as ZirExpr, Folder, Id, MultipleDefinitionStatement, Select};
use zokrates_ast::zir::{IntoType as ZirIntoType, SourceIdentifier};
use zokrates_field::Field;

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
        typed::ConcreteType::FieldElement => vec![zir::Variable::new(
            zir::Identifier::Source(id),
            zir::Type::FieldElement,
        )],
        typed::types::ConcreteType::Boolean => vec![zir::Variable::new(
            zir::Identifier::Source(id),
            zir::Type::Boolean,
        )],
        typed::types::ConcreteType::Uint(bitwidth) => {
            vec![zir::Variable::new(
                zir::Identifier::Source(id),
                zir::Type::uint(bitwidth.to_usize()),
            )]
        }
        typed::types::ConcreteType::Array(array_type) => (0..*array_type.size)
            .flat_map(|i| {
                flatten_identifier_rec(SourceIdentifier::select(id.clone(), i), &array_type.ty)
            })
            .collect(),
        typed::types::ConcreteType::Struct(members) => members
            .iter()
            .flat_map(|struct_member| {
                flatten_identifier_rec(
                    SourceIdentifier::member(id.clone(), struct_member.id.clone()),
                    &struct_member.ty,
                )
            })
            .collect(),
        typed::types::ConcreteType::Tuple(tuple_ty) => tuple_ty
            .elements
            .iter()
            .enumerate()
            .flat_map(|(i, ty)| {
                flatten_identifier_rec(SourceIdentifier::element(id.clone(), i as u32), ty)
            })
            .collect(),
    }
}

fn flatten_identifier_to_expression_rec<'ast, T: Field>(
    id: zir::SourceIdentifier<'ast>,
    ty: &typed::types::ConcreteType,
) -> Vec<zir::ZirExpression<'ast, T>> {
    match ty {
        typed::ConcreteType::Int => unreachable!(),
        typed::ConcreteType::FieldElement => {
            vec![zir::FieldElementExpression::identifier(zir::Identifier::Source(id)).into()]
        }
        typed::ConcreteType::Boolean => {
            vec![zir::BooleanExpression::identifier(zir::Identifier::Source(id)).into()]
        }
        typed::ConcreteType::Uint(bitwidth) => {
            vec![zir::UExpression::identifier(zir::Identifier::Source(id))
                .annotate(bitwidth.to_usize())
                .into()]
        }
        typed::ConcreteType::Array(array_type) => (0..*array_type.size)
            .flat_map(|i| {
                flatten_identifier_to_expression_rec(
                    SourceIdentifier::select(id.clone(), i),
                    &array_type.ty,
                )
            })
            .collect(),
        typed::types::ConcreteType::Struct(members) => members
            .iter()
            .flat_map(|struct_member| {
                flatten_identifier_to_expression_rec(
                    SourceIdentifier::member(id.clone(), struct_member.id.clone()),
                    &struct_member.ty,
                )
            })
            .collect(),
        typed::types::ConcreteType::Tuple(tuple_ty) => tuple_ty
            .elements
            .iter()
            .enumerate()
            .flat_map(|(i, ty)| {
                flatten_identifier_to_expression_rec(
                    SourceIdentifier::element(id.clone(), i as u32),
                    ty,
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
        let span = p.get_span();

        let private = p.private;
        self.fold_variable(zokrates_ast::typed::variable::try_from_g_variable(p.id).unwrap())
            .into_iter()
            .map(|v| zir::Parameter::new(v, private).span(span))
            .collect()
    }

    fn fold_name(&mut self, n: typed::Identifier<'ast>) -> zir::SourceIdentifier<'ast> {
        SourceIdentifier::Basic(n)
    }

    fn fold_variable(&mut self, v: typed::Variable<'ast, T>) -> Vec<zir::Variable<'ast>> {
        let span = v.get_span();
        let ty = v.get_type();
        let id = self.fold_name(v.id);

        let ty = typed::types::ConcreteType::try_from(ty).unwrap();

        flatten_identifier_rec(id, &ty)
            .into_iter()
            .map(|v| v.span(span))
            .collect()
    }

    fn fold_assignee(&mut self, a: typed::TypedAssignee<'ast, T>) -> Vec<zir::ZirAssignee<'ast>> {
        match a {
            typed::TypedAssignee::Identifier(v) => self.fold_variable(v),
            typed::TypedAssignee::Select(a, i) => {
                let count = match typed::ConcreteType::try_from(a.get_type()).unwrap() {
                    typed::ConcreteType::Array(array_ty) => array_ty.ty.get_primitive_count(),
                    _ => unreachable!(),
                };
                let a = self.fold_assignee(*a);

                match i.as_inner() {
                    typed::UExpressionInner::Value(index) => {
                        a[index.value as usize * count..(index.value as usize + 1) * count].to_vec()
                    }
                    i => unreachable!("index {:?} not allowed, should be a constant", i),
                }
            }
            typed::TypedAssignee::Member(a, m) => {
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

                let a = self.fold_assignee(*a);

                a[offset..offset + size].to_vec()
            }
            typed::TypedAssignee::Element(a, index) => {
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

                let a = self.fold_assignee(*a);

                a[offset..offset + size].to_vec()
            }
        }
    }

    fn fold_assembly_statement(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        s: typed::TypedAssemblyStatement<'ast, T>,
    ) -> zir::ZirAssemblyStatement<'ast, T> {
        fold_assembly_statement(self, statements_buffer, s)
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

    fn fold_identifier_expression<E: Expr<'ast, T>>(
        &mut self,
        ty: E::ConcreteTy,
        e: typed::IdentifierExpression<'ast, E>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_identifier_expression(self, ty, e)
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

    fn fold_binary_expression<
        L: Flatten<'ast, T> + typed::Expr<'ast, T> + Basic<'ast, T>,
        R: Flatten<'ast, T> + typed::Expr<'ast, T> + Basic<'ast, T>,
        E: Flatten<'ast, T> + typed::Expr<'ast, T> + Basic<'ast, T>,
        Op,
    >(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        e: BinaryExpression<Op, L, R, E>,
    ) -> BinaryExpression<Op, L::ZirExpressionType, R::ZirExpressionType, E::ZirExpressionType>
    {
        fold_binary_expression(self, statements_buffer, e)
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
        eq: BinaryExpression<OpEq, E, E, typed::BooleanExpression<'ast, T>>,
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
        ty: typed::types::ConcreteType,
        size: u32,
        e: typed::ArrayExpressionInner<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_array_expression_inner(self, statements_buffer, ty, size, e)
    }

    fn fold_struct_expression_inner(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        ty: typed::types::ConcreteStructType,
        e: typed::StructExpressionInner<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_struct_expression_inner(self, statements_buffer, ty, e)
    }

    fn fold_tuple_expression_inner(
        &mut self,
        statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
        ty: typed::types::ConcreteTupleType,
        e: typed::TupleExpressionInner<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_tuple_expression_inner(self, statements_buffer, ty, e)
    }
}

// This finder looks for identifiers that were not defined in some block of statements
// These identifiers are used as function arguments when moving witness assignment expression
// to a zir function.
//
// Example:
// def main(field a, field mut b) -> field {
//     asm {
//         b <== a * a;
//     }
//     return b;
// }
// is turned into
// def main(field a, field mut b) -> field {
//     asm {
//         b <-- (field a) -> field {
//             return a * a;
//         }
//         b == a * a;
//     }
//     return b;
// }
#[derive(Default)]
pub struct ArgumentFinder<'ast, T> {
    pub identifiers: BTreeMap<zir::Identifier<'ast>, zir::Type>,
    _phantom: PhantomData<T>,
}

impl<'ast, T: Field> Folder<'ast, T> for ArgumentFinder<'ast, T> {
    fn fold_statement(&mut self, s: zir::ZirStatement<'ast, T>) -> Vec<zir::ZirStatement<'ast, T>> {
        match s {
            zir::ZirStatement::Definition(s) => {
                let assignee = self.fold_assignee(s.assignee);
                let expr = self.fold_expression(s.rhs);
                self.identifiers.remove(&assignee.id);
                vec![zir::ZirStatement::definition(assignee, expr)]
            }
            zir::ZirStatement::MultipleDefinition(s) => {
                let assignees: Vec<zir::ZirAssignee<'ast>> = s
                    .assignees
                    .into_iter()
                    .map(|v| self.fold_assignee(v))
                    .collect();
                let list = self.fold_expression_list(s.rhs);
                for a in &assignees {
                    self.identifiers.remove(&a.id);
                }
                vec![zir::ZirStatement::multiple_definition(assignees, list)]
            }
            s => zir::folder::fold_statement(self, s),
        }
    }

    fn fold_identifier_expression<E: zir::Expr<'ast, T> + Id<'ast, T>>(
        &mut self,
        ty: &E::Ty,
        e: zir::IdentifierExpression<'ast, E>,
    ) -> zir::IdentifierOrExpression<'ast, T, E> {
        self.identifiers
            .insert(e.id.clone(), ty.clone().into_type());
        zir::IdentifierOrExpression::Identifier(e)
    }
}

fn fold_assembly_statement<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    s: typed::TypedAssemblyStatement<'ast, T>,
) -> zir::ZirAssemblyStatement<'ast, T> {
    let span = s.get_span();

    match s {
        typed::TypedAssemblyStatement::Assignment(s) => {
            let mut statements_buffer: Vec<zir::ZirStatement<'ast, T>> = vec![];
            let a = f.fold_assignee(s.assignee);
            let e = f.fold_expression(&mut statements_buffer, s.expression);
            statements_buffer.push(zir::ZirStatement::ret(e));

            let mut finder = ArgumentFinder::default();
            let mut statements_buffer: Vec<zir::ZirStatement<'ast, T>> = statements_buffer
                .into_iter()
                .rev()
                .flat_map(|s| finder.fold_statement(s))
                .collect();
            statements_buffer.reverse();

            let function = zir::ZirFunction {
                signature: zir::types::Signature::default()
                    .inputs(finder.identifiers.values().cloned().collect())
                    .outputs(a.iter().map(|a| a.get_type()).collect()),
                arguments: finder
                    .identifiers
                    .into_iter()
                    .map(|(id, ty)| {
                        zir::Parameter::private(zir::Variable::with_id_and_type(id, ty))
                    })
                    .collect(),
                statements: statements_buffer,
            };

            zir::ZirAssemblyStatement::assignment(a, function)
        }
        typed::TypedAssemblyStatement::Constraint(s) => {
            let lhs = f.fold_field_expression(statements_buffer, s.left);
            let rhs = f.fold_field_expression(statements_buffer, s.right);
            zir::ZirAssemblyStatement::constraint(lhs, rhs, s.metadata)
        }
    }
    .span(span)
}

fn fold_statement<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    s: typed::TypedStatement<'ast, T>,
) {
    let span = s.get_span();

    let res = match s {
        typed::TypedStatement::Return(s) => vec![zir::ZirStatement::ret(
            f.fold_expression(statements_buffer, s.inner),
        )],
        typed::TypedStatement::Assembly(s) => {
            let statements = s
                .inner
                .into_iter()
                .map(|s| f.fold_assembly_statement(statements_buffer, s))
                .collect();
            vec![zir::ZirStatement::assembly(statements)]
        }
        typed::TypedStatement::Definition(typed::DefinitionStatement {
            assignee: a,
            rhs: typed::DefinitionRhs::Expression(e),
            ..
        }) => {
            let a = f.fold_assignee(a);
            let e = f.fold_expression(statements_buffer, e);
            assert_eq!(a.len(), e.len());
            a.into_iter()
                .zip(e.into_iter())
                .map(|(a, e)| zir::ZirStatement::definition(a, e))
                .collect()
        }
        typed::TypedStatement::Assertion(s) => {
            let e = f.fold_boolean_expression(statements_buffer, s.expression);
            let error = match s.error {
                typed::RuntimeError::SourceAssertion(metadata) => {
                    zir::RuntimeError::SourceAssertion(metadata)
                }
                typed::RuntimeError::SelectRangeCheck => zir::RuntimeError::SelectRangeCheck,
                typed::RuntimeError::DivisionByZero => zir::RuntimeError::DivisionByZero,
            };
            vec![zir::ZirStatement::assertion(e, error)]
        }
        typed::TypedStatement::Definition(typed::DefinitionStatement {
            assignee: a,
            rhs: typed::DefinitionRhs::EmbedCall(embed_call),
            ..
        }) => {
            vec![zir::ZirStatement::MultipleDefinition(
                MultipleDefinitionStatement::new(
                    f.fold_assignee(a),
                    zir::ZirExpressionList::EmbedCall(
                        embed_call.embed,
                        embed_call.generics,
                        embed_call
                            .arguments
                            .into_iter()
                            .flat_map(|a| f.fold_expression(statements_buffer, a))
                            .collect(),
                    ),
                ),
            )]
        }
        typed::TypedStatement::Log(e) => vec![zir::ZirStatement::Log(LogStatement::new(
            e.format_string,
            e.expressions
                .into_iter()
                .map(|e| {
                    (
                        e.get_type().try_into().unwrap(),
                        f.fold_expression(statements_buffer, e),
                    )
                })
                .collect(),
        ))],
        typed::TypedStatement::For(..) => unreachable!(),
    };

    statements_buffer.extend(res.into_iter().map(|s| s.span(span)));
}

fn fold_array_expression_inner<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    ty: typed::types::ConcreteType,
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
            f.fold_identifier_expression(ConcreteArrayType::new(ty, size), id)
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
        typed::ArrayExpressionInner::Slice(e) => {
            let array = f.fold_array_expression(statements_buffer, *e.array);
            let from = f.fold_uint_expression(statements_buffer, *e.from);
            let to = f.fold_uint_expression(statements_buffer, *e.to);

            match (from.into_inner(), to.into_inner()) {
                (zir::UExpressionInner::Value(from), zir::UExpressionInner::Value(to)) => {
                    assert_eq!(size, to.value.saturating_sub(from.value) as u32);

                    let element_size = ty.get_primitive_count();
                    let start = from.value as usize * element_size;
                    let end = to.value as usize * element_size;
                    array[start..end].to_vec()
                }
                _ => unreachable!(),
            }
        }
        typed::ArrayExpressionInner::Repeat(r) => {
            let e = f.fold_expression(statements_buffer, *r.e);
            let count = f.fold_uint_expression(statements_buffer, *r.count);

            match count.into_inner() {
                zir::UExpressionInner::Value(count) => vec![e; count.value as usize]
                    .into_iter()
                    .flatten()
                    .collect(),
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
    ty: typed::types::ConcreteStructType,
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
        typed::StructExpressionInner::Identifier(id) => f.fold_identifier_expression(ty, id),
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
    ty: typed::types::ConcreteTupleType,
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
        typed::TupleExpressionInner::Identifier(id) => f.fold_identifier_expression(ty, id),
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
            let v = v.value as usize;

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
    let span = c.get_span();
    let condition_span = c.condition.get_span();

    let mut consequence_statements = vec![];
    let mut alternative_statements = vec![];

    let condition = f.fold_boolean_expression(statements_buffer, *c.condition);
    let consequence = c.consequence.flatten(f, &mut consequence_statements);
    let alternative = c.alternative.flatten(f, &mut alternative_statements);

    assert_eq!(consequence.len(), alternative.len());

    if !consequence_statements.is_empty() || !alternative_statements.is_empty() {
        statements_buffer.push(
            zir::ZirStatement::if_else(
                condition.clone().span(condition_span),
                consequence_statements,
                alternative_statements,
            )
            .span(span),
        );
    }

    use zokrates_ast::zir::Conditional;

    consequence
        .into_iter()
        .zip(alternative.into_iter())
        .map(|(c, a)| match (c, a) {
            (zir::ZirExpression::FieldElement(c), zir::ZirExpression::FieldElement(a)) => {
                zir::FieldElementExpression::conditional(condition.clone(), c, a)
                    .span(span)
                    .into()
            }
            (zir::ZirExpression::Boolean(c), zir::ZirExpression::Boolean(a)) => {
                zir::BooleanExpression::conditional(condition.clone(), c, a)
                    .span(span)
                    .into()
            }
            (zir::ZirExpression::Uint(c), zir::ZirExpression::Uint(a)) => {
                zir::UExpression::conditional(condition.clone(), c, a)
                    .span(span)
                    .into()
            }
            _ => unreachable!(),
        })
        .collect()
}

fn fold_binary_expression<
    'ast,
    T: Field,
    L: Flatten<'ast, T> + typed::Expr<'ast, T> + Basic<'ast, T>,
    R: Flatten<'ast, T> + typed::Expr<'ast, T> + Basic<'ast, T>,
    E: Flatten<'ast, T> + typed::Expr<'ast, T> + Basic<'ast, T>,
    Op,
>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    e: BinaryExpression<Op, L, R, E>,
) -> BinaryExpression<Op, L::ZirExpressionType, R::ZirExpressionType, E::ZirExpressionType> {
    let left_span = e.left.get_span();
    let right_span = e.left.get_span();

    let left: L::ZirExpressionType = e.left.flatten(f, statements_buffer).pop().unwrap().into();
    let right: R::ZirExpressionType = e.right.flatten(f, statements_buffer).pop().unwrap().into();

    BinaryExpression::new(left.span(left_span), right.span(right_span)).span(e.span)
}

fn fold_identifier_expression<'ast, T: Field, E: Expr<'ast, T>>(
    f: &mut Flattener<T>,
    ty: E::ConcreteTy,
    e: typed::IdentifierExpression<'ast, E>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    flatten_identifier_to_expression_rec(f.fold_name(e.id), &ty.into_type())
}

fn fold_field_expression<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    e: typed::FieldElementExpression<'ast, T>,
) -> zir::FieldElementExpression<'ast, T> {
    let span = e.get_span();

    match e {
        typed::FieldElementExpression::Value(n) => zir::FieldElementExpression::Value(n),
        typed::FieldElementExpression::Identifier(id) => f
            .fold_identifier_expression(typed::ConcreteType::FieldElement, id)
            .pop()
            .unwrap()
            .try_into()
            .unwrap(),
        typed::FieldElementExpression::Add(e) => {
            zir::FieldElementExpression::Add(f.fold_binary_expression(statements_buffer, e))
        }
        typed::FieldElementExpression::Sub(e) => {
            zir::FieldElementExpression::Sub(f.fold_binary_expression(statements_buffer, e))
        }
        typed::FieldElementExpression::Mult(e) => {
            zir::FieldElementExpression::Mult(f.fold_binary_expression(statements_buffer, e))
        }
        typed::FieldElementExpression::Div(e) => {
            zir::FieldElementExpression::Div(f.fold_binary_expression(statements_buffer, e))
        }
        typed::FieldElementExpression::Pow(e) => {
            zir::FieldElementExpression::Pow(f.fold_binary_expression(statements_buffer, e))
        }
        typed::FieldElementExpression::And(e) => {
            zir::FieldElementExpression::And(f.fold_binary_expression(statements_buffer, e))
        }
        typed::FieldElementExpression::Or(e) => {
            zir::FieldElementExpression::Or(f.fold_binary_expression(statements_buffer, e))
        }
        typed::FieldElementExpression::Xor(e) => {
            zir::FieldElementExpression::Xor(f.fold_binary_expression(statements_buffer, e))
        }
        typed::FieldElementExpression::LeftShift(e) => {
            zir::FieldElementExpression::LeftShift(f.fold_binary_expression(statements_buffer, e))
        }
        typed::FieldElementExpression::RightShift(e) => {
            zir::FieldElementExpression::RightShift(f.fold_binary_expression(statements_buffer, e))
        }
        typed::FieldElementExpression::Neg(e) => {
            let e = f.fold_field_expression(statements_buffer, *e.inner);

            zir::FieldElementExpression::sub(
                zir::FieldElementExpression::Value(ValueExpression::new(T::zero())),
                e,
            )
        }
        typed::FieldElementExpression::Pos(e) => {
            f.fold_field_expression(statements_buffer, *e.inner)
        }
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
    .span(span)
}

// util function to output a boolean expression representing the equality of two lists of ZirExpression.
// the two list are checked to have the same size
// we build a binary tree with internal nodes `And(left, right)` and leaves `Eq(left, right)`
fn conjunction_tree<'ast, T: Field>(
    v: &[zir::ZirExpression<'ast, T>],
    w: &[zir::ZirExpression<'ast, T>],
    span: Option<Span>,
) -> zir::BooleanExpression<'ast, T> {
    assert_eq!(v.len(), w.len());

    match v.len() {
        0 => zir::BooleanExpression::value(true),
        1 => match (v[0].clone(), w[0].clone()) {
            (zir::ZirExpression::Boolean(v), zir::ZirExpression::Boolean(w)) => {
                zir::BooleanExpression::bool_eq(v, w).span(span)
            }
            (zir::ZirExpression::FieldElement(v), zir::ZirExpression::FieldElement(w)) => {
                zir::BooleanExpression::field_eq(v, w).span(span)
            }
            (zir::ZirExpression::Uint(v), zir::ZirExpression::Uint(w)) => {
                zir::BooleanExpression::uint_eq(v, w).span(span)
            }
            _ => unreachable!(),
        },
        n => {
            let (x0, y0) = v.split_at(n / 2);
            let (x1, y1) = w.split_at(n / 2);
            zir::BooleanExpression::bitand(
                conjunction_tree(x0, x1, span),
                conjunction_tree(y0, y1, span),
            )
            .span(span)
        }
    }
}

fn fold_eq_expression<'ast, T: Field, E: Flatten<'ast, T>>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    e: zokrates_ast::common::expressions::BinaryExpression<
        OpEq,
        E,
        E,
        typed::BooleanExpression<'ast, T>,
    >,
) -> zir::BooleanExpression<'ast, T> {
    let span = e.get_span();

    let left = e.left.flatten(f, statements_buffer);
    let right = e.right.flatten(f, statements_buffer);
    conjunction_tree(&left, &right, span)
}

fn fold_boolean_expression<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    e: typed::BooleanExpression<'ast, T>,
) -> zir::BooleanExpression<'ast, T> {
    let span = e.get_span();

    match e {
        typed::BooleanExpression::Block(block) => {
            block
                .statements
                .into_iter()
                .for_each(|s| f.fold_statement(statements_buffer, s));
            f.fold_boolean_expression(statements_buffer, *block.value)
        }
        typed::BooleanExpression::Value(v) => zir::BooleanExpression::Value(v),
        typed::BooleanExpression::Identifier(id) => f
            .fold_identifier_expression(typed::ConcreteType::Boolean, id)
            .pop()
            .unwrap()
            .try_into()
            .unwrap(),
        typed::BooleanExpression::FieldEq(e) => f.fold_eq_expression(statements_buffer, e),
        typed::BooleanExpression::BoolEq(e) => f.fold_eq_expression(statements_buffer, e),
        typed::BooleanExpression::ArrayEq(e) => f.fold_eq_expression(statements_buffer, e),
        typed::BooleanExpression::StructEq(e) => f.fold_eq_expression(statements_buffer, e),
        typed::BooleanExpression::TupleEq(e) => f.fold_eq_expression(statements_buffer, e),
        typed::BooleanExpression::UintEq(e) => f.fold_eq_expression(statements_buffer, e),
        typed::BooleanExpression::FieldLt(e) => {
            zir::BooleanExpression::FieldLt(f.fold_binary_expression(statements_buffer, e))
        }
        typed::BooleanExpression::FieldLe(e) => {
            zir::BooleanExpression::FieldLe(f.fold_binary_expression(statements_buffer, e))
        }
        typed::BooleanExpression::UintLt(e) => {
            zir::BooleanExpression::UintLt(f.fold_binary_expression(statements_buffer, e))
        }
        typed::BooleanExpression::UintLe(e) => {
            zir::BooleanExpression::UintLe(f.fold_binary_expression(statements_buffer, e))
        }
        typed::BooleanExpression::Or(e) => {
            zir::BooleanExpression::Or(f.fold_binary_expression(statements_buffer, e))
        }
        typed::BooleanExpression::And(e) => {
            zir::BooleanExpression::And(f.fold_binary_expression(statements_buffer, e))
        }
        typed::BooleanExpression::Not(e) => {
            zir::BooleanExpression::not(f.fold_boolean_expression(statements_buffer, *e.inner))
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
    .span(span)
}

fn fold_uint_expression<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    e: typed::UExpression<'ast, T>,
) -> zir::UExpression<'ast, T> {
    let span = e.get_span();
    f.fold_uint_expression_inner(statements_buffer, e.bitwidth, e.inner)
        .annotate(e.bitwidth.to_usize())
        .span(span)
}

fn fold_uint_expression_inner<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    bitwidth: UBitwidth,
    e: typed::UExpressionInner<'ast, T>,
) -> zir::UExpressionInner<'ast, T> {
    let span = e.get_span();

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
        typed::UExpressionInner::Identifier(id) => {
            zir::UExpression::try_from(f.fold_identifier_expression(bitwidth, id).pop().unwrap())
                .unwrap()
                .into_inner()
        }
        typed::UExpressionInner::Add(e) => {
            let left = f.fold_uint_expression(statements_buffer, *e.left);
            let right = f.fold_uint_expression(statements_buffer, *e.right);

            zir::UExpression::add(left, right).into_inner()
        }
        typed::UExpressionInner::Sub(e) => {
            let left = f.fold_uint_expression(statements_buffer, *e.left);
            let right = f.fold_uint_expression(statements_buffer, *e.right);

            zir::UExpression::sub(left, right).into_inner()
        }
        typed::UExpressionInner::FloorSub(..) => unreachable!(),
        typed::UExpressionInner::Mult(e) => {
            let left = f.fold_uint_expression(statements_buffer, *e.left);
            let right = f.fold_uint_expression(statements_buffer, *e.right);

            zir::UExpression::mult(left, right).into_inner()
        }
        typed::UExpressionInner::Div(e) => {
            let left = f.fold_uint_expression(statements_buffer, *e.left);
            let right = f.fold_uint_expression(statements_buffer, *e.right);

            zir::UExpression::div(left, right).into_inner()
        }
        typed::UExpressionInner::Rem(e) => {
            let left = f.fold_uint_expression(statements_buffer, *e.left);
            let right = f.fold_uint_expression(statements_buffer, *e.right);

            zir::UExpression::rem(left, right).into_inner()
        }
        typed::UExpressionInner::Xor(e) => {
            let left = f.fold_uint_expression(statements_buffer, *e.left);
            let right = f.fold_uint_expression(statements_buffer, *e.right);

            zir::UExpression::xor(left, right).into_inner()
        }
        typed::UExpressionInner::And(e) => {
            let left = f.fold_uint_expression(statements_buffer, *e.left);
            let right = f.fold_uint_expression(statements_buffer, *e.right);

            zir::UExpression::and(left, right).into_inner()
        }
        typed::UExpressionInner::Or(e) => {
            let left = f.fold_uint_expression(statements_buffer, *e.left);
            let right = f.fold_uint_expression(statements_buffer, *e.right);

            zir::UExpression::or(left, right).into_inner()
        }
        typed::UExpressionInner::LeftShift(e) => {
            let left = f.fold_uint_expression(statements_buffer, *e.left);
            let right = f.fold_uint_expression(statements_buffer, *e.right);

            zir::UExpression::left_shift(left, right).into_inner()
        }
        typed::UExpressionInner::RightShift(e) => {
            let left = f.fold_uint_expression(statements_buffer, *e.left);
            let right = f.fold_uint_expression(statements_buffer, *e.right);

            zir::UExpression::right_shift(left, right).into_inner()
        }
        typed::UExpressionInner::Not(e) => {
            zir::UExpression::not(f.fold_uint_expression(statements_buffer, *e.inner)).into_inner()
        }
        typed::UExpressionInner::Neg(e) => {
            let bitwidth = e.inner.bitwidth();

            f.fold_uint_expression(
                statements_buffer,
                typed::UExpression::value(0).annotate(bitwidth) - *e.inner,
            )
            .into_inner()
        }

        typed::UExpressionInner::Pos(e) => f
            .fold_uint_expression(statements_buffer, *e.inner)
            .into_inner(),
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
    .span(span)
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
    let span = e.get_span();
    let size: u32 = e.size().try_into().unwrap();
    f.fold_array_expression_inner(
        statements_buffer,
        typed::types::ConcreteType::try_from(e.inner_type().clone()).unwrap(),
        size,
        e.into_inner(),
    )
    .into_iter()
    .map(|e| e.span(span))
    .collect()
}

fn fold_struct_expression<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    e: typed::StructExpression<'ast, T>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    let span = e.get_span();
    f.fold_struct_expression_inner(
        statements_buffer,
        typed::types::ConcreteStructType::try_from(e.ty().clone()).unwrap(),
        e.into_inner(),
    )
    .into_iter()
    .map(|e| e.span(span))
    .collect()
}

fn fold_tuple_expression<'ast, T: Field>(
    f: &mut Flattener<T>,
    statements_buffer: &mut Vec<zir::ZirStatement<'ast, T>>,
    e: typed::TupleExpression<'ast, T>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    let span = e.get_span();
    f.fold_tuple_expression_inner(
        statements_buffer,
        typed::types::ConcreteTupleType::try_from(e.ty().clone()).unwrap(),
        e.into_inner(),
    )
    .into_iter()
    .map(|e| e.span(span))
    .collect()
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
        module_map: p.module_map,
    }
}
