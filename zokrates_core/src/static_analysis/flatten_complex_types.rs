use crate::typed_absy;
use crate::typed_absy::types::{StructType, UBitwidth};
use crate::zir;
use std::marker::PhantomData;
use zokrates_field::Field;

pub struct Flattener<T: Field> {
    phantom: PhantomData<T>,
}

fn flatten_identifier_rec<'a>(
    id: zir::SourceIdentifier<'a>,
    ty: &typed_absy::Type,
) -> Vec<zir::Variable<'a>> {
    match ty {
        typed_absy::Type::FieldElement => vec![zir::Variable {
            id: zir::Identifier::Source(id),
            _type: zir::Type::FieldElement,
        }],
        typed_absy::Type::Boolean => vec![zir::Variable {
            id: zir::Identifier::Source(id),
            _type: zir::Type::Boolean,
        }],
        typed_absy::Type::Uint(bitwidth) => vec![zir::Variable {
            id: zir::Identifier::Source(id),
            _type: zir::Type::uint(bitwidth.to_usize()),
        }],
        typed_absy::Type::Array(array_type) => (0..array_type.size)
            .flat_map(|i| {
                flatten_identifier_rec(
                    zir::SourceIdentifier::Select(box id.clone(), i),
                    &array_type.ty,
                )
            })
            .collect(),
        typed_absy::Type::Struct(members) => members
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

impl<'ast, T: Field> Flattener<T> {
    pub fn flatten(p: typed_absy::TypedProgram<T>) -> zir::ZirProgram<T> {
        let mut f = Flattener {
            phantom: PhantomData,
        };
        f.fold_program(p)
    }

    fn fold_program(&mut self, p: typed_absy::TypedProgram<'ast, T>) -> zir::ZirProgram<'ast, T> {
        fold_program(self, p)
    }

    fn fold_module(&mut self, p: typed_absy::TypedModule<'ast, T>) -> zir::ZirModule<'ast, T> {
        fold_module(self, p)
    }

    fn fold_function_symbol(
        &mut self,
        s: typed_absy::TypedFunctionSymbol<'ast, T>,
    ) -> zir::ZirFunctionSymbol<'ast, T> {
        fold_function_symbol(self, s)
    }

    fn fold_function(
        &mut self,
        f: typed_absy::TypedFunction<'ast, T>,
    ) -> zir::ZirFunction<'ast, T> {
        fold_function(self, f)
    }

    fn fold_parameter(&mut self, p: typed_absy::Parameter<'ast>) -> Vec<zir::Parameter<'ast>> {
        let private = p.private;
        self.fold_variable(p.id)
            .into_iter()
            .map(|v| zir::Parameter { id: v, private })
            .collect()
    }

    fn fold_name(&mut self, n: typed_absy::Identifier<'ast>) -> zir::SourceIdentifier<'ast> {
        zir::SourceIdentifier::Basic(n)
    }

    fn fold_variable(&mut self, v: typed_absy::Variable<'ast>) -> Vec<zir::Variable<'ast>> {
        let id = self.fold_name(v.id.clone());
        let ty = v.get_type();

        flatten_identifier_rec(id, &ty)
    }

    fn fold_assignee(
        &mut self,
        a: typed_absy::TypedAssignee<'ast, T>,
    ) -> Vec<zir::ZirAssignee<'ast>> {
        match a {
            typed_absy::TypedAssignee::Identifier(v) => self.fold_variable(v),
            _ => unreachable!(),
        }
    }

    fn fold_statement(
        &mut self,
        s: typed_absy::TypedStatement<'ast, T>,
    ) -> Vec<zir::ZirStatement<'ast, T>> {
        fold_statement(self, s)
    }

    fn fold_expression(
        &mut self,
        e: typed_absy::TypedExpression<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        match e {
            typed_absy::TypedExpression::FieldElement(e) => {
                vec![self.fold_field_expression(e).into()]
            }
            typed_absy::TypedExpression::Boolean(e) => vec![self.fold_boolean_expression(e).into()],
            typed_absy::TypedExpression::Uint(e) => vec![self.fold_uint_expression(e).into()],
            typed_absy::TypedExpression::Array(e) => self.fold_array_expression(e),
            typed_absy::TypedExpression::Struct(e) => self.fold_struct_expression(e),
        }
    }

    fn fold_array_expression(
        &mut self,
        e: typed_absy::ArrayExpression<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_array_expression(self, e)
    }

    fn fold_struct_expression(
        &mut self,
        e: typed_absy::StructExpression<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_struct_expression(self, e)
    }

    fn fold_expression_list(
        &mut self,
        es: typed_absy::TypedExpressionList<'ast, T>,
    ) -> zir::ZirExpressionList<'ast, T> {
        match es {
            typed_absy::TypedExpressionList::FunctionCall(id, arguments, _) => {
                zir::ZirExpressionList::FunctionCall(
                    self.fold_function_key(id),
                    arguments
                        .into_iter()
                        .flat_map(|a| self.fold_expression(a))
                        .collect(),
                    vec![],
                )
            }
        }
    }

    fn fold_function_key(
        &mut self,
        k: typed_absy::types::FunctionKey<'ast>,
    ) -> zir::types::FunctionKey<'ast> {
        k.into()
    }

    fn fold_field_expression(
        &mut self,
        e: typed_absy::FieldElementExpression<'ast, T>,
    ) -> zir::FieldElementExpression<'ast, T> {
        fold_field_expression(self, e)
    }
    fn fold_boolean_expression(
        &mut self,
        e: typed_absy::BooleanExpression<'ast, T>,
    ) -> zir::BooleanExpression<'ast, T> {
        fold_boolean_expression(self, e)
    }
    fn fold_uint_expression(
        &mut self,
        e: typed_absy::UExpression<'ast, T>,
    ) -> zir::UExpression<'ast, T> {
        fold_uint_expression(self, e)
    }

    fn fold_uint_expression_inner(
        &mut self,
        bitwidth: UBitwidth,
        e: typed_absy::UExpressionInner<'ast, T>,
    ) -> zir::UExpressionInner<'ast, T> {
        fold_uint_expression_inner(self, bitwidth, e)
    }

    fn fold_array_expression_inner(
        &mut self,
        ty: &typed_absy::Type,
        size: usize,
        e: typed_absy::ArrayExpressionInner<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_array_expression_inner(self, ty, size, e)
    }
    fn fold_struct_expression_inner(
        &mut self,
        ty: &StructType,
        e: typed_absy::StructExpressionInner<'ast, T>,
    ) -> Vec<zir::ZirExpression<'ast, T>> {
        fold_struct_expression_inner(self, ty, e)
    }
}

pub fn fold_module<'ast, T: Field>(
    f: &mut Flattener<T>,
    p: typed_absy::TypedModule<'ast, T>,
) -> zir::ZirModule<'ast, T> {
    zir::ZirModule {
        functions: p
            .functions
            .into_iter()
            .map(|(key, fun)| (f.fold_function_key(key), f.fold_function_symbol(fun)))
            .collect(),
    }
}

pub fn fold_statement<'ast, T: Field>(
    f: &mut Flattener<T>,
    s: typed_absy::TypedStatement<'ast, T>,
) -> Vec<zir::ZirStatement<'ast, T>> {
    match s {
        typed_absy::TypedStatement::Return(expressions) => vec![zir::ZirStatement::Return(
            expressions
                .into_iter()
                .flat_map(|e| f.fold_expression(e))
                .collect(),
        )],
        typed_absy::TypedStatement::Definition(a, e) => {
            let a = f.fold_assignee(a);
            let e = f.fold_expression(e);
            assert_eq!(a.len(), e.len());
            a.into_iter()
                .zip(e.into_iter())
                .map(|(a, e)| zir::ZirStatement::Definition(a, e))
                .collect()
        }
        typed_absy::TypedStatement::Declaration(v) => {
            let v = f.fold_variable(v);
            v.into_iter().map(zir::ZirStatement::Declaration).collect()
        }
        typed_absy::TypedStatement::Assertion(e) => {
            let e = f.fold_boolean_expression(e);
            vec![zir::ZirStatement::Assertion(e)]
        }
        typed_absy::TypedStatement::For(..) => unreachable!(),
        typed_absy::TypedStatement::MultipleDefinition(variables, elist) => {
            vec![zir::ZirStatement::MultipleDefinition(
                variables
                    .into_iter()
                    .flat_map(|v| f.fold_variable(v))
                    .collect(),
                f.fold_expression_list(elist),
            )]
        }
    }
}

pub fn fold_array_expression_inner<'ast, T: Field>(
    f: &mut Flattener<T>,
    ty: &typed_absy::Type,
    size: usize,
    array: typed_absy::ArrayExpressionInner<'ast, T>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    match array {
        typed_absy::ArrayExpressionInner::Identifier(id) => {
            let variables =
                flatten_identifier_rec(f.fold_name(id), &typed_absy::Type::array(ty.clone(), size));
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
        typed_absy::ArrayExpressionInner::Value(exprs) => exprs
            .into_iter()
            .flat_map(|e| f.fold_expression(e))
            .collect(),
        typed_absy::ArrayExpressionInner::FunctionCall(..) => unreachable!(),
        typed_absy::ArrayExpressionInner::IfElse(
            box condition,
            box consequence,
            box alternative,
        ) => {
            let condition = f.fold_boolean_expression(condition);
            let consequence = f.fold_array_expression(consequence);
            let alternative = f.fold_array_expression(alternative);

            assert_eq!(consequence.len(), alternative.len());

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
        typed_absy::ArrayExpressionInner::Member(box s, id) => {
            let members = s.ty().clone();

            let s = f.fold_struct_expression(s);

            let offset: usize = members
                .iter()
                .take_while(|member| member.id != id)
                .map(|member| member.ty.get_primitive_count())
                .sum();

            // we also need the size of this member
            let size = ty.get_primitive_count() * size;

            s[offset..offset + size].to_vec()
        }
        typed_absy::ArrayExpressionInner::Select(box array, box index) => {
            let array = f.fold_array_expression(array);
            let index = f.fold_field_expression(index);

            match index {
                zir::FieldElementExpression::Number(i) => {
                    let size = ty.get_primitive_count() * size;
                    let start = i.to_dec_string().parse::<usize>().unwrap() * size;
                    let end = start + size;
                    array[start..end].to_vec()
                }
                _ => unreachable!(),
            }
        }
    }
}

pub fn fold_struct_expression_inner<'ast, T: Field>(
    f: &mut Flattener<T>,
    ty: &StructType,
    struc: typed_absy::StructExpressionInner<'ast, T>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    match struc {
        typed_absy::StructExpressionInner::Identifier(id) => {
            let variables =
                flatten_identifier_rec(f.fold_name(id), &typed_absy::Type::struc(ty.clone()));
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
            .flat_map(|e| f.fold_expression(e))
            .collect(),
        typed_absy::StructExpressionInner::FunctionCall(..) => unreachable!(),
        typed_absy::StructExpressionInner::IfElse(
            box condition,
            box consequence,
            box alternative,
        ) => {
            let condition = f.fold_boolean_expression(condition);
            let consequence = f.fold_struct_expression(consequence);
            let alternative = f.fold_struct_expression(alternative);

            assert_eq!(consequence.len(), alternative.len());

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
        typed_absy::StructExpressionInner::Member(box s, id) => {
            let members = s.ty().clone();

            let s = f.fold_struct_expression(s);

            let offset: usize = members
                .iter()
                .take_while(|member| member.id != id)
                .map(|member| member.ty.get_primitive_count())
                .sum();

            // we also need the size of this member
            let size = ty
                .iter()
                .find(|member| member.id == id)
                .unwrap()
                .ty
                .get_primitive_count();

            s[offset..offset + size].to_vec()
        }
        typed_absy::StructExpressionInner::Select(box array, box index) => {
            let array = f.fold_array_expression(array);
            let index = f.fold_field_expression(index);

            match index {
                zir::FieldElementExpression::Number(i) => {
                    let size: usize = ty.iter().map(|m| m.ty.get_primitive_count()).sum();
                    let start = i.to_dec_string().parse::<usize>().unwrap() * size;
                    let end = start + size;
                    array[start..end].to_vec()
                }
                _ => unreachable!(),
            }
        }
    }
}

pub fn fold_field_expression<'ast, T: Field>(
    f: &mut Flattener<T>,
    e: typed_absy::FieldElementExpression<'ast, T>,
) -> zir::FieldElementExpression<'ast, T> {
    match e {
        typed_absy::FieldElementExpression::Number(n) => zir::FieldElementExpression::Number(n),
        typed_absy::FieldElementExpression::Identifier(id) => {
            zir::FieldElementExpression::Identifier(
                flatten_identifier_rec(f.fold_name(id), &typed_absy::Type::FieldElement)[0]
                    .id
                    .clone(),
            )
        }
        typed_absy::FieldElementExpression::Add(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            zir::FieldElementExpression::Add(box e1, box e2)
        }
        typed_absy::FieldElementExpression::Sub(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            zir::FieldElementExpression::Sub(box e1, box e2)
        }
        typed_absy::FieldElementExpression::Mult(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            zir::FieldElementExpression::Mult(box e1, box e2)
        }
        typed_absy::FieldElementExpression::Div(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            zir::FieldElementExpression::Div(box e1, box e2)
        }
        typed_absy::FieldElementExpression::Pow(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            zir::FieldElementExpression::Pow(box e1, box e2)
        }
        typed_absy::FieldElementExpression::IfElse(box cond, box cons, box alt) => {
            let cond = f.fold_boolean_expression(cond);
            let cons = f.fold_field_expression(cons);
            let alt = f.fold_field_expression(alt);
            zir::FieldElementExpression::IfElse(box cond, box cons, box alt)
        }
        typed_absy::FieldElementExpression::FunctionCall(..) => unreachable!(""),
        typed_absy::FieldElementExpression::Member(box s, id) => {
            let members = s.ty().clone();

            let s = f.fold_struct_expression(s);

            let offset: usize = members
                .iter()
                .take_while(|member| member.id != id)
                .map(|member| member.ty.get_primitive_count())
                .sum();

            use std::convert::TryInto;

            s[offset].clone().try_into().unwrap()
        }
        typed_absy::FieldElementExpression::Select(box array, box index) => {
            let array = f.fold_array_expression(array);

            let index = f.fold_field_expression(index);

            use std::convert::TryInto;

            match index {
                zir::FieldElementExpression::Number(i) => array
                    [i.to_dec_string().parse::<usize>().unwrap()]
                .clone()
                .try_into()
                .unwrap(),
                _ => unreachable!(""),
            }
        }
    }
}

pub fn fold_boolean_expression<'ast, T: Field>(
    f: &mut Flattener<T>,
    e: typed_absy::BooleanExpression<'ast, T>,
) -> zir::BooleanExpression<'ast, T> {
    match e {
        typed_absy::BooleanExpression::Value(v) => zir::BooleanExpression::Value(v),
        typed_absy::BooleanExpression::Identifier(id) => zir::BooleanExpression::Identifier(
            flatten_identifier_rec(f.fold_name(id), &typed_absy::Type::Boolean)[0]
                .id
                .clone(),
        ),
        typed_absy::BooleanExpression::FieldEq(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            zir::BooleanExpression::FieldEq(box e1, box e2)
        }
        typed_absy::BooleanExpression::BoolEq(box e1, box e2) => {
            let e1 = f.fold_boolean_expression(e1);
            let e2 = f.fold_boolean_expression(e2);
            zir::BooleanExpression::BoolEq(box e1, box e2)
        }
        typed_absy::BooleanExpression::ArrayEq(box e1, box e2) => {
            let e1 = f.fold_array_expression(e1);
            let e2 = f.fold_array_expression(e2);

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
            let e1 = f.fold_struct_expression(e1);
            let e2 = f.fold_struct_expression(e2);

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
            let e1 = f.fold_uint_expression(e1);
            let e2 = f.fold_uint_expression(e2);

            zir::BooleanExpression::UintEq(box e1, box e2)
        }
        typed_absy::BooleanExpression::Lt(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            zir::BooleanExpression::Lt(box e1, box e2)
        }
        typed_absy::BooleanExpression::Le(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            zir::BooleanExpression::Le(box e1, box e2)
        }
        typed_absy::BooleanExpression::Gt(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            zir::BooleanExpression::Gt(box e1, box e2)
        }
        typed_absy::BooleanExpression::Ge(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            zir::BooleanExpression::Ge(box e1, box e2)
        }
        typed_absy::BooleanExpression::Or(box e1, box e2) => {
            let e1 = f.fold_boolean_expression(e1);
            let e2 = f.fold_boolean_expression(e2);
            zir::BooleanExpression::Or(box e1, box e2)
        }
        typed_absy::BooleanExpression::And(box e1, box e2) => {
            let e1 = f.fold_boolean_expression(e1);
            let e2 = f.fold_boolean_expression(e2);
            zir::BooleanExpression::And(box e1, box e2)
        }
        typed_absy::BooleanExpression::Not(box e) => {
            let e = f.fold_boolean_expression(e);
            zir::BooleanExpression::Not(box e)
        }
        typed_absy::BooleanExpression::IfElse(box cond, box cons, box alt) => {
            let cond = f.fold_boolean_expression(cond);
            let cons = f.fold_boolean_expression(cons);
            let alt = f.fold_boolean_expression(alt);
            zir::BooleanExpression::IfElse(box cond, box cons, box alt)
        }
        typed_absy::BooleanExpression::FunctionCall(..) => unreachable!(),
        typed_absy::BooleanExpression::Member(box s, id) => {
            let members = s.ty().clone();

            let s = f.fold_struct_expression(s);

            let offset: usize = members
                .iter()
                .take_while(|member| member.id != id)
                .map(|member| member.ty.get_primitive_count())
                .sum();

            use std::convert::TryInto;

            s[offset].clone().try_into().unwrap()
        }
        typed_absy::BooleanExpression::Select(box array, box index) => {
            let array = f.fold_array_expression(array);
            let index = f.fold_field_expression(index);

            use std::convert::TryInto;

            match index {
                zir::FieldElementExpression::Number(i) => array
                    [i.to_dec_string().parse::<usize>().unwrap()]
                .clone()
                .try_into()
                .unwrap(),
                _ => unreachable!(),
            }
        }
    }
}

pub fn fold_uint_expression<'ast, T: Field>(
    f: &mut Flattener<T>,
    e: typed_absy::UExpression<'ast, T>,
) -> zir::UExpression<'ast, T> {
    f.fold_uint_expression_inner(e.bitwidth, e.inner)
        .annotate(e.bitwidth.to_usize())
}

pub fn fold_uint_expression_inner<'ast, T: Field>(
    f: &mut Flattener<T>,
    bitwidth: UBitwidth,
    e: typed_absy::UExpressionInner<'ast, T>,
) -> zir::UExpressionInner<'ast, T> {
    match e {
        typed_absy::UExpressionInner::Value(v) => zir::UExpressionInner::Value(v),
        typed_absy::UExpressionInner::Identifier(id) => zir::UExpressionInner::Identifier(
            flatten_identifier_rec(f.fold_name(id), &typed_absy::Type::Uint(bitwidth))[0]
                .id
                .clone(),
        ),
        typed_absy::UExpressionInner::Add(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            zir::UExpressionInner::Add(box left, box right)
        }
        typed_absy::UExpressionInner::Sub(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            zir::UExpressionInner::Sub(box left, box right)
        }
        typed_absy::UExpressionInner::Mult(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            zir::UExpressionInner::Mult(box left, box right)
        }
        typed_absy::UExpressionInner::Div(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            zir::UExpressionInner::Div(box left, box right)
        }
        typed_absy::UExpressionInner::Rem(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            zir::UExpressionInner::Rem(box left, box right)
        }
        typed_absy::UExpressionInner::Xor(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            zir::UExpressionInner::Xor(box left, box right)
        }
        typed_absy::UExpressionInner::And(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            zir::UExpressionInner::And(box left, box right)
        }
        typed_absy::UExpressionInner::Or(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            zir::UExpressionInner::Or(box left, box right)
        }
        typed_absy::UExpressionInner::LeftShift(box e, box by) => {
            let e = f.fold_uint_expression(e);
            let by = f.fold_field_expression(by);

            zir::UExpressionInner::LeftShift(box e, box by)
        }
        typed_absy::UExpressionInner::RightShift(box e, box by) => {
            let e = f.fold_uint_expression(e);
            let by = f.fold_field_expression(by);

            zir::UExpressionInner::RightShift(box e, box by)
        }
        typed_absy::UExpressionInner::Not(box e) => {
            let e = f.fold_uint_expression(e);

            zir::UExpressionInner::Not(box e)
        }
        typed_absy::UExpressionInner::FunctionCall(..) => {
            unreachable!("function calls should have been removed")
        }
        typed_absy::UExpressionInner::Select(box array, box index) => {
            let array = f.fold_array_expression(array);
            let index = f.fold_field_expression(index);

            use std::convert::TryInto;

            match index {
                zir::FieldElementExpression::Number(i) => {
                    let e: zir::UExpression<_> = array[i.to_dec_string().parse::<usize>().unwrap()]
                        .clone()
                        .try_into()
                        .unwrap();
                    e.into_inner()
                }
                _ => unreachable!(),
            }
        }
        typed_absy::UExpressionInner::Member(box s, id) => {
            let members = s.ty().clone();

            let s = f.fold_struct_expression(s);

            let offset: usize = members
                .iter()
                .take_while(|member| member.id != id)
                .map(|member| member.ty.get_primitive_count())
                .sum();

            use std::convert::TryInto;

            let res: zir::UExpression<'ast, T> = s[offset].clone().try_into().unwrap();

            res.into_inner()
        }
        typed_absy::UExpressionInner::IfElse(box cond, box cons, box alt) => {
            let cond = f.fold_boolean_expression(cond);
            let cons = f.fold_uint_expression(cons);
            let alt = f.fold_uint_expression(alt);
            zir::UExpressionInner::IfElse(box cond, box cons, box alt)
        }
    }
}

pub fn fold_function<'ast, T: Field>(
    f: &mut Flattener<T>,
    fun: typed_absy::TypedFunction<'ast, T>,
) -> zir::ZirFunction<'ast, T> {
    zir::ZirFunction {
        arguments: fun
            .arguments
            .into_iter()
            .flat_map(|a| f.fold_parameter(a))
            .collect(),
        statements: fun
            .statements
            .into_iter()
            .flat_map(|s| f.fold_statement(s))
            .collect(),
        signature: fun.signature.into(),
    }
}

pub fn fold_array_expression<'ast, T: Field>(
    f: &mut Flattener<T>,
    e: typed_absy::ArrayExpression<'ast, T>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    f.fold_array_expression_inner(&e.inner_type().clone(), e.size(), e.into_inner())
}

pub fn fold_struct_expression<'ast, T: Field>(
    f: &mut Flattener<T>,
    e: typed_absy::StructExpression<'ast, T>,
) -> Vec<zir::ZirExpression<'ast, T>> {
    f.fold_struct_expression_inner(&e.ty().clone(), e.into_inner())
}

pub fn fold_function_symbol<'ast, T: Field>(
    f: &mut Flattener<T>,
    s: typed_absy::TypedFunctionSymbol<'ast, T>,
) -> zir::ZirFunctionSymbol<'ast, T> {
    match s {
        typed_absy::TypedFunctionSymbol::Here(fun) => {
            zir::ZirFunctionSymbol::Here(f.fold_function(fun))
        }
        typed_absy::TypedFunctionSymbol::There(key, module) => {
            zir::ZirFunctionSymbol::There(f.fold_function_key(key), module)
        } // by default, do not fold modules recursively
        typed_absy::TypedFunctionSymbol::Flat(flat) => zir::ZirFunctionSymbol::Flat(flat),
    }
}

pub fn fold_program<'ast, T: Field>(
    f: &mut Flattener<T>,
    p: typed_absy::TypedProgram<'ast, T>,
) -> zir::ZirProgram<'ast, T> {
    zir::ZirProgram {
        modules: p
            .modules
            .into_iter()
            .map(|(module_id, module)| (module_id, f.fold_module(module)))
            .collect(),
        main: p.main,
    }
}
