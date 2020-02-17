//! Add runtime boolean checks on user inputs
//!
//! Example:
//! ```zokrates
//! struct Foo {
//!    bar: bool
//! }
//!
//! def main(Foo f) -> ():
//!    f.bar == f.bar && f.bar
//!    return
//! ```
//!
//! Becomes
//!
//! ```zokrates
//! struct Foo {
//!    bar: bool
//! }
//!
//! def main(Foo f) -> ():
//!    f.bar == f.bar && f.bar
//!    return
//! ```
//!
//! @file constrain_inputs.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2019

use crate::typed_absy::folder::Folder;
use crate::typed_absy::types::Type;
use crate::typed_absy::*;
use std::collections::HashSet;
use typed_absy::folder::fold_uint_expression;
use typed_absy::folder::fold_uint_expression_inner;
use zokrates_field::field::Field;

pub struct InputConstrainer<'ast, T: Field> {
    uints: HashSet<Identifier<'ast>>,
    next_var_id: usize,
    constraints: Vec<TypedStatement<'ast, T>>,
}

impl<'ast, T: Field> InputConstrainer<'ast, T> {
    fn new() -> Self {
        InputConstrainer {
            uints: HashSet::new(),
            next_var_id: 0,
            constraints: vec![],
        }
    }

    pub fn constrain(p: TypedProgram<T>) -> TypedProgram<T> {
        InputConstrainer::new().fold_program(p)
    }

    fn constrain_bits(&mut self, u: UExpression<'ast, T>) {
        // let bitwidth = u.bitwidth;
        // let u = UExpression {
        //     metadata: Some(UMetadata {
        //         bitwidth: Some(bitwidth),
        //         should_reduce: Some(false)
        //     }),
        //     ..u
        // };
        // let bit_input = Variable::with_id_and_type(
        //     CoreIdentifier::Internal("bit_input_array", self.next_var_id),
        //     Type::array(Type::FieldElement, bitwidth),
        // );
        // self.next_var_id += 1;
        // self.constraints.push(TypedStatement::MultipleDefinition(
        //     vec![bit_input],
        //     TypedExpressionList::FunctionCall(
        //         match bitwidth {
        //             8 => crate::embed::FlatEmbed::CheckU8.key::<T>(),
        //             16 => crate::embed::FlatEmbed::CheckU16.key::<T>(),
        //             32 => crate::embed::FlatEmbed::CheckU32.key::<T>(),
        //             _ => unreachable!(),
        //         },
        //         vec![u.into()],
        //         vec![Type::array(Type::FieldElement, bitwidth)],
        //     ),
        // ));
    }

    fn constrain_expression(&mut self, e: TypedExpression<'ast, T>) {
        match e {
            TypedExpression::FieldElement(_) => {}
            TypedExpression::Boolean(b) => self.constraints.push(TypedStatement::Condition(
                b.clone().into(),
                BooleanExpression::And(box b.clone(), box b).into(),
            )),
            TypedExpression::Uint(u) => {
                self.constrain_bits(u);
            }
            TypedExpression::Array(a) => {
                for i in 0..a.size() {
                    let e = match a.inner_type() {
                        Type::FieldElement => FieldElementExpression::select(
                            a.clone(),
                            FieldElementExpression::Number(T::from(i)),
                        )
                        .into(),
                        Type::Uint(..) => UExpression::select(
                            a.clone(),
                            FieldElementExpression::Number(T::from(i)),
                        )
                        .into(),
                        Type::Boolean => BooleanExpression::select(
                            a.clone(),
                            FieldElementExpression::Number(T::from(i)),
                        )
                        .into(),
                        Type::Array(..) => ArrayExpression::select(
                            a.clone(),
                            FieldElementExpression::Number(T::from(i)),
                        )
                        .into(),
                        Type::Struct(..) => StructExpression::select(
                            a.clone(),
                            FieldElementExpression::Number(T::from(i)),
                        )
                        .into(),
                    };

                    self.constrain_expression(e);
                }
            }
            TypedExpression::Struct(s) => {
                for member in s.ty() {
                    let e = match *member.ty {
                        Type::FieldElement => {
                            FieldElementExpression::member(s.clone(), member.id.clone()).into()
                        }
                        Type::Boolean => {
                            BooleanExpression::member(s.clone(), member.id.clone()).into()
                        }
                        Type::Boolean => BooleanExpression::member(s.clone(), member.id.clone()).into(),
                        Type::Uint(..) => UExpression::member(s.clone(), member.id.clone()).into(),
                        Type::Array(..) => ArrayExpression::member(s.clone(), member.id.clone()).into(),
                        Type::Struct(..) => StructExpression::member(s.clone(), member.id.clone()).into(),
                    };

                    self.constrain_expression(e);
                }
            }
        }
    }
}

impl<'ast, T: Field> Folder<'ast, T> for InputConstrainer<'ast, T> {
    fn fold_parameter(&mut self, p: Parameter<'ast>) -> Parameter<'ast> {
        let v = p.id.clone();

        let e = match v.get_type() {
            Type::FieldElement => FieldElementExpression::Identifier(v.id).into(),
            Type::Boolean => BooleanExpression::Identifier(v.id).into(),
            Type::Uint(bitwidth) => {
                self.uints.insert(v.id.clone());
                UExpressionInner::Identifier(v.id).annotate(bitwidth).into()
            }
            Type::Struct(members) => StructExpressionInner::Identifier(v.id)
                .annotate(members)
                .into(),
            Type::Array(array_type) => ArrayExpressionInner::Identifier(v.id)
                .annotate((*array_type.ty).clone(), array_type.size)
                .into(),
        };

        self.constrain_expression(e);

        p
    }

    fn fold_function(&mut self, f: TypedFunction<'ast, T>) -> TypedFunction<'ast, T> {
        let arguments: Vec<_> = f
            .arguments
            .into_iter()
            .map(|a| self.fold_parameter(a))
            .collect();
        let statements: Vec<_> = f
            .statements
            .into_iter()
            .flat_map(|s| self.fold_statement(s))
            .collect();

        TypedFunction {
            arguments,
            statements: self.constraints.drain(..).chain(statements).collect(),
            ..f
        }
    }

    fn fold_uint_expression(&mut self, e: UExpression<'ast, T>) -> UExpression<'ast, T> {
        match e.inner {
            UExpressionInner::Identifier(ref id) => {
                if self.uints.contains(id) {
                    UExpression {
                        metadata: Some(UMetadata {
                            bitwidth: Some(e.bitwidth),
                            should_reduce: Some(false),
                        }),
                        ..e
                    }
                } else {
                    e
                }
            }
            _ => fold_uint_expression(self, e),
        }
    }
}
