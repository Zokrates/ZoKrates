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
use zokrates_field::field::Field;

pub struct InputConstrainer<'ast, T: Field> {
    constraints: Vec<TypedStatement<'ast, T>>,
}

impl<'ast, T: Field> InputConstrainer<'ast, T> {
    fn new() -> Self {
        InputConstrainer {
            constraints: vec![],
        }
    }

    pub fn constrain(p: TypedProgram<T>) -> TypedProgram<T> {
        InputConstrainer::new().fold_program(p)
    }

    fn constrain_expression(&mut self, e: TypedExpression<'ast, T>) {
        match e {
            TypedExpression::FieldElement(_) => {}
            TypedExpression::Boolean(b) => self.constraints.push(TypedStatement::Condition(
                b.clone().into(),
                BooleanExpression::And(box b.clone(), box b).into(),
            )),
            TypedExpression::Array(a) => {
                for i in 0..a.size() {
                    let e = match a.inner_type() {
                        Type::FieldElement => FieldElementExpression::select(
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
                        Type::Array(..) => {
                            ArrayExpression::member(s.clone(), member.id.clone()).into()
                        }
                        Type::Struct(..) => {
                            StructExpression::member(s.clone(), member.id.clone()).into()
                        }
                    };

                    self.constrain_expression(e);
                }
            }
        }
    }
}

impl<'ast, T: Field> Folder<'ast, T> for InputConstrainer<'ast, T> {
    fn fold_function(&mut self, f: TypedFunction<'ast, T>) -> TypedFunction<'ast, T> {
        TypedFunction {
            arguments: f
                .arguments
                .into_iter()
                .map(|a| self.fold_parameter(a))
                .collect(),
            statements: self.constraints.drain(..).chain(f.statements).collect(),
            ..f
        }
    }

    fn fold_parameter(&mut self, p: Parameter<'ast>) -> Parameter<'ast> {
        let v = p.id.clone();

        let e = match v.get_type() {
            Type::FieldElement => FieldElementExpression::Identifier(v.id).into(),
            Type::Boolean => BooleanExpression::Identifier(v.id).into(),
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
}
