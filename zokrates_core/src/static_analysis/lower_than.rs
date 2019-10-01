//! Module containing constant propagation for the typed AST
//!
//! @file propagation.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use crate::typed_absy::folder::*;
use crate::typed_absy::*;
use std::collections::HashMap;
use std::convert::TryFrom;
use types::Type;
use zokrates_field::field::Field;

pub struct LowerThan<'ast, T: Field> {
    statements: Vec<TypedStatement<'ast, T>>,
}

impl<'ast, T: Field> LowerThan<'ast, T> {
    fn new() -> Self {
        LowerThan { statements: vec![] }
    }

    pub fn reduce(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        LowerThan::new().fold_program(p)
    }
}

impl<'ast, T: Field> Folder<'ast, T> for LowerThan<'ast, T> {
    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> BooleanExpression<'ast, T> {
        match e {
            BooleanExpression::Lt(box left, box right) => {
                let statements: Vec<TypedStatement<T>> = vec![
                    // write all statements here
                ];
                unimplemented!() // return a BooleanExpression here, which is equivalent to the original expression after execution of the statements above
            }
            e => fold_boolean_expression(self, e),
        }
    }

    fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        let s = fold_statement(self, s);
        self.statements.drain(..).chain(s.into_iter()).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;
}
