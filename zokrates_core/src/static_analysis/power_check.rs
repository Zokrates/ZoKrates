use crate::typed_absy::folder::*;
use crate::typed_absy::Folder;
use crate::typed_absy::*;
use zokrates_field::field::Field;

pub struct PowerChecker {}

impl PowerChecker {
    fn new() -> Self {
        PowerChecker {}
    }

    pub fn check<T: Field>(p: TypedProg<T>) -> TypedProg<T> {
        PowerChecker::new().fold_program(p)
    }
}

impl<'ast, T: Field> Folder<'ast, T> for PowerChecker {
    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> FieldElementExpression<'ast, T> {
        match e {
            FieldElementExpression::Pow(box FieldElementExpression::Identifier(..), _) |  FieldElementExpression::Pow(box FieldElementExpression::Number(..), _)=> {
				fold_field_expression(self, e)
            },
            FieldElementExpression::Pow(e, _) => {
            	panic!(format!("Base of an exponentiation has to be a number or identifier, found {}. Please use intermediate variables.", e))
            },
            e => fold_field_expression(self, e)
        }
    }
}
