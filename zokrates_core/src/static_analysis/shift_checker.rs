use crate::typed_absy::TypedProgram;
use crate::typed_absy::{
    result_folder::fold_uint_expression_inner, result_folder::ResultFolder, UBitwidth,
    UExpressionInner,
};
use zokrates_field::Field;
pub struct ShiftChecker;

impl ShiftChecker {
    pub fn check<T: Field>(p: TypedProgram<T>) -> Result<TypedProgram<T>, Error> {
        ShiftChecker.fold_program(p)
    }
}

pub type Error = String;

impl<'ast, T: Field> ResultFolder<'ast, T> for ShiftChecker {
    type Error = Error;

    fn fold_uint_expression_inner(
        &mut self,
        bitwidth: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> Result<UExpressionInner<'ast, T>, Error> {
        match e {
            UExpressionInner::LeftShift(box e, box by) => {
                let e = self.fold_uint_expression(e)?;
                let by = self.fold_uint_expression(by)?;

                match by.as_inner() {
                    UExpressionInner::Value(_) => Ok(UExpressionInner::LeftShift(box e, box by)),
                    by => Err(format!(
                        "Cannot shift by a variable value, found `{} << {}`",
                        e,
                        by.clone().annotate(UBitwidth::B32)
                    )),
                }
            }
            UExpressionInner::RightShift(box e, box by) => {
                let e = self.fold_uint_expression(e)?;
                let by = self.fold_uint_expression(by)?;

                match by.as_inner() {
                    UExpressionInner::Value(_) => Ok(UExpressionInner::RightShift(box e, box by)),
                    by => Err(format!(
                        "Cannot shift by a variable value, found `{} >> {}`",
                        e,
                        by.clone().annotate(UBitwidth::B32)
                    )),
                }
            }
            e => fold_uint_expression_inner(self, bitwidth, e),
        }
    }
}
