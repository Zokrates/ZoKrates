use crate::embed::FlatEmbed;
use crate::typed_absy::TypedProgram;
use crate::typed_absy::{
    result_folder::ResultFolder,
    result_folder::{fold_expression_list_inner, fold_uint_expression_inner},
    ArrayExpressionInner, BooleanExpression, TypedExpression, TypedExpressionListInner,
    TypedExpressionOrSpread, Types, UBitwidth, UExpressionInner,
};
use zokrates_field::Field;
pub struct ConstantArgumentChecker;

impl ConstantArgumentChecker {
    pub fn check<T: Field>(p: TypedProgram<T>) -> Result<TypedProgram<T>, Error> {
        ConstantArgumentChecker.fold_program(p)
    }
}

pub type Error = String;

impl<'ast, T: Field> ResultFolder<'ast, T> for ConstantArgumentChecker {
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

    fn fold_expression_list_inner(
        &mut self,
        tys: &Types<'ast, T>,
        l: TypedExpressionListInner<'ast, T>,
    ) -> Result<TypedExpressionListInner<'ast, T>, Error> {
        match l {
            TypedExpressionListInner::EmbedCall(FlatEmbed::BitArrayLe, generics, arguments) => {
                let arguments = arguments
                    .into_iter()
                    .map(|a| self.fold_expression(a))
                    .collect::<Result<Vec<_>, _>>()?;

                match arguments[1] {
                    TypedExpression::Array(ref a) => match a.as_inner() {
                        ArrayExpressionInner::Value(v) => {
                            if v.0.iter().all(|v| {
                                matches!(
                                    v,
                                    TypedExpressionOrSpread::Expression(TypedExpression::Boolean(
                                        BooleanExpression::Value(_)
                                    ))
                                )
                            }) {
                                Ok(TypedExpressionListInner::EmbedCall(
                                    FlatEmbed::BitArrayLe,
                                    generics,
                                    arguments,
                                ))
                            } else {
                                Err(format!("Cannot compare to a variable value, found `{}`", a))
                            }
                        }
                        v => Err(format!("Cannot compare to a variable value, found `{}`", v)),
                    },
                    _ => unreachable!(),
                }
            }
            l => fold_expression_list_inner(self, tys, l),
        }
    }
}
