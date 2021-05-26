use crate::typed_absy::result_folder::*;
use crate::typed_absy::*;
use zokrates_field::Field;

pub struct BoundsChecker;

pub type Error = String;

impl BoundsChecker {
    pub fn check<T: Field>(p: TypedProgram<T>) -> Result<TypedProgram<T>, Error> {
        BoundsChecker.fold_program(p)
    }
}

impl<'ast, T: Field> ResultFolder<'ast, T> for BoundsChecker {
    type Error = Error;

    fn fold_array_expression_inner(
        &mut self,
        ty: ArrayType<'ast, T>,
        e: ArrayExpressionInner<'ast, T>,
    ) -> Result<ArrayExpressionInner<'ast, T>, Self::Error> {
        match e {
            ArrayExpressionInner::Slice(box array, box from, box to) => {
                let array = self.fold_array_expression(array)?;
                let from = self.fold_uint_expression(from)?;
                let to = self.fold_uint_expression(to)?;

                match (array.ty().size.as_inner(), from.as_inner(), to.as_inner()) {
                    (
                        UExpressionInner::Value(size),
                        UExpressionInner::Value(from),
                        UExpressionInner::Value(to),
                    ) => {
                        if from > to {
                            return Err(format!(
                                "Slice is created from an invalid range {}..{}",
                                from, to
                            ));
                        }

                        if from > size {
                            return Err(format!("Lower bound {} of slice {}[{}..{}] is out of bounds for array of size {}", from, array, from, to, size));
                        }

                        if to > size {
                            return Err(format!("Upper bound {} of slice {}[{}..{}] is out of bounds for array of size {}", to, array, from, to, size));
                        }
                    }
                    _ => unreachable!(),
                };

                Ok(ArrayExpressionInner::Slice(box array, box from, box to))
            }
            e => fold_array_expression_inner(self, ty, e),
        }
    }

    fn fold_select_expression<
        E: Expr<'ast, T> + Select<'ast, T> + From<TypedExpression<'ast, T>>,
    >(
        &mut self,
        select: SelectExpression<'ast, T, E>,
    ) -> Result<ThisOrUncle<SelectExpression<'ast, T, E>, E::Inner>, Self::Error> {
        let array = self.fold_array_expression(*select.array)?;
        let index = self.fold_uint_expression(*select.index)?;

        match (array.ty().size.as_inner(), index.as_inner()) {
            (UExpressionInner::Value(size), UExpressionInner::Value(index)) => {
                if index >= size {
                    return Err(format!(
                        "Out of bounds access: {}[{}] but {} is of size {}",
                        array, index, array, size
                    ));
                }
            }
            _ => unreachable!(),
        };

        Ok(ThisOrUncle::This(SelectExpression::new(array, index)))
    }
}
