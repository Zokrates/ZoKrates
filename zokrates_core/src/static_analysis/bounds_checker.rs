use crate::typed_absy::result_folder::*;
use crate::typed_absy::*;
use zokrates_field::Field;

pub struct BoundsChecker;

pub type Error = String;

impl BoundsChecker {
    pub fn check<T: Field>(p: TypedProgram<T>) -> Result<TypedProgram<T>, Error> {
        BoundsChecker.fold_program(p)
    }

    pub fn check_select<'ast, T: Field, U: Select<'ast, T>>(
        &mut self,
        array: ArrayExpression<'ast, T>,
        index: UExpression<'ast, T>,
    ) -> Result<U, Error> {
        let array = self.fold_array_expression(array)?;
        let index = self.fold_uint_expression(index)?;

        match (array.get_array_type().size.as_inner(), index.as_inner()) {
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

        Ok(U::select(array, index))
    }
}

impl<'ast, T: Field> ResultFolder<'ast, T> for BoundsChecker {
    type Error = Error;

    fn fold_array_expression_inner(
        &mut self,
        ty: &ArrayType<'ast, T>,
        e: ArrayExpressionInner<'ast, T>,
    ) -> Result<ArrayExpressionInner<'ast, T>, Self::Error> {
        match e {
            ArrayExpressionInner::Select(box array, box index) => self
                .check_select::<_, ArrayExpression<_>>(array, index)
                .map(|a| a.into_inner()),
            ArrayExpressionInner::Slice(box array, box from, box to) => {
                let array = self.fold_array_expression(array)?;
                let from = self.fold_uint_expression(from)?;
                let to = self.fold_uint_expression(to)?;

                match (
                    array.get_array_type().size.as_inner(),
                    from.as_inner(),
                    to.as_inner(),
                ) {
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

    fn fold_struct_expression_inner(
        &mut self,
        ty: &StructType<'ast, T>,
        e: StructExpressionInner<'ast, T>,
    ) -> Result<StructExpressionInner<'ast, T>, Self::Error> {
        match e {
            StructExpressionInner::Select(box array, box index) => self
                .check_select::<_, StructExpression<_>>(array, index)
                .map(|a| a.into_inner()),
            e => fold_struct_expression_inner(self, ty, e),
        }
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> Result<FieldElementExpression<'ast, T>, Self::Error> {
        match e {
            FieldElementExpression::Select(box array, box index) => self.check_select(array, index),
            e => fold_field_expression(self, e),
        }
    }

    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> Result<BooleanExpression<'ast, T>, Self::Error> {
        match e {
            BooleanExpression::Select(box array, box index) => self.check_select(array, index),
            e => fold_boolean_expression(self, e),
        }
    }

    fn fold_uint_expression_inner(
        &mut self,
        bitwidth: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> Result<UExpressionInner<'ast, T>, Self::Error> {
        match e {
            UExpressionInner::Select(box array, box index) => self
                .check_select::<_, UExpression<_>>(array, index)
                .map(|a| a.into_inner()),
            e => fold_uint_expression_inner(self, bitwidth, e),
        }
    }
}
