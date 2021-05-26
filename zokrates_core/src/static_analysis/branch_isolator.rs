// Isolate branches means making sure that any branch is enclosed in a block.
// This is important, because we want any statement resulting from inlining any branch to be isolated from the coller, so that its panics can be conditional to the branch being logically run

// `if c then a else b fi` becomes `if c then { a } else { b } fi`, and down the line any statements resulting from trating `a` and `b` can be safely kept inside the respective blocks.

use crate::typed_absy::folder::*;
use crate::typed_absy::*;
use zokrates_field::Field;

pub struct Isolator;

impl Isolator {
    pub fn isolate<T: Field>(p: TypedProgram<T>) -> TypedProgram<T> {
        let mut isolator = Isolator;
        isolator.fold_program(p)
    }
}

impl<'ast, T: Field> Folder<'ast, T> for Isolator {
    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> FieldElementExpression<'ast, T> {
        match e {
            FieldElementExpression::IfElse(box condition, box consequence, box alternative) => {
                FieldElementExpression::IfElse(
                    box self.fold_boolean_expression(condition),
                    box FieldElementExpression::block(vec![], consequence.fold(self)),
                    box FieldElementExpression::block(vec![], alternative.fold(self)),
                )
            }
            e => fold_field_expression(self, e),
        }
    }

    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> BooleanExpression<'ast, T> {
        match e {
            BooleanExpression::IfElse(box condition, box consequence, box alternative) => {
                BooleanExpression::IfElse(
                    box self.fold_boolean_expression(condition),
                    box BooleanExpression::block(vec![], consequence.fold(self)),
                    box BooleanExpression::block(vec![], alternative.fold(self)),
                )
            }
            e => fold_boolean_expression(self, e),
        }
    }

    fn fold_uint_expression_inner(
        &mut self,
        bitwidth: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> UExpressionInner<'ast, T> {
        match e {
            UExpressionInner::IfElse(box condition, box consequence, box alternative) => {
                UExpressionInner::IfElse(
                    box self.fold_boolean_expression(condition),
                    box UExpression::block(vec![], consequence.fold(self)),
                    box UExpression::block(vec![], alternative.fold(self)),
                )
            }
            e => fold_uint_expression_inner(self, bitwidth, e),
        }
    }

    fn fold_array_expression_inner(
        &mut self,
        array_ty: ArrayType<'ast, T>,
        e: ArrayExpressionInner<'ast, T>,
    ) -> ArrayExpressionInner<'ast, T> {
        match e {
            ArrayExpressionInner::IfElse(box condition, box consequence, box alternative) => {
                ArrayExpressionInner::IfElse(
                    box self.fold_boolean_expression(condition),
                    box ArrayExpression::block(vec![], consequence.fold(self)),
                    box ArrayExpression::block(vec![], alternative.fold(self)),
                )
            }
            e => fold_array_expression_inner(self, array_ty, e),
        }
    }

    fn fold_struct_expression_inner(
        &mut self,
        struct_ty: StructType<'ast, T>,
        e: StructExpressionInner<'ast, T>,
    ) -> StructExpressionInner<'ast, T> {
        match e {
            StructExpressionInner::IfElse(box condition, box consequence, box alternative) => {
                StructExpressionInner::IfElse(
                    box self.fold_boolean_expression(condition),
                    box StructExpression::block(vec![], consequence.fold(self)),
                    box StructExpression::block(vec![], alternative.fold(self)),
                )
            }
            e => fold_struct_expression_inner(self, struct_ty, e),
        }
    }
}
