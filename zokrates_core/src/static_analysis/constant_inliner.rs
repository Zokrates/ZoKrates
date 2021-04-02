use crate::typed_absy::folder::{
    fold_array_expression, fold_array_expression_inner, fold_boolean_expression,
    fold_field_expression, fold_module, fold_struct_expression, fold_struct_expression_inner,
    fold_uint_expression, fold_uint_expression_inner, Folder,
};
use crate::typed_absy::{
    ArrayExpression, ArrayExpressionInner, ArrayType, BooleanExpression, FieldElementExpression,
    StructExpression, StructExpressionInner, StructType, TypedConstants, TypedModule, TypedProgram,
    UBitwidth, UExpression, UExpressionInner,
};
use std::collections::HashMap;
use std::convert::TryInto;
use zokrates_field::Field;

pub struct ConstantInliner<'ast, T: Field> {
    constants: TypedConstants<'ast, T>,
}

impl<'ast, T: Field> ConstantInliner<'ast, T> {
    pub fn inline(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        let mut inliner = ConstantInliner {
            constants: HashMap::new(),
        };
        inliner.fold_program(p)
    }
}

impl<'ast, T: Field> Folder<'ast, T> for ConstantInliner<'ast, T> {
    fn fold_module(&mut self, p: TypedModule<'ast, T>) -> TypedModule<'ast, T> {
        self.constants = p.constants.clone();
        fold_module(self, p)
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> FieldElementExpression<'ast, T> {
        match e {
            FieldElementExpression::Identifier(ref id) => match self.constants.get(id).cloned() {
                Some(c) => fold_field_expression(self, c.expression.try_into().unwrap()),
                None => fold_field_expression(self, e),
            },
            e => fold_field_expression(self, e),
        }
    }

    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> BooleanExpression<'ast, T> {
        match e {
            BooleanExpression::Identifier(ref id) => match self.constants.get(id).cloned() {
                Some(c) => fold_boolean_expression(self, c.expression.try_into().unwrap()),
                None => fold_boolean_expression(self, e),
            },
            e => fold_boolean_expression(self, e),
        }
    }

    fn fold_uint_expression_inner(
        &mut self,
        size: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> UExpressionInner<'ast, T> {
        match e {
            UExpressionInner::Identifier(ref id) => match self.constants.get(id).cloned() {
                Some(c) => {
                    let expr: UExpression<'ast, T> = c.expression.try_into().unwrap();
                    fold_uint_expression(self, expr).into_inner()
                }
                None => fold_uint_expression_inner(self, size, e),
            },
            // default
            e => fold_uint_expression_inner(self, size, e),
        }
    }

    fn fold_array_expression_inner(
        &mut self,
        ty: &ArrayType<'ast, T>,
        e: ArrayExpressionInner<'ast, T>,
    ) -> ArrayExpressionInner<'ast, T> {
        match e {
            ArrayExpressionInner::Identifier(ref id) => match self.constants.get(id).cloned() {
                Some(c) => {
                    let expr: ArrayExpression<'ast, T> = c.expression.try_into().unwrap();
                    fold_array_expression(self, expr).into_inner()
                }
                None => fold_array_expression_inner(self, ty, e),
            },
            // default
            e => fold_array_expression_inner(self, ty, e),
        }
    }

    fn fold_struct_expression_inner(
        &mut self,
        ty: &StructType<'ast, T>,
        e: StructExpressionInner<'ast, T>,
    ) -> StructExpressionInner<'ast, T> {
        match e {
            StructExpressionInner::Identifier(ref id) => match self.constants.get(id).cloned() {
                Some(c) => {
                    let expr: StructExpression<'ast, T> = c.expression.try_into().unwrap();
                    fold_struct_expression(self, expr).into_inner()
                }
                None => fold_struct_expression_inner(self, ty, e),
            },
            // default
            e => fold_struct_expression_inner(self, ty, e),
        }
    }
}
