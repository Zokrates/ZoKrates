// given a (partial) map of values for program constants, replace where applicable constants by their value

use crate::static_analysis::reducer::ConstantDefinitions;
use zokrates_ast::typed::{
    folder::*, ArrayExpression, ArrayExpressionInner, ArrayType, BooleanExpression, CoreIdentifier,
    DeclarationConstant, Expr, FieldElementExpression, Identifier, StructExpression,
    StructExpressionInner, StructType, TupleExpression, TupleExpressionInner, TupleType,
    TypedProgram, TypedSymbolDeclaration, UBitwidth, UExpression, UExpressionInner,
};
use zokrates_field::Field;

use std::convert::{TryFrom, TryInto};

pub struct ConstantsReader<'a, 'ast, T> {
    constants: &'a ConstantDefinitions<'ast, T>,
}

impl<'a, 'ast, T: Field> ConstantsReader<'a, 'ast, T> {
    pub fn with_constants(constants: &'a ConstantDefinitions<'ast, T>) -> Self {
        Self { constants }
    }

    pub fn read_into_program(&mut self, p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        self.fold_program(p)
    }

    pub fn read_into_symbol_declaration(
        &mut self,
        d: TypedSymbolDeclaration<'ast, T>,
    ) -> TypedSymbolDeclaration<'ast, T> {
        self.fold_symbol_declaration(d)
    }
}

impl<'a, 'ast, T: Field> Folder<'ast, T> for ConstantsReader<'a, 'ast, T> {
    fn fold_declaration_constant(
        &mut self,
        c: DeclarationConstant<'ast, T>,
    ) -> DeclarationConstant<'ast, T> {
        match c {
            DeclarationConstant::Constant(c) => {
                let c = self.fold_canonical_constant_identifier(c);

                match self.constants.get(&c).cloned() {
                    Some(e) => match UExpression::try_from(e).unwrap().into_inner() {
                        UExpressionInner::Value(v) => DeclarationConstant::Concrete(v as u32),
                        _ => unreachable!(),
                    },
                    None => DeclarationConstant::Constant(c),
                }
            }
            c => fold_declaration_constant(self, c),
        }
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> FieldElementExpression<'ast, T> {
        match e {
            FieldElementExpression::Identifier(Identifier {
                id: CoreIdentifier::Constant(c),
                version,
            }) => {
                assert_eq!(version, 0);
                match self.constants.get(&c).cloned() {
                    Some(v) => v.try_into().unwrap(),
                    None => FieldElementExpression::Identifier(Identifier::from(
                        CoreIdentifier::Constant(c),
                    )),
                }
            }
            e => fold_field_expression(self, e),
        }
    }

    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> BooleanExpression<'ast, T> {
        match e {
            BooleanExpression::Identifier(Identifier {
                id: CoreIdentifier::Constant(c),
                version,
            }) => {
                assert_eq!(version, 0);
                match self.constants.get(&c).cloned() {
                    Some(v) => v.try_into().unwrap(),
                    None => {
                        BooleanExpression::Identifier(Identifier::from(CoreIdentifier::Constant(c)))
                    }
                }
            }
            e => fold_boolean_expression(self, e),
        }
    }

    fn fold_uint_expression_inner(
        &mut self,
        ty: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> UExpressionInner<'ast, T> {
        match e {
            UExpressionInner::Identifier(Identifier {
                id: CoreIdentifier::Constant(c),
                version,
            }) => {
                assert_eq!(version, 0);
                match self.constants.get(&c).cloned() {
                    Some(v) => UExpression::try_from(v).unwrap().into_inner(),
                    None => {
                        UExpressionInner::Identifier(Identifier::from(CoreIdentifier::Constant(c)))
                    }
                }
            }
            e => fold_uint_expression_inner(self, ty, e),
        }
    }

    fn fold_array_expression_inner(
        &mut self,
        ty: &ArrayType<'ast, T>,
        e: ArrayExpressionInner<'ast, T>,
    ) -> ArrayExpressionInner<'ast, T> {
        match e {
            ArrayExpressionInner::Identifier(Identifier {
                id: CoreIdentifier::Constant(c),
                version,
            }) => {
                assert_eq!(version, 0);
                match self.constants.get(&c).cloned() {
                    Some(v) => ArrayExpression::try_from(v).unwrap().into_inner(),
                    None => ArrayExpressionInner::Identifier(Identifier::from(
                        CoreIdentifier::Constant(c),
                    )),
                }
            }
            e => fold_array_expression_inner(self, ty, e),
        }
    }

    fn fold_tuple_expression_inner(
        &mut self,
        ty: &TupleType<'ast, T>,
        e: TupleExpressionInner<'ast, T>,
    ) -> TupleExpressionInner<'ast, T> {
        match e {
            TupleExpressionInner::Identifier(Identifier {
                id: CoreIdentifier::Constant(c),
                version,
            }) => {
                assert_eq!(version, 0);
                match self.constants.get(&c).cloned() {
                    Some(v) => TupleExpression::try_from(v).unwrap().into_inner(),
                    None => TupleExpressionInner::Identifier(Identifier::from(
                        CoreIdentifier::Constant(c),
                    )),
                }
            }
            e => fold_tuple_expression_inner(self, ty, e),
        }
    }

    fn fold_struct_expression_inner(
        &mut self,
        ty: &StructType<'ast, T>,
        e: StructExpressionInner<'ast, T>,
    ) -> StructExpressionInner<'ast, T> {
        match e {
            StructExpressionInner::Identifier(Identifier {
                id: CoreIdentifier::Constant(c),
                version,
            }) => {
                assert_eq!(version, 0);
                match self.constants.get(&c).cloned() {
                    Some(v) => StructExpression::try_from(v).unwrap().into_inner(),
                    None => StructExpressionInner::Identifier(Identifier::from(
                        CoreIdentifier::Constant(c),
                    )),
                }
            }
            e => fold_struct_expression_inner(self, ty, e),
        }
    }
}
