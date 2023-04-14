// given a (partial) map of values for program constants, replace where applicable constants by their value

use crate::reducer::ConstantDefinitions;
use zokrates_ast::typed::{
    folder::*, identifier::FrameIdentifier, CoreIdentifier, DeclarationConstant, Expr, Id,
    Identifier, IdentifierExpression, IdentifierOrExpression, TypedExpression, TypedProgram,
    TypedSymbolDeclaration, UExpression, UExpressionInner,
};
use zokrates_field::Field;

use std::convert::TryFrom;

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
                        UExpressionInner::Value(v) => DeclarationConstant::Concrete(v.value as u32),
                        _ => unreachable!(),
                    },
                    None => DeclarationConstant::Constant(c),
                }
            }
            c => fold_declaration_constant(self, c),
        }
    }

    fn fold_identifier_expression<
        E: Expr<'ast, T> + Id<'ast, T> + From<TypedExpression<'ast, T>>,
    >(
        &mut self,
        ty: &E::Ty,
        e: IdentifierExpression<'ast, E>,
    ) -> IdentifierOrExpression<'ast, T, E> {
        match e.id {
            Identifier {
                id:
                    FrameIdentifier {
                        id: CoreIdentifier::Constant(c),
                        frame: _,
                    },
                version,
            } => {
                assert_eq!(version, 0);
                match self.constants.get(&c).cloned() {
                    Some(v) => IdentifierOrExpression::Expression(E::from(v).into_inner()),
                    None => IdentifierOrExpression::Identifier(IdentifierExpression::new(
                        CoreIdentifier::Constant(c).into(),
                    )),
                }
            }
            _ => fold_identifier_expression(self, ty, e),
        }
    }
}
