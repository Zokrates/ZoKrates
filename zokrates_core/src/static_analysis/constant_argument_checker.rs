use std::fmt;
use zokrates_ast::common::FlatEmbed;
use zokrates_ast::typed::{
    result_folder::ResultFolder,
    result_folder::{fold_statement, fold_uint_expression_inner},
    Constant, EmbedCall, TypedStatement, UBitwidth, UExpressionInner,
};
use zokrates_ast::typed::{DefinitionRhs, TypedProgram, UExpression};
use zokrates_field::Field;

pub struct ConstantArgumentChecker;

impl ConstantArgumentChecker {
    pub fn check<T: Field>(p: TypedProgram<T>) -> Result<TypedProgram<T>, Error> {
        ConstantArgumentChecker.fold_program(p)
    }
}

#[derive(Debug)]
pub struct Error(String);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<'ast, T: Field> ResultFolder<'ast, T> for ConstantArgumentChecker {
    type Error = Error;

    fn fold_statement(
        &mut self,
        s: TypedStatement<'ast, T>,
    ) -> Result<Vec<TypedStatement<'ast, T>>, Self::Error> {
        match s {
            TypedStatement::Definition(assignee, DefinitionRhs::EmbedCall(embed_call)) => {
                match embed_call {
                    EmbedCall {
                        embed: FlatEmbed::BitArrayLe,
                        ..
                    } => {
                        let arguments = embed_call
                            .arguments
                            .into_iter()
                            .map(|a| self.fold_expression(a))
                            .collect::<Result<Vec<_>, _>>()?;

                        if arguments[1].is_constant() {
                            Ok(vec![TypedStatement::Definition(
                                assignee,
                                EmbedCall {
                                    embed: FlatEmbed::BitArrayLe,
                                    generics: embed_call.generics,
                                    arguments,
                                }
                                .into(),
                            )])
                        } else {
                            Err(Error(format!(
                                "Cannot compare to a variable value, found `{}`",
                                arguments[1]
                            )))
                        }
                    }
                    embed_call => Ok(vec![TypedStatement::Definition(
                        assignee,
                        embed_call.into(),
                    )]),
                }
            }
            s => fold_statement(self, s),
        }
    }

    fn fold_uint_expression_inner(
        &mut self,
        bitwidth: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> Result<UExpressionInner<'ast, T>, Error> {
        match e {
            UExpressionInner::LeftShift(e) => {
                let left = self.fold_uint_expression(*e.left)?;
                let right = self.fold_uint_expression(*e.right)?;

                match right.as_inner() {
                    UExpressionInner::Value(_) => {
                        Ok(UExpression::left_shift(left, right).into_inner())
                    }
                    by => Err(Error(format!(
                        "Cannot shift by a variable value, found `{} << {}`",
                        e,
                        by.clone().annotate(UBitwidth::B32)
                    ))),
                }
            }
            UExpressionInner::RightShift(e) => {
                let left = self.fold_uint_expression(*e.left)?;
                let right = self.fold_uint_expression(*e.right)?;

                match right.as_inner() {
                    UExpressionInner::Value(_) => {
                        Ok(UExpression::right_shift(left, right).into_inner())
                    }
                    by => Err(Error(format!(
                        "Cannot shift by a variable value, found `{} >> {}`",
                        e,
                        by.clone().annotate(UBitwidth::B32)
                    ))),
                }
            }
            e => fold_uint_expression_inner(self, bitwidth, e),
        }
    }
}
