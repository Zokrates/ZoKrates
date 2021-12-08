use super::{MemoryZirStatements, ZirStatement};
use fallible_iterator::{FallibleIterator, IntoFallibleIterator};
use std::iter::FromIterator;

pub type DynamicError = Box<dyn std::error::Error>;

pub trait IntoZirStatements<'ast>:
    IntoFallibleIterator<Item = ZirStatement<'ast, Self::Field>, Error = DynamicError>
{
    type Field;
}

impl<'ast, T, U: IntoFallibleIterator<Item = ZirStatement<'ast, T>, Error = DynamicError>>
    IntoZirStatements<'ast> for U
{
    type Field = T;
}

pub trait ZirStatements<'ast>:
    FallibleIterator<Item = ZirStatement<'ast, Self::Field>, Error = DynamicError>
{
    type Field;
}

impl<'ast, T, U: FallibleIterator<Item = ZirStatement<'ast, T>, Error = DynamicError>>
    ZirStatements<'ast> for U
{
    type Field = T;
}

impl<'ast, T> IntoIterator for MemoryZirStatements<'ast, T> {
    type Item = ZirStatement<'ast, T>;
    type IntoIter = std::vec::IntoIter<ZirStatement<'ast, T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'ast, T> FromIterator<ZirStatement<'ast, T>> for MemoryZirStatements<'ast, T> {
    fn from_iter<I: IntoIterator<Item = ZirStatement<'ast, T>>>(i: I) -> Self {
        MemoryZirStatements(i.into_iter().collect())
    }
}

pub struct MemoryZirStatementsIterator<'ast, T, I: Iterator<Item = ZirStatement<'ast, T>>> {
    statements: I,
}

impl<'ast, T, I: Iterator<Item = ZirStatement<'ast, T>>> FallibleIterator
    for MemoryZirStatementsIterator<'ast, T, I>
{
    type Item = ZirStatement<'ast, T>;
    type Error = DynamicError;

    fn next(&mut self) -> Result<Option<Self::Item>, Self::Error> {
        Ok(self.statements.next())
    }
}

impl<'ast, T> IntoFallibleIterator for MemoryZirStatements<'ast, T> {
    type Item = ZirStatement<'ast, T>;
    type Error = DynamicError;
    type IntoFallibleIter =
        MemoryZirStatementsIterator<'ast, T, std::vec::IntoIter<ZirStatement<'ast, T>>>;

    fn into_fallible_iter(self) -> Self::IntoFallibleIter {
        MemoryZirStatementsIterator {
            statements: self.into_iter(),
        }
    }
}
