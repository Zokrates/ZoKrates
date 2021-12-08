use super::{MemoryTypedStatements, TypedStatement};
use fallible_iterator::{FallibleIterator, IntoFallibleIterator};
use std::iter::FromIterator;

pub type DynamicError = Box<dyn std::error::Error>;

pub trait IntoTypedStatements<'ast>:
    IntoFallibleIterator<Item = TypedStatement<'ast, Self::Field>, Error = DynamicError>
{
    type Field;
}

impl<'ast, T, U: IntoFallibleIterator<Item = TypedStatement<'ast, T>, Error = DynamicError>>
    IntoTypedStatements<'ast> for U
{
    type Field = T;
}

pub trait TypedStatements<'ast>:
    FallibleIterator<Item = TypedStatement<'ast, Self::Field>, Error = DynamicError>
{
    type Field;
}

impl<'ast, T, U: FallibleIterator<Item = TypedStatement<'ast, T>, Error = DynamicError>>
    TypedStatements<'ast> for U
{
    type Field = T;
}

impl<'ast, T> IntoIterator for MemoryTypedStatements<'ast, T> {
    type Item = TypedStatement<'ast, T>;
    type IntoIter = std::vec::IntoIter<TypedStatement<'ast, T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'ast, T> FromIterator<TypedStatement<'ast, T>> for MemoryTypedStatements<'ast, T> {
    fn from_iter<I: IntoIterator<Item = TypedStatement<'ast, T>>>(i: I) -> Self {
        MemoryTypedStatements(i.into_iter().collect())
    }
}

pub struct MemoryTypedStatementsIterator<'ast, T, I: Iterator<Item = TypedStatement<'ast, T>>> {
    statements: I,
}

impl<'ast, T, I: Iterator<Item = TypedStatement<'ast, T>>> FallibleIterator
    for MemoryTypedStatementsIterator<'ast, T, I>
{
    type Item = TypedStatement<'ast, T>;
    type Error = DynamicError;

    fn next(&mut self) -> Result<Option<Self::Item>, Self::Error> {
        Ok(self.statements.next())
    }
}

impl<'ast, T> IntoFallibleIterator for MemoryTypedStatements<'ast, T> {
    type Item = TypedStatement<'ast, T>;
    type Error = DynamicError;
    type IntoFallibleIter =
        MemoryTypedStatementsIterator<'ast, T, std::vec::IntoIter<TypedStatement<'ast, T>>>;

    fn into_fallible_iter(self) -> Self::IntoFallibleIter {
        MemoryTypedStatementsIterator {
            statements: self.into_iter(),
        }
    }
}
