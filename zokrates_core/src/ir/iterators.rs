use super::{MemoryStatements, Statement};
use fallible_iterator::{FallibleIterator, IntoFallibleIterator};
use std::iter::FromIterator;

impl<T> IntoIterator for MemoryStatements<T> {
    type Item = Statement<T>;
    type IntoIter = std::vec::IntoIter<Statement<T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<T> FromIterator<Statement<T>> for MemoryStatements<T> {
    fn from_iter<I: IntoIterator<Item = Statement<T>>>(i: I) -> Self {
        MemoryStatements(i.into_iter().collect())
    }
}

pub struct MemoryStatementsIterator<T, I: Iterator<Item = Statement<T>>> {
    statements: I,
}

impl<T, I: Iterator<Item = Statement<T>>> FallibleIterator for MemoryStatementsIterator<T, I> {
    type Item = Statement<T>;
    type Error = DynamicError;

    fn next(&mut self) -> Result<Option<Self::Item>, Self::Error> {
        Ok(self.statements.next())
    }
}

impl<T> IntoFallibleIterator for MemoryStatements<T> {
    type Item = Statement<T>;
    type Error = DynamicError;
    type IntoFallibleIter = MemoryStatementsIterator<T, std::vec::IntoIter<Statement<T>>>;

    fn into_fallible_iter(self) -> Self::IntoFallibleIter {
        MemoryStatementsIterator {
            statements: self.into_iter(),
        }
    }
}

pub type DynamicError = Box<dyn std::error::Error>;

pub trait IntoStatements:
    IntoFallibleIterator<Item = Statement<Self::Field>, Error = DynamicError>
{
    type Field;
}

impl<T, U: IntoFallibleIterator<Item = Statement<T>, Error = DynamicError>> IntoStatements for U {
    type Field = T;
}

pub trait Statements:
    FallibleIterator<Item = Statement<Self::Field>, Error = DynamicError>
{
    type Field;
}

impl<T, U: FallibleIterator<Item = Statement<T>, Error = DynamicError>> Statements for U {
    type Field = T;
}
