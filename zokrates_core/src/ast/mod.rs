mod memory;

use fallible_iterator::{FallibleIterator, IntoFallibleIterator};
pub use memory::MemoryStatements;

pub type DynamicError = Box<dyn std::error::Error>;

/// A marker trait for statements, so that we can recover the underlying `Field`
pub trait StatementTrait {
    type Field;
}

pub trait IntoStatements:
    IntoFallibleIterator<Item = Self::Statement, Error = DynamicError>
{
    type Statement: StatementTrait;
    type Field;
}

pub trait Statements: FallibleIterator<Item = Self::Statement, Error = DynamicError> {
    type Statement: StatementTrait;
    type Field;
}

impl<S: StatementTrait, U: IntoFallibleIterator<Item = S, Error = DynamicError>> IntoStatements
    for U
{
    type Statement = S;
    type Field = S::Field;
}

impl<S: StatementTrait, U: FallibleIterator<Item = S, Error = DynamicError>> Statements for U {
    type Statement = S;
    type Field = S::Field;
}
