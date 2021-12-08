use super::FlatStatement;
use fallible_iterator::{FallibleIterator, IntoFallibleIterator};

pub type DynamicError = Box<dyn std::error::Error>;

pub trait IntoFlatStatements:
    IntoFallibleIterator<Item = FlatStatement<Self::Field>, Error = DynamicError>
{
    type Field;
}

impl<T, U: IntoFallibleIterator<Item = FlatStatement<T>, Error = DynamicError>> IntoFlatStatements
    for U
{
    type Field = T;
}

pub trait FlatStatements:
    FallibleIterator<Item = FlatStatement<Self::Field>, Error = DynamicError>
{
    type Field;
}

impl<T, U: FallibleIterator<Item = FlatStatement<T>, Error = DynamicError>> FlatStatements for U {
    type Field = T;
}
