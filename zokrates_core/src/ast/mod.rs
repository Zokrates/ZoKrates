mod memory;

use fallible_iterator::{FallibleIterator, IntoFallibleIterator};
pub use memory::MemoryStatements;

pub type DynamicError = Box<dyn std::error::Error>;

pub trait Ast {
    type Statement;
}

pub trait IntoStatements<A: Ast>:
    IntoFallibleIterator<Item = A::Statement, Error = DynamicError>
{
    type Statement;
}

pub trait Statements<A: Ast>: FallibleIterator<Item = A::Statement, Error = DynamicError> {
    type Statement;
}

impl<A: Ast, U: IntoFallibleIterator<Item = A::Statement, Error = DynamicError>> IntoStatements<A>
    for U
{
    type Statement = A::Statement;
}

impl<A: Ast, U: FallibleIterator<Item = A::Statement, Error = DynamicError>> Statements<A> for U {
    type Statement = A::Statement;
}
