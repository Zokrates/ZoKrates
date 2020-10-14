// The reducer reduces the program to a single function which is:
// - in SSA form
// - free of function calls (except for low level calls) thanks to inlining
// - free of for-loops thanks to unrolling

// The process happens in two steps
// 1. Shallow SSA for the `main` function
// We turn the `main` function into SSA form, but ignoring function calls and for loops

mod inline;
mod shallow_ssa;
mod unroll;

use std::collections::HashMap;
use typed_absy::CoreIdentifier;
use typed_absy::TypedFunction;
use typed_absy::TypedProgram;
use zokrates_field::Field;

use self::shallow_ssa::ShallowTransformer;

// An SSA version map, giving access to the latest version number for each identifier
pub type Versions<'ast> = HashMap<CoreIdentifier<'ast>, usize>;

// A container to represent whether more treatment must be applied to the function
#[derive(Debug, PartialEq)]
pub enum Output<'ast, T> {
    Complete(TypedFunction<'ast, T>),
    Incomplete(TypedFunction<'ast, T>, Vec<Versions<'ast>>, Versions<'ast>),
}

fn reduce<T: Field>(p: TypedProgram<T>) -> TypedProgram<T> {
    unimplemented!()
}
