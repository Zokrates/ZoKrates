use std::fmt::Debug;
use flat_absy::flat_variable::FlatVariable;

pub mod direct_substitution;

pub trait Substitution : Debug {
	fn new() -> Self where Self: Sized;
	fn insert(&mut self, key: FlatVariable, element: FlatVariable) -> Option<FlatVariable>;
	fn get(&self, key: &FlatVariable) -> Option<FlatVariable>;
	fn contains_key(&mut self, key: &FlatVariable) -> bool;
}