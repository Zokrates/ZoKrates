pub trait Substitution {
	fn new() -> Self where Self: Sized;
	fn insert(&mut self, key: String, element: String) -> Option<String>;
	fn get(&self, key: &str) -> Option<String>;
	fn contains_key(&mut self, key: &str) -> bool;
}