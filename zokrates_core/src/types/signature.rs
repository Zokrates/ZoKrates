use types::Type;
use std::fmt;

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Signature {
	pub inputs: Vec<Type>,
	pub outputs: Vec<Type>
}

impl fmt::Debug for Signature {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Signature(inputs: {:?}, outputs: {:?})", self.inputs, self.outputs)
    }
}

impl fmt::Display for Signature {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({:?}) -> ({:?})", self.inputs, self.outputs)
    }
}

impl Signature {
	pub fn to_slug(&self) -> String {
		let inputs = self.inputs.iter().fold(String::from(""), |acc, ref t| format!("{}{}", acc, t.to_slug()));
		let outputs = self.outputs.iter().fold(String::from(""), |acc, ref t| format!("{}{}", acc, t.to_slug()));

		format!("i{}o{}", inputs, outputs)
	}
}