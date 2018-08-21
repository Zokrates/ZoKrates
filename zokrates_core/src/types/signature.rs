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
    	try!(write!(f, "("));
    	for (i, t) in self.inputs.iter().enumerate() {
            try!(write!(f, "{}", t));
            if i < self.inputs.len() - 1 {
                try!(write!(f, ", "));
            }
        }
        try!(write!(f, ") -> ("));
        for (i, t) in self.outputs.iter().enumerate() {
            try!(write!(f, "{}", t));
            if i < self.outputs.len() - 1 {
                try!(write!(f, ", "));
            }
        }
        write!(f, ")")
    }
}