use crate::types::Type;
use std::fmt;

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Signature {
    pub inputs: Vec<Type>,
    pub outputs: Vec<Type>,
}

impl fmt::Debug for Signature {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Signature(inputs: {:?}, outputs: {:?})",
            self.inputs, self.outputs
        )
    }
}

impl fmt::Display for Signature {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        r#try!(write!(f, "("));
        for (i, t) in self.inputs.iter().enumerate() {
            r#try!(write!(f, "{}", t));
            if i < self.inputs.len() - 1 {
                r#try!(write!(f, ", "));
            }
        }
        r#try!(write!(f, ") -> ("));
        for (i, t) in self.outputs.iter().enumerate() {
            r#try!(write!(f, "{}", t));
            if i < self.outputs.len() - 1 {
                r#try!(write!(f, ", "));
            }
        }
        write!(f, ")")
    }
}

impl Signature {
    pub fn new() -> Signature {
        Signature {
            inputs: vec![],
            outputs: vec![],
        }
    }

    pub fn inputs(mut self, inputs: Vec<Type>) -> Self {
        self.inputs = inputs;
        self
    }

    pub fn outputs(mut self, outputs: Vec<Type>) -> Self {
        self.outputs = outputs;
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn signature() {
        let s = Signature::new()
            .inputs(vec![Type::FieldElement, Type::Boolean])
            .outputs(vec![Type::Boolean]);

        assert_eq!(s.to_string(), String::from("(field, bool) -> (bool)"));
    }
}
