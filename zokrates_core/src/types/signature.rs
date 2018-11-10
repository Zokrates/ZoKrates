use std::fmt;
use types::Type;

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

impl Signature {
    /// Returns a slug for a signature, with the following encoding:
    /// i{inputs}o{outputs} where {inputs} and {outputs} each encode a list of types.
    /// A list of types is encoded by compressing sequences of the same type like so:
    ///
    /// [field, field, field] -> 3f
    /// [field] -> f
    /// [field, bool, field] -> fbf
    /// [field, field, bool, field] -> 2fbf
    ///
    pub fn to_slug(&self) -> String {
        let to_slug = |types| {
            let mut res = vec![];
            for t in types {
                let len = res.len();
                if len == 0 {
                    res.push((1, t))
                } else {
                    if res[len - 1].1 == t {
                        res[len - 1].0 += 1;
                    } else {
                        res.push((1, t))
                    }
                }
            }
            res.into_iter()
                .map(|(n, t): (usize, &Type)| {
                    let mut r = String::new();

                    if n > 1 {
                        r.push_str(&format!("{}", n));
                    }
                    r.push_str(&t.to_slug());
                    r
                })
                .fold(String::new(), |mut acc, e| {
                    acc.push_str(&e);
                    acc
                })
        };

        format!("i{}o{}", to_slug(&self.inputs), to_slug(&self.outputs))
    }

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

    #[test]
    fn slug_0() {
        let s = Signature::new().inputs(vec![]).outputs(vec![]);

        assert_eq!(s.to_slug(), String::from("io"));
    }

    #[test]
    fn slug_1() {
        let s = Signature::new()
            .inputs(vec![Type::FieldElement, Type::Boolean])
            .outputs(vec![
                Type::FieldElement,
                Type::FieldElement,
                Type::Boolean,
                Type::FieldElement,
            ]);

        assert_eq!(s.to_slug(), String::from("ifbo2fbf"));
    }

    #[test]
    fn slug_2() {
        let s = Signature::new()
            .inputs(vec![
                Type::FieldElement,
                Type::FieldElement,
                Type::FieldElement,
            ])
            .outputs(vec![Type::FieldElement, Type::Boolean, Type::FieldElement]);

        assert_eq!(s.to_slug(), String::from("i3fofbf"));
    }

    #[test]
    fn array_slug() {
        let s = Signature::new()
            .inputs(vec![
                Type::FieldElementArray(42),
                Type::FieldElementArray(21),
            ])
            .outputs(vec![]);

        assert_eq!(s.to_slug(), String::from("if[42]f[21]o"));
    }
}
