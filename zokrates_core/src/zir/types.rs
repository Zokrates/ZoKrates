use serde::{Deserialize, Serialize};
use std::fmt;

pub type MemberId = String;

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize, PartialOrd, Ord)]
pub enum Type {
    FieldElement,
    Boolean,
    Uint(UBitwidth),
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord, Hash, Copy)]
pub enum UBitwidth {
    #[serde(rename = "8")]
    B8 = 8,
    #[serde(rename = "16")]
    B16 = 16,
    #[serde(rename = "32")]
    B32 = 32,
    #[serde(rename = "64")]
    B64 = 64,
}

impl UBitwidth {
    pub fn to_usize(&self) -> usize {
        match self {
            UBitwidth::B8 => 8,
            UBitwidth::B16 => 16,
            UBitwidth::B32 => 32,
            UBitwidth::B64 => 64,
        }
    }
}

impl From<usize> for UBitwidth {
    fn from(b: usize) -> Self {
        match b {
            8 => UBitwidth::B8,
            16 => UBitwidth::B16,
            32 => UBitwidth::B32,
            64 => UBitwidth::B64,
            _ => unreachable!(),
        }
    }
}

impl fmt::Display for UBitwidth {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_usize())
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::FieldElement => write!(f, "field"),
            Type::Boolean => write!(f, "bool"),
            Type::Uint(ref bitwidth) => write!(f, "u{}", bitwidth),
        }
    }
}

impl fmt::Debug for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::FieldElement => write!(f, "field"),
            Type::Boolean => write!(f, "bool"),
            Type::Uint(ref bitwidth) => write!(f, "u{}", bitwidth),
        }
    }
}

impl Type {
    fn to_slug(&self) -> String {
        match self {
            Type::FieldElement => String::from("f"),
            Type::Boolean => String::from("b"),
            Type::Uint(bitwidth) => format!("u{}", bitwidth),
        }
    }

    pub fn uint<W: Into<UBitwidth>>(b: W) -> Self {
        Type::Uint(b.into())
    }

    // the number of field elements the type maps to
    pub fn get_primitive_count(&self) -> usize {
        match self {
            Type::FieldElement => 1,
            Type::Boolean => 1,
            Type::Uint(_) => 1,
        }
    }
}

pub use self::signature::Signature;

pub mod signature {
    use super::*;
    use std::fmt;

    #[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize, Ord, PartialOrd, Default)]
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
            write!(f, "(")?;
            for (i, t) in self.inputs.iter().enumerate() {
                write!(f, "{}", t)?;
                if i < self.inputs.len() - 1 {
                    write!(f, ", ")?;
                }
            }
            write!(f, ")")?;
            match self.outputs.len() {
                0 => write!(f, ""),
                1 => write!(f, " -> {}", self.outputs[0]),
                _ => {
                    write!(f, " -> (")?;
                    for (i, t) in self.outputs.iter().enumerate() {
                        write!(f, "{}", t)?;
                        if i < self.outputs.len() - 1 {
                            write!(f, ", ")?;
                        }
                    }
                    write!(f, ")")
                }
            }
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
                    } else if res[len - 1].1 == t {
                        res[len - 1].0 += 1;
                    } else {
                        res.push((1, t))
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
            Signature::default()
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

            assert_eq!(s.to_string(), String::from("(field, bool) -> bool"));
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
    }
}
