use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;

// A variable in a constraint system
// id > 0 for intermediate variables
// id == 0 for ~one
// id < 0 for public outputs
#[derive(Serialize, Deserialize, Clone, PartialEq, Hash, Eq, Ord, PartialOrd, Copy)]
pub struct FlatVariable {
    id: isize,
}

impl FlatVariable {
    pub fn new(id: usize) -> Self {
        FlatVariable {
            id: 1 + id as isize,
        }
    }

    pub fn one() -> Self {
        FlatVariable { id: 0 }
    }

    pub fn public(id: usize) -> Self {
        FlatVariable {
            id: -(id as isize) - 1,
        }
    }

    pub fn id(&self) -> usize {
        assert!(self.id > 0);
        (self.id as usize) - 1
    }

    pub fn try_from_human_readable(s: &str) -> Result<Self, &str> {
        if s == "~one" {
            return Ok(FlatVariable::one());
        }

        let mut public = s.split("~out_");
        match public.nth(1) {
            Some(v) => {
                let v = v.parse().map_err(|_| s)?;
                Ok(FlatVariable::public(v))
            }
            None => {
                let mut private = s.split('_');
                match private.nth(1) {
                    Some(v) => {
                        let v = v.parse().map_err(|_| s)?;
                        Ok(FlatVariable::new(v))
                    }
                    None => Err(s),
                }
            }
        }
    }
}

impl fmt::Display for FlatVariable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.id {
            0 => write!(f, "~one"),
            i if i > 0 => write!(f, "_{}", i - 1),
            i => write!(f, "~out_{}", -(i + 1)),
        }
    }
}

impl fmt::Debug for FlatVariable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "FlatVariable(id: {})", self.id)
    }
}

impl FlatVariable {
    pub fn apply_substitution(self, substitution: &HashMap<FlatVariable, FlatVariable>) -> &Self {
        substitution.get(&self).unwrap()
    }

    pub fn is_output(&self) -> bool {
        self.id < 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn one() {
        assert_eq!(format!("{}", FlatVariable::one()), "~one");
    }

    #[test]
    fn public() {
        assert_eq!(format!("{}", FlatVariable::public(0)), "~out_0");
        assert_eq!(format!("{}", FlatVariable::public(42)), "~out_42");
    }

    #[test]
    fn private() {
        assert_eq!(format!("{}", FlatVariable::new(0)), "_0");
        assert_eq!(format!("{}", FlatVariable::new(42)), "_42");
    }
}
