use std::collections::HashMap;
use std::fmt;

// A variable in a constraint system
#[derive(Serialize, Deserialize, Clone, PartialEq, Hash, Eq, Ord, PartialOrd, Copy)]
pub struct FlatVariable(usize);

impl FlatVariable {
    pub fn new(id: usize) -> Self {
        FlatVariable(id)
    }

    pub fn id(&self) -> usize {
        self.0
    }
}

impl fmt::Display for FlatVariable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "_{}", self.0)
    }
}

impl fmt::Debug for FlatVariable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "FlatVariable(id: {})", self.0)
    }
}

impl FlatVariable {
    pub fn apply_substitution(
        self,
        substitution: &HashMap<FlatVariable, FlatVariable>,
        should_fallback: bool,
    ) -> Self {
        match should_fallback {
            true => substitution.get(&self).unwrap_or(&self).clone(),
            false => substitution.get(&self).unwrap().clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn private() {
        assert_eq!(format!("{}", FlatVariable::new(0)), "_0");
        assert_eq!(format!("{}", FlatVariable::new(42)), "_42");
    }
}
