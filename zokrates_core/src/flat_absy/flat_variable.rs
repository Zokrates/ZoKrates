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
    fn with_id(id: isize) -> Self {
        FlatVariable { id }
    }

    pub fn new(id: usize) -> Self {
        FlatVariable::with_id(1 + id as isize)
    }

    pub fn one() -> Self {
        FlatVariable::with_id(0)
    }

    pub fn public(id: usize) -> Self {
        FlatVariable::with_id(-(id as isize) - 1)
    }

    pub fn apply_substitution(
        self,
        substitution: &HashMap<FlatVariable, FlatVariable>,
        should_fallback: bool,
    ) -> Self {
        match substitution.get(&self) {
            Some(value) => *value,
            None => {
                if should_fallback {
                    self
                } else {
                    unreachable!()
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;
    use std::iter;

    #[test]
    fn one() {
        assert_eq!(FlatVariable::one().to_string(), "~one");
    }

    #[test]
    fn public() {
        let v = FlatVariable::public(0);
        assert_eq!(v.to_string(), "~out_0");
        assert_eq!(format!("{:?}", v), "FlatVariable(id: -1)");

        let v = FlatVariable::public(42);
        assert_eq!(v.to_string(), "~out_42");
        assert_eq!(format!("{:?}", v), "FlatVariable(id: -43)");
    }

    #[test]
    fn private() {
        let v = FlatVariable::new(0);
        assert_eq!(v.to_string(), "_0");
        assert_eq!(format!("{:?}", v), "FlatVariable(id: 1)");

        let v = FlatVariable::new(42);
        assert_eq!(v.to_string(), "_42");
        assert_eq!(format!("{:?}", v), "FlatVariable(id: 43)");
    }

    #[test]
    fn no_overlap() {
        // make sure public, private and one variables do not overlap
        let set: HashSet<_> = (0..10)
            .map(|i| FlatVariable::public(i))
            .chain((0..10).map(|i| FlatVariable::new(i)))
            .chain(iter::once(FlatVariable::one()))
            .collect();
        assert_eq!(set.iter().count(), 10 + 10 + 1);
    }

    #[test]
    fn substitute_no_fallback() {
        let v = FlatVariable::new(42);
        let hashmap: HashMap<_, _> = vec![(FlatVariable::new(42), FlatVariable::new(21))]
            .into_iter()
            .collect();
        assert_eq!(v.apply_substitution(&hashmap, false), FlatVariable::new(21));
    }

    #[test]
    fn substitute_with_fallback() {
        let v = FlatVariable::new(42);
        let hashmap = HashMap::new();
        assert_eq!(v.apply_substitution(&hashmap, true), FlatVariable::new(42));
    }

    #[test]
    #[should_panic]
    fn substitute_no_fallback_panic() {
        let v = FlatVariable::new(42);
        let hashmap = HashMap::new();
        v.apply_substitution(&hashmap, false);
    }
}
