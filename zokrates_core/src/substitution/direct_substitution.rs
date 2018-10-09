use flat_absy::flat_variable::FlatVariable;
use std::collections::HashMap;
use substitution::Substitution;

#[derive(Debug, Clone)]
pub struct DirectSubstitution {
    hashmap: HashMap<FlatVariable, FlatVariable>
}

impl Substitution for DirectSubstitution {
	fn new() -> DirectSubstitution {
		DirectSubstitution {
			hashmap: HashMap::new()
		}
    }

    fn insert(&mut self, key: FlatVariable, element: FlatVariable) -> Option<FlatVariable> {
    	self.hashmap.insert(key, element)
    }

    fn get(&self, key: &FlatVariable) -> Option<FlatVariable> {
    	match self.hashmap.get(key) {
            Some(value) => Some(value.clone()),
            None => None
        }
    }

    fn contains_key(&mut self, key: &FlatVariable) -> bool {
    	self.hashmap.contains_key(key)
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn insert_simple_variable() {
        let mut s = DirectSubstitution::new();
        let key = FlatVariable::new(1);
        let value = FlatVariable::new(123);
        s.insert(key, value);
        assert_eq!(s.get(&key).unwrap(), value);
    }
}