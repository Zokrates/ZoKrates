//! A substitution which attributes the same prefix to related FlatVariables:
//! foo_b12 -> _123_b12  =>  foo_b13 -> _123_b13
//! 
//! @file prefixed_substitution.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use flat_absy::flat_variable::FlatVariable;
use substitution::Substitution;
use std::collections::{HashMap};

#[derive(Debug, Clone)]
pub struct PrefixedSubstitution {
    hashmap: HashMap<usize, usize>,
}

impl Substitution for PrefixedSubstitution {
    fn new() -> PrefixedSubstitution {
        PrefixedSubstitution {
            hashmap: {
                HashMap::new()
            },
        }
    }

    fn insert(&mut self, key: FlatVariable, element: FlatVariable) -> Option<FlatVariable>
    {
        self.hashmap.entry(key.id()).or_insert(element.id());
        None

        // match self.hashmap.get(&key.id) {
        //     Some(id) => Some(FlatVariable {
        //         id: *id,
        //         ..key
        //     }),
        //     None => {
        //         self.hashmap.insert(key.id, element.id);
        //         None
        //     }
        // }
    }

    fn get(&self, key: &FlatVariable) -> Option<FlatVariable> {
        match self.hashmap.get(&key.id()) {
            Some(id) => Some(key.with_id(*id)),
            None => None
        }
    }

    fn contains_key(&mut self, key: &FlatVariable) -> bool {
        self.hashmap.contains_key(&key.id())
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn insert_simple_variable() {
        let mut s = PrefixedSubstitution::new();
        let key = FlatVariable::new(1);
        let value = FlatVariable::new(123);
        s.insert(key, value);
        assert_eq!(s.get(&key).unwrap(), value);
    }

    #[test]
    fn insert_binary_variable() {
        let mut s = PrefixedSubstitution::new();
        let key = FlatVariable::new(1).with_binary(42);
        let value = FlatVariable::new(123);       
        s.insert(key, value);
        assert_eq!(s.get(&key).unwrap(), FlatVariable::new(123).with_binary(42));
    }

    #[test]
    fn insert_twice_with_same_prefix() {
        let mut s = PrefixedSubstitution::new();
        let key1 = FlatVariable::new(1).with_binary(23);
        let value1 = FlatVariable::new(123);
        let key2 = FlatVariable::new(1).with_binary(24);
        let value2 = FlatVariable::new(456);

        s.insert(key1, value1);
        s.insert(key2, value2);
        assert_eq!(s.get(&key2).unwrap(), FlatVariable::new(123).with_binary(24));
    }
}