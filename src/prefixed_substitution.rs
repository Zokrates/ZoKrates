//! Module containing ways to represent a substitution.
//!
//! @file prefixed_substitution.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

const BINARY_SEPARATOR: &str = "_b";

use substitution::Substitution;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct PrefixedSubstitution {
    hashmap: HashMap<String, String>
}

impl Substitution for PrefixedSubstitution {
    fn new() -> PrefixedSubstitution {
        PrefixedSubstitution {
            hashmap: {
                HashMap::<String, String>::new()
            }
        }
    }

    fn insert(&mut self, key: String, element: String) -> Option<String>
    {
        let (p, _) = Self::split_key(&key);
        match self.hashmap.get(p) {
            None => self.hashmap.insert(p.to_string(), element),
            Some(_) => None
        }
    }

    fn get(&self, key: &str) -> Option<String> {
        let (p, s) = Self::split_key(key);

        let p_val = match self.hashmap.get(p) {
            Some(ref v) => Some(v.to_string()),
            None => None
        };

        match (s, p_val.clone()) {
            (Some(suffix), Some(v)) => Some(format!("{}{}{}", v, BINARY_SEPARATOR, suffix)),
            (Some(_), None) => None,
            (None, _) => p_val
        }
    }

    fn contains_key(&mut self, key: &str) -> bool {
        let (p, _) = Self::split_key(&key);
        self.hashmap.contains_key(p)
    }
}

impl PrefixedSubstitution {
    fn split_key(key: &str) -> (&str, Option<&str>) {
        let mut parts = key.split(BINARY_SEPARATOR);
        assert!(parts.clone().count() <= 2);
        (parts.nth(0).unwrap(), parts.nth(0))
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn insert_simple_variable() {
        let mut s = PrefixedSubstitution::new();
        s.insert("abc_de".to_string(), "_123".to_string());
        assert_eq!(s.get("abc_de").unwrap(), "_123".to_string());
    }

    #[test]
    fn insert_binary_variable() {
        let mut s = PrefixedSubstitution::new();
        s.insert("abc_de_b23".to_string(), "_123".to_string());
        assert_eq!(s.get("abc_de_b23").unwrap(), "_123_b23".to_string());
    }

    #[test]
    fn insert_twice_with_same_prefix() {
        let mut s = PrefixedSubstitution::new();
        s.insert("abc_de_b23".to_string(), "_123".to_string());
        s.insert("abc_de_b24".to_string(), "_456".to_string());
        assert_eq!(s.get("abc_de_b24").unwrap(), "_123_b24".to_string());
    }

    #[test]
    #[should_panic]
    fn two_separators() {
        let mut s = PrefixedSubstitution::new();
        s.insert("abc_b21_b33".to_string(), "_123".to_string());
    }
}