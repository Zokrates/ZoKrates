//! Module containing ways to represent a substitution.
//!
//! @file substitution.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

const BINARY_SEPARATOR: &str = "_b";

use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct Substitution {
    hashmap: HashMap<String, String>
}

impl Substitution {
    pub fn new() -> Substitution {
        Substitution {
            hashmap: {
                HashMap::<String, String>::new()
            }
        }
    }

    pub fn insert(&mut self, key: String, element: String) -> Option<String>
    {
        let (p, _) = Self::split_key(&key);
        match self.hashmap.get(p) {
            None => self.hashmap.insert(p.to_string(), element),
            Some(_) => None
        }
    }

    pub fn get(&self, key: &str) -> Option<String> {
        let (p, s) = Self::split_key(key);
        match self.hashmap.get(p) {
            Some(ref v) => {
                match s {
                    Some(suffix) => {
                        Some(format!("{}{}{}", v, BINARY_SEPARATOR, suffix))
                    },
                    None => Some(v.to_string()),
                }
            },
            None => None
        }
    }

    pub fn contains_key(&mut self, key: &str) -> bool {
        let (p, _) = Self::split_key(&key);
        self.hashmap.contains_key(p)
    }

    fn split_key(key: &str) -> (&str, Option<&str>) {
        let mut parts = key.split(BINARY_SEPARATOR);
        (parts.nth(0).unwrap(), parts.nth(0))
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn insert_simple_variable() {
        let mut s = Substitution::new();
        s.insert("abc_de".to_string(), "_123".to_string());
        assert_eq!(s.get("abc_de").unwrap(), "_123".to_string());
    }

    #[test]
    fn insert_binary_variable() {
        let mut s = Substitution::new();
        s.insert("abc_de_b23".to_string(), "_123".to_string());
        assert_eq!(s.get("abc_de_b23").unwrap(), "_123_b23".to_string());
    }

    #[test]
    fn insert_twice_with_same_prefix() {
        let mut s = Substitution::new();
        s.insert("abc_de_b23".to_string(), "_123".to_string());
        s.insert("abc_de_b24".to_string(), "_456".to_string());
        assert_eq!(s.get("abc_de_b24").unwrap(), "_123_b24".to_string());
    }
}