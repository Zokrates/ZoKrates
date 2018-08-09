//! A substitution which attributes the same prefix to related strings:
//! foo_b12 -> _123_b12  =>  foo_b13 -> _123_b13
//! 
//! @file prefixed_substitution.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use substitution::Substitution;
use std::collections::HashMap;
use regex::Regex;

#[derive(Debug, Clone)]
pub struct PrefixedSubstitution {
    hashmap: HashMap<String, String>,
    regex: Regex
}

impl Substitution for PrefixedSubstitution {
    fn new() -> PrefixedSubstitution {
        PrefixedSubstitution {
            hashmap: {
                HashMap::<String, String>::new()
            },
            regex: Regex::new(r"_b\d+$").unwrap()
        }
    }

    fn insert(&mut self, key: String, element: String) -> Option<String>
    {
        let (p, _) = self.split_key(&key);
        match self.hashmap.get(p) {
            None => self.hashmap.insert(p.to_string(), element),
            Some(_) => None
        }
    }

    fn get(&self, key: &str) -> Option<String> {
        let (p, s) = self.split_key(key);

        let p_val = match self.hashmap.get(p) {
            Some(ref v) => Some(v.to_string()),
            None => None
        };

        match (s, p_val.clone()) {
            (Some(suffix), Some(v)) => Some(format!("{}{}", v, suffix)),
            (Some(_), None) => None,
            (None, _) => p_val
        }
    }

    fn contains_key(&mut self, key: &str) -> bool {
        let (p, _) = self.split_key(&key);
        self.hashmap.contains_key(p)
    }
}

impl PrefixedSubstitution {
    fn split_key<'a>(&self, key: &'a str) -> (&'a str, Option<&'a str>) {
        match self.regex.find_iter(key).last() {
            Some(candidate) => (&key[0..candidate.start()], Some(&key[candidate.start()..])),
            None => (key, None)
        }
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
}