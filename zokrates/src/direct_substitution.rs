use std::collections::HashMap;
use substitution::Substitution;

#[derive(Debug, Clone)]
pub struct DirectSubstitution {
    hashmap: HashMap<String, String>
}

impl Substitution for DirectSubstitution {
	fn new() -> DirectSubstitution {
		DirectSubstitution {
			hashmap: HashMap::new()
		}
    }

    fn insert(&mut self, key: String, element: String) -> Option<String> {
    	self.hashmap.insert(key, element)
    }

    fn get(&self, key: &str) -> Option<String> {
    	match self.hashmap.get(key) {
    		Some(ref v) => Some(v.to_string()),
    		None => None
    	}
    }

    fn contains_key(&mut self, key: &str) -> bool {
    	self.hashmap.contains_key(key)
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn insert_simple_variable() {
        let mut s = DirectSubstitution::new();
        s.insert("abc_de".to_string(), "_123".to_string());
        assert_eq!(s.get("abc_de").unwrap(), "_123".to_string());
    }

    #[test]
    fn insert_binary_variable() {
        let mut s = DirectSubstitution::new();
        s.insert("abc_de_b23".to_string(), "_123".to_string());
        assert_eq!(s.get("abc_de_b23").unwrap(), "_123".to_string());
    }

    #[test]
    fn insert_twice_with_same_prefix() {
        let mut s = DirectSubstitution::new();
        s.insert("abc_de_b23".to_string(), "_123".to_string());
        s.insert("abc_de_b24".to_string(), "_456".to_string());
        assert_eq!(s.get("abc_de_b24").unwrap(), "_456".to_string());
    }

    #[test]
    fn two_separators() {
        let mut s = DirectSubstitution::new();
        s.insert("abc_b21_b33".to_string(), "_123".to_string());
    }
}