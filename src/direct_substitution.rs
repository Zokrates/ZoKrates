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