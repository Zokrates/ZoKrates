use std::collections::HashMap;

// Key-value store with constant-time access (two HashMap lookups) and constant-time deletion of many key-value pairs
// This way we can remove all variables of a given scope when we exit it
#[derive(Debug)]
pub struct StackedHashMap<K, V> {
    stack: Vec<HashMap<K, V>>,
    scope: HashMap<K, usize>,
}

impl<K: std::hash::Hash + Eq + Clone, V> StackedHashMap<K, V> {
    pub fn get(&self, key: &K) -> Option<&V> {
        self.scope
            .get(key)
            .map(|i| self.stack.get(*i).map(|m| m.get(key)).flatten())
            .flatten()
    }

    pub fn push_scope(&mut self) {
        self.stack.push(HashMap::default())
    }

    pub fn pop_scope(&mut self) -> Option<HashMap<K, V>> {
        self.stack.pop()
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let len = self.stack.len() - 1;
        self.scope.insert(key.clone(), len);
        self.stack[len].insert(key, value)
    }

    pub fn drain(&mut self) {
        self.stack = vec![HashMap::default()];
        self.scope = HashMap::default();
    }

    pub fn entry(&mut self, key: K) -> std::collections::hash_map::Entry<K, V> {
        let len = self.stack.len() - 1;
        self.stack[len].entry(key)
    }
}

impl<K, V> Default for StackedHashMap<K, V> {
    fn default() -> Self {
        Self {
            stack: vec![HashMap::default()],
            scope: HashMap::default(),
        }
    }
}
