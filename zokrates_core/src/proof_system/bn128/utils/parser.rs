use std::collections::HashMap;

pub trait KeyValueParser {
    fn parse_kv(&self) -> HashMap<String, String>;
}

impl KeyValueParser for String {
    fn parse_kv(&self) -> HashMap<String, String> {
        let mut map = HashMap::new();
        let mut lines = self.lines();

        while let Some(current_line) = lines.next() {
            let key_value: Vec<&str> = current_line.split("=").collect();
            if key_value.len() < 2 {
                continue;
            }
            map.insert(
                String::from(key_value[0].trim()),
                String::from(key_value[1].trim_start()),
            );
        }
        map
    }
}

#[cfg(test)]
mod tests {
    use super::KeyValueParser;

    #[test]
    fn parse_example() {
        let example: &str = r#"
            a = 1
            b = 2
        "#;

        let map = String::from(example).parse_kv();
        assert_eq!("1", map.get("a").unwrap());
        assert_eq!("2", map.get("b").unwrap());
    }

    #[test]
    fn parse_empty() {
        let map = String::from("").parse_kv();
        assert!(map.is_empty());
    }
}