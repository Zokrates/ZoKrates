use std::collections::HashMap;

pub struct KeyValueParser;

impl KeyValueParser {
    pub fn parse(input: String) -> HashMap<String, String> {
        let mut map = HashMap::new();
        let mut lines = input.lines();

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

        let map = KeyValueParser::parse(String::from(example));
        assert_eq!("1", map.get("a").unwrap());
        assert_eq!("2", map.get("b").unwrap());
    }

    #[test]
    fn parse_empty() {
        let map = KeyValueParser::parse(String::new());
        assert!(map.is_empty());
    }
}
