use std::collections::HashMap;

pub fn parse_vk(vk: String) -> HashMap<String, String> {
    let mut reader = csv::ReaderBuilder::new()
        .delimiter(b'=')
        .has_headers(false)
        .trim(csv::Trim::All)
        .from_reader(vk.as_bytes());

    let mut map = HashMap::new();
    let mut iterator = reader.deserialize::<(String, String)>();

    while let Some(r) = iterator.next() {
        if r.is_ok() {
            let r = r.unwrap();
            map.insert(r.0, r.1);
        }
    }
    map
}

#[cfg(test)]
mod tests {
    use proof_system::bn128::utils::parser::parse_vk;

    #[test]
    fn parse_example() {
        let example: &str = r#"
            a = 1
            b = 2
        "#;

        let map = parse_vk(example.to_string());
        assert_eq!("1", map.get("a").unwrap());
        assert_eq!("2", map.get("b").unwrap());
    }

    #[test]
    fn parse_empty() {
        let map = parse_vk(String::new());
        assert!(map.is_empty());
    }
}
