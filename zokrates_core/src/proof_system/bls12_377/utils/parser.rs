use std::collections::HashMap;

pub fn parse_vk(vk: String) -> Result<HashMap<String, String>, csv::Error> {
    let mut reader = csv::ReaderBuilder::new()
        .delimiter(b'=')
        .has_headers(false)
        .trim(csv::Trim::All)
        .flexible(false)
        .from_reader(vk.trim().as_bytes());

    let mut map = HashMap::new();
    let mut iterator = reader.deserialize::<(String, String)>();

    while let Some(r) = iterator.next() {
        let r = r?;
        map.insert(r.0, r.1);
    }
    Ok(map)
}

#[cfg(test)]
mod tests {
    use proof_system::bn128::utils::parser::parse_vk;

    #[test]
    fn parse_valid_input() {
        let example: String = r#"
            a = 1
            b = 2
        "#
        .to_string();

        let map = parse_vk(example).unwrap();
        assert_eq!("1", map.get("a").unwrap());
        assert_eq!("2", map.get("b").unwrap());
    }

    #[test]
    #[should_panic]
    fn panic_on_invalid_delimiter() {
        parse_vk("a , 1".to_string()).unwrap();
    }

    #[test]
    #[should_panic]
    fn panic_on_unequal_lengths() {
        let example: String = r#"
            a = 1
            b = 2 = 3
        "#
        .to_string();
        parse_vk(example).unwrap();
    }

    #[test]
    fn parse_empty() {
        let map = parse_vk(String::new()).unwrap();
        assert!(map.is_empty());
    }
}
