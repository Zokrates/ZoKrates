use std::collections::BTreeMap;
use std::convert::TryFrom;
use std::fmt;
use typed_absy::types::Type;

use zokrates_field::field::Field;

type Map<K, V> = BTreeMap<K, V>;

#[derive(Debug, PartialEq)]
enum Error {
    Json(String),
    Conversion(String),
    Type(String),
}

#[derive(PartialEq, Debug)]
enum Value<T> {
    Field(T),
    Boolean(bool),
    Array(Vec<Value<T>>),
    Struct(Map<String, Value<T>>),
}

impl<T: Field> fmt::Display for Value<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Field(v) => write!(f, "{}", v),
            Value::Boolean(v) => write!(f, "{}", v),
            Value::Array(v) => write!(
                f,
                "[{}]",
                v.iter()
                    .map(|v| format!("{}", v))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Value::Struct(v) => write!(
                f,
                "{{{}}}",
                v.iter()
                    .map(|(k, v)| format!("{}: {}", k, v))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

impl<T: Field> Value<T> {
    fn check(&self, ty: &Type) -> Result<(), String> {
        match (&self, ty) {
            (Value::Field(_), Type::FieldElement) => Ok(()),
            (Value::Boolean(_), Type::Boolean) => Ok(()),
            (Value::Array(v), Type::Array(inner_ty, size)) => {
                if v.len() != *size {
                    Err(format!(
                        "Expected array of size {}, found array of size {}",
                        size,
                        v.len()
                    ))
                } else {
                    v.iter()
                        .map(|val| val.check(inner_ty))
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok(())
                }
            }
            (Value::Struct(v), Type::Struct(members)) => {
                if v.len() != members.len() {
                    Err(format!(
                        "Expected {} member(s), found {}",
                        members.len(),
                        v.len()
                    ))
                } else {
                    members
                        .iter()
                        .map(|(id, ty)| {
                            v.get(id)
                                .ok_or_else(|| format!("Member with id `{}` not found", id))
                                .map(|v| v.check(&ty))
                        })
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .collect::<Result<_, _>>()?;
                    Ok(())
                }
            }
            (v, t) => Err(format!("Value `{}` doesn't match expected type `{}", v, t)),
        }
    }
}

#[derive(PartialEq, Debug)]
struct Values<T>(Vec<Value<T>>);

impl<T: Field> TryFrom<serde_json::Value> for Values<T> {
    type Error = String;

    fn try_from(v: serde_json::Value) -> Result<Values<T>, Self::Error> {
        match v {
            serde_json::Value::Array(a) => a
                .into_iter()
                .map(|v| Value::try_from(v))
                .collect::<Result<_, _>>()
                .map(|v| Values(v)),
            v => Err(format!("Expected an array of values, found `{}`", v)),
        }
    }
}

impl<T: Field> TryFrom<serde_json::Value> for Value<T> {
    type Error = String;
    fn try_from(v: serde_json::Value) -> Result<Value<T>, Self::Error> {
        match v {
            serde_json::Value::String(s) => T::try_from_dec_str(&s)
                .map(|v| Value::Field(v))
                .map_err(|_| format!("Could not parse `{}` as field element", s)),
            serde_json::Value::Bool(b) => Ok(Value::Boolean(b)),
            serde_json::Value::Number(n) => Err(format!(
                "Value `{}` isn't allowed, did you mean `\"{}\"`?",
                n, n
            )),
            serde_json::Value::Array(a) => a
                .into_iter()
                .map(|v| Value::try_from(v))
                .collect::<Result<_, _>>()
                .map(|v| Value::Array(v)),
            serde_json::Value::Object(o) => o
                .into_iter()
                .map(|(k, v)| Value::try_from(v).map(|v| (k, v)))
                .collect::<Result<Map<_, _>, _>>()
                .map(|v| Value::Struct(v)),
            v => Err(format!("Value `{}` isn't allowed", v)),
        }
    }
}

fn parse<T: Field>(s: &str) -> Result<Values<T>, Error> {
    let json_values: serde_json::Value =
        serde_json::from_str(s).map_err(|e| Error::Json(e.to_string()))?;
    Values::try_from(json_values).map_err(|e| Error::Conversion(e))
}

fn parse_strict<T: Field>(s: &str, types: &Vec<Type>) -> Result<Values<T>, Error> {
    let parsed = parse(s)?;
    parsed
        .0
        .iter()
        .zip(types.iter())
        .map(|(v, ty)| v.check(ty))
        .collect::<Result<_, _>>()
        .map_err(|e| Error::Type(e))?;
    Ok(parsed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    #[test]
    fn numbers() {
        let s = "[1, 2]";
        assert_eq!(
            parse::<FieldPrime>(s).unwrap_err(),
            Error::Conversion(String::from(
                "Value `1` isn't allowed, did you mean `\"1\"`?"
            ))
        );
    }

    #[test]
    fn fields() {
        let s = r#"["1", "2"]"#;
        assert_eq!(
            parse::<FieldPrime>(s).unwrap(),
            Values(vec![Value::Field(1.into()), Value::Field(2.into())])
        );
    }

    #[test]
    fn bools() {
        let s = "[true, false]";
        assert_eq!(
            parse::<FieldPrime>(s).unwrap(),
            Values(vec![Value::Boolean(true), Value::Boolean(false)])
        );
    }

    #[test]
    fn array() {
        let s = "[[true, false]]";
        assert_eq!(
            parse::<FieldPrime>(s).unwrap(),
            Values(vec![Value::Array(vec![
                Value::Boolean(true),
                Value::Boolean(false)
            ])])
        );
    }

    #[test]
    fn struc() {
        let s = r#"[{"a": "42"}]"#;
        assert_eq!(
            parse::<FieldPrime>(s).unwrap(),
            Values(vec![Value::Struct(
                vec![("a".to_string(), Value::Field(42.into()))]
                    .into_iter()
                    .collect()
            )])
        );
    }

    mod strict {
        use super::*;

        #[test]
        fn fields() {
            let s = r#"["1", "2"]"#;
            assert_eq!(
                parse_strict::<FieldPrime>(s, &vec![Type::FieldElement, Type::FieldElement])
                    .unwrap(),
                Values(vec![Value::Field(1.into()), Value::Field(2.into())])
            );
        }

        #[test]
        fn bools() {
            let s = "[true, false]";
            assert_eq!(
                parse_strict::<FieldPrime>(s, &vec![Type::Boolean, Type::Boolean]).unwrap(),
                Values(vec![Value::Boolean(true), Value::Boolean(false)])
            );
        }

        #[test]
        fn array() {
            let s = "[[true, false]]";
            assert_eq!(
                parse_strict::<FieldPrime>(s, &vec![Type::array(Type::Boolean, 2)]).unwrap(),
                Values(vec![Value::Array(vec![
                    Value::Boolean(true),
                    Value::Boolean(false)
                ])])
            );
        }

        #[test]
        fn struc() {
            let s = r#"[{"a": "42"}]"#;
            assert_eq!(
                parse_strict::<FieldPrime>(
                    s,
                    &vec![Type::Struct(vec![("a".into(), Type::FieldElement)])]
                )
                .unwrap(),
                Values(vec![Value::Struct(
                    vec![("a".to_string(), Value::Field(42.into()))]
                        .into_iter()
                        .collect()
                )])
            );

            let s = r#"[{"b": "42"}]"#;
            assert_eq!(
                parse_strict::<FieldPrime>(
                    s,
                    &vec![Type::Struct(vec![("a".into(), Type::FieldElement)])]
                )
                .unwrap_err(),
                Error::Type("Member with id `a` not found".into())
            );

            let s = r#"[{}]"#;
            assert_eq!(
                parse_strict::<FieldPrime>(
                    s,
                    &vec![Type::Struct(vec![("a".into(), Type::FieldElement)])]
                )
                .unwrap_err(),
                Error::Type("Expected 1 member(s), found 0".into())
            );

            let s = r#"[{"a": false}]"#;
            assert_eq!(
                parse_strict::<FieldPrime>(
                    s,
                    &vec![Type::Struct(vec![("a".into(), Type::FieldElement)])]
                )
                .unwrap_err(),
                Error::Type("Value `false` doesn't match expected type `field`".into())
            );
        }
    }
}
