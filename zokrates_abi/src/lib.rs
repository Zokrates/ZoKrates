#![feature(box_patterns, box_syntax)]

pub enum Inputs<T> {
    Raw(Vec<T>),
    Abi(CheckedValues<T>),
}

impl<T: From<usize>> Encode<T> for Inputs<T> {
    fn encode(self) -> Vec<T> {
        match self {
            Inputs::Raw(v) => v,
            Inputs::Abi(v) => v.encode(),
        }
    }
}

use std::collections::BTreeMap;
use std::convert::TryFrom;
use std::fmt;
use zokrates_core::typed_absy::Type;

use zokrates_field::field::Field;

type Map<K, V> = BTreeMap<K, V>;

#[derive(Debug, PartialEq)]
pub enum Error {
    Json(String),
    Conversion(String),
    Type(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Json(e) => write!(f, "Invalid JSON: {}", e),
            Error::Conversion(e) => write!(f, "Invalid ZoKrates values: {}", e),
            Error::Type(e) => write!(f, "Type error: {}", e),
        }
    }
}

#[derive(PartialEq, Debug)]
enum Value<T> {
    Field(T),
    Boolean(bool),
    Array(Vec<Value<T>>),
    Struct(Map<String, Value<T>>),
}

#[derive(PartialEq, Debug)]
enum CheckedValue<T> {
    Field(T),
    Boolean(bool),
    Array(Vec<CheckedValue<T>>),
    Struct(Vec<(String, CheckedValue<T>)>),
}

#[derive(PartialEq, Debug)]
pub struct CheckedValues<T>(Vec<CheckedValue<T>>);

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
    fn check(self, ty: Type) -> Result<CheckedValue<T>, String> {
        match (self, ty) {
            (Value::Field(f), Type::FieldElement) => Ok(CheckedValue::Field(f)),
            (Value::Boolean(b), Type::Boolean) => Ok(CheckedValue::Boolean(b)),
            (Value::Array(a), Type::Array(array_type)) => {
                if a.len() != array_type.size {
                    Err(format!(
                        "Expected array of size {}, found array of size {}",
                        array_type.size,
                        a.len()
                    ))
                } else {
                    let a = a
                        .into_iter()
                        .map(|val| val.check(*array_type.ty.clone()))
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok(CheckedValue::Array(a))
                }
            }
            (Value::Struct(mut s), Type::Struct(members)) => {
                if s.len() != members.len() {
                    Err(format!(
                        "Expected {} member(s), found {}",
                        members.len(),
                        s.len()
                    ))
                } else {
                    let s = members
                        .into_iter()
                        .map(|member| {
                            s.remove(&member.id)
                                .ok_or_else(|| format!("Member with id `{}` not found", member.id))
                                .map(|v| v.check(*member.ty.clone()).map(|v| (member.id, v)))
                        })
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .collect::<Result<_, _>>()?;
                    Ok(CheckedValue::Struct(s))
                }
            }
            (v, t) => Err(format!("Value `{}` doesn't match expected type `{}`", v, t)),
        }
    }
}

pub trait Encode<T> {
    fn encode(self) -> Vec<T>;
}

pub trait Decode<T> {
    type Expected;

    fn decode(raw: Vec<T>, expected: Self::Expected) -> Self;
}

impl<T: From<usize>> Encode<T> for CheckedValue<T> {
    fn encode(self) -> Vec<T> {
        match self {
            CheckedValue::Field(t) => vec![t],
            CheckedValue::Boolean(b) => vec![if b { 1.into() } else { 0.into() }],
            CheckedValue::Array(a) => a.into_iter().flat_map(|v| v.encode()).collect(),
            CheckedValue::Struct(s) => s.into_iter().flat_map(|(_, v)| v.encode()).collect(),
        }
    }
}

impl<T: Clone + From<usize> + PartialEq> Decode<T> for CheckedValues<T> {
    type Expected = Vec<Type>;

    fn decode(raw: Vec<T>, expected: Self::Expected) -> Self {
        CheckedValues(
            expected
                .into_iter()
                .scan(0, |state, e| {
                    let new_state = *state + e.get_primitive_count();
                    let res = CheckedValue::decode(raw[*state..new_state].to_vec(), e);
                    *state = new_state;
                    Some(res)
                })
                .collect(),
        )
    }
}

impl<T: From<usize> + PartialEq + Clone> Decode<T> for CheckedValue<T> {
    type Expected = Type;

    fn decode(raw: Vec<T>, expected: Self::Expected) -> Self {
        let mut raw = raw;

        match expected {
            Type::FieldElement => CheckedValue::Field(raw.pop().unwrap()),
            Type::Boolean => {
                let v = raw.pop().unwrap();
                CheckedValue::Boolean(if v == 0.into() {
                    false
                } else if v == 1.into() {
                    true
                } else {
                    unreachable!()
                })
            }
            Type::Array(array_type) => CheckedValue::Array(
                raw.chunks(array_type.ty.get_primitive_count())
                    .map(|c| CheckedValue::decode(c.to_vec(), *array_type.ty.clone()))
                    .collect(),
            ),
            Type::Struct(members) => CheckedValue::Struct(
                members
                    .into_iter()
                    .scan(0, |state, member| {
                        let new_state = *state + member.ty.get_primitive_count();
                        let res = CheckedValue::decode(raw[*state..new_state].to_vec(), *member.ty);
                        *state = new_state;
                        Some((member.id, res))
                    })
                    .collect(),
            ),
        }
    }
}

impl<T: From<usize>> Encode<T> for CheckedValues<T> {
    fn encode(self) -> Vec<T> {
        self.0.into_iter().flat_map(|v| v.encode()).collect()
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

impl<T: Field> Into<serde_json::Value> for CheckedValue<T> {
    fn into(self) -> serde_json::Value {
        match self {
            CheckedValue::Field(f) => serde_json::Value::String(f.to_dec_string()),
            CheckedValue::Boolean(b) => serde_json::Value::Bool(b),
            CheckedValue::Array(a) => {
                serde_json::Value::Array(a.into_iter().map(|e| e.into()).collect())
            }
            CheckedValue::Struct(s) => {
                serde_json::Value::Object(s.into_iter().map(|(k, v)| (k, v.into())).collect())
            }
        }
    }
}

impl<T: Field> Into<serde_json::Value> for CheckedValues<T> {
    fn into(self) -> serde_json::Value {
        serde_json::Value::Array(self.0.into_iter().map(|e| e.into()).collect())
    }
}

fn parse<T: Field>(s: &str) -> Result<Values<T>, Error> {
    let json_values: serde_json::Value =
        serde_json::from_str(s).map_err(|e| Error::Json(e.to_string()))?;
    Values::try_from(json_values).map_err(|e| Error::Conversion(e))
}

pub fn parse_strict<T: Field>(s: &str, types: Vec<Type>) -> Result<CheckedValues<T>, Error> {
    let parsed = parse(s)?;
    if parsed.0.len() != types.len() {
        return Err(Error::Type(format!(
            "Expected {} inputs, found {}",
            types.len(),
            parsed.0.len()
        )));
    }
    let checked = parsed
        .0
        .into_iter()
        .zip(types.into_iter())
        .map(|(v, ty)| v.check(ty))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| Error::Type(e))?;
    Ok(CheckedValues(checked))
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
        use zokrates_core::typed_absy::types::StructMember;

        #[test]
        fn fields() {
            let s = r#"["1", "2"]"#;
            assert_eq!(
                parse_strict::<FieldPrime>(s, vec![Type::FieldElement, Type::FieldElement])
                    .unwrap(),
                CheckedValues(vec![
                    CheckedValue::Field(1.into()),
                    CheckedValue::Field(2.into())
                ])
            );
        }

        #[test]
        fn bools() {
            let s = "[true, false]";
            assert_eq!(
                parse_strict::<FieldPrime>(s, vec![Type::Boolean, Type::Boolean]).unwrap(),
                CheckedValues(vec![
                    CheckedValue::Boolean(true),
                    CheckedValue::Boolean(false)
                ])
            );
        }

        #[test]
        fn array() {
            let s = "[[true, false]]";
            assert_eq!(
                parse_strict::<FieldPrime>(s, vec![Type::array(Type::Boolean, 2)]).unwrap(),
                CheckedValues(vec![CheckedValue::Array(vec![
                    CheckedValue::Boolean(true),
                    CheckedValue::Boolean(false)
                ])])
            );
        }

        #[test]
        fn struc() {
            let s = r#"[{"a": "42"}]"#;
            assert_eq!(
                parse_strict::<FieldPrime>(
                    s,
                    vec![Type::Struct(vec![StructMember::new(
                        "a".into(),
                        Type::FieldElement
                    )])]
                )
                .unwrap(),
                CheckedValues(vec![CheckedValue::Struct(
                    vec![("a".to_string(), CheckedValue::Field(42.into()))]
                        .into_iter()
                        .collect()
                )])
            );

            let s = r#"[{"b": "42"}]"#;
            assert_eq!(
                parse_strict::<FieldPrime>(
                    s,
                    vec![Type::Struct(vec![StructMember::new(
                        "a".into(),
                        Type::FieldElement
                    )])]
                )
                .unwrap_err(),
                Error::Type("Member with id `a` not found".into())
            );

            let s = r#"[{}]"#;
            assert_eq!(
                parse_strict::<FieldPrime>(
                    s,
                    vec![Type::Struct(vec![StructMember::new(
                        "a".into(),
                        Type::FieldElement
                    )])]
                )
                .unwrap_err(),
                Error::Type("Expected 1 member(s), found 0".into())
            );

            let s = r#"[{"a": false}]"#;
            assert_eq!(
                parse_strict::<FieldPrime>(
                    s,
                    vec![Type::Struct(vec![StructMember::new(
                        "a".into(),
                        Type::FieldElement
                    )])]
                )
                .unwrap_err(),
                Error::Type("Value `false` doesn't match expected type `field`".into())
            );
        }
    }

    mod encode {
        use super::*;

        #[test]
        fn fields() {
            let v = CheckedValues(vec![CheckedValue::Field(1), CheckedValue::Field(2)]);
            assert_eq!(v.encode(), vec![1, 2]);
        }

        #[test]
        fn bools() {
            let v: CheckedValues<usize> = CheckedValues(vec![
                CheckedValue::Boolean(true),
                CheckedValue::Boolean(false),
            ]);
            assert_eq!(v.encode(), vec![1, 0]);
        }

        #[test]
        fn array() {
            let v: CheckedValues<usize> = CheckedValues(vec![CheckedValue::Array(vec![
                CheckedValue::Boolean(true),
                CheckedValue::Boolean(false),
            ])]);
            assert_eq!(v.encode(), vec![1, 0]);
        }

        #[test]
        fn struc() {
            let v: CheckedValues<usize> = CheckedValues(vec![CheckedValue::Struct(
                vec![("a".to_string(), CheckedValue::Field(42))]
                    .into_iter()
                    .collect(),
            )]);
            assert_eq!(v.encode(), vec![42]);
        }
    }
}
