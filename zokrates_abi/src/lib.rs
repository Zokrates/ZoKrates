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
use zokrates_core::typed_absy::types::{ConcreteType, UBitwidth};

use zokrates_field::Field;

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
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    Field(T),
    Boolean(bool),
    Array(Vec<Value<T>>),
    Struct(Map<String, Value<T>>),
}

#[derive(PartialEq, Debug)]
enum CheckedValue<T> {
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
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
            Value::U8(v) => write!(f, "{:#04x}", v),
            Value::U16(v) => write!(f, "{:#06x}", v),
            Value::U32(v) => write!(f, "{:#010x}", v),
            Value::U64(v) => write!(f, "{:#018x}", v),
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
    fn check(self, ty: ConcreteType) -> Result<CheckedValue<T>, String> {
        match (self, ty) {
            (Value::Field(f), ConcreteType::FieldElement) => Ok(CheckedValue::Field(f)),
            (Value::U8(f), ConcreteType::Uint(UBitwidth::B8)) => Ok(CheckedValue::U8(f)),
            (Value::U16(f), ConcreteType::Uint(UBitwidth::B16)) => Ok(CheckedValue::U16(f)),
            (Value::U32(f), ConcreteType::Uint(UBitwidth::B32)) => Ok(CheckedValue::U32(f)),
            (Value::U64(f), ConcreteType::Uint(UBitwidth::B64)) => Ok(CheckedValue::U64(f)),
            (Value::Boolean(b), ConcreteType::Boolean) => Ok(CheckedValue::Boolean(b)),
            (Value::Array(a), ConcreteType::Array(array_type)) => {
                let size = array_type.size;

                if a.len() != size as usize {
                    Err(format!(
                        "Expected array of size {}, found array of size {}",
                        size,
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
            (Value::Struct(mut s), ConcreteType::Struct(struc)) => {
                if s.len() != struc.members_count() {
                    Err(format!(
                        "Expected {} member(s), found {}",
                        struc.members_count(),
                        s.len()
                    ))
                } else {
                    let s = struc
                        .members
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
            CheckedValue::U8(t) => vec![T::from(t as usize)],
            CheckedValue::U16(t) => vec![T::from(t as usize)],
            CheckedValue::U32(t) => vec![T::from(t as usize)],
            CheckedValue::U64(t) => vec![T::from(t as usize)],
            CheckedValue::Boolean(b) => vec![if b { 1.into() } else { 0.into() }],
            CheckedValue::Array(a) => a.into_iter().flat_map(|v| v.encode()).collect(),
            CheckedValue::Struct(s) => s.into_iter().flat_map(|(_, v)| v.encode()).collect(),
        }
    }
}

impl<T: Field> Decode<T> for CheckedValues<T> {
    type Expected = Vec<ConcreteType>;

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

impl<T: Field> Decode<T> for CheckedValue<T> {
    type Expected = ConcreteType;

    fn decode(raw: Vec<T>, expected: Self::Expected) -> Self {
        let mut raw = raw;

        match expected {
            ConcreteType::Int => unreachable!(),
            ConcreteType::FieldElement => CheckedValue::Field(raw.pop().unwrap()),
            ConcreteType::Uint(UBitwidth::B8) => {
                CheckedValue::U8(raw.pop().unwrap().to_dec_string().parse().unwrap())
            }
            ConcreteType::Uint(UBitwidth::B16) => {
                CheckedValue::U16(raw.pop().unwrap().to_dec_string().parse().unwrap())
            }
            ConcreteType::Uint(UBitwidth::B32) => {
                CheckedValue::U32(raw.pop().unwrap().to_dec_string().parse().unwrap())
            }
            ConcreteType::Uint(UBitwidth::B64) => {
                CheckedValue::U64(raw.pop().unwrap().to_dec_string().parse().unwrap())
            }
            ConcreteType::Boolean => {
                let v = raw.pop().unwrap();
                CheckedValue::Boolean(if v == 0.into() {
                    false
                } else if v == 1.into() {
                    true
                } else {
                    unreachable!()
                })
            }
            ConcreteType::Array(array_type) => CheckedValue::Array(
                raw.chunks(array_type.ty.get_primitive_count())
                    .map(|c| CheckedValue::decode(c.to_vec(), *array_type.ty.clone()))
                    .collect(),
            ),
            ConcreteType::Struct(members) => CheckedValue::Struct(
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
                .map(Value::try_from)
                .collect::<Result<_, _>>()
                .map(Values),
            v => Err(format!("Expected an array of values, found `{}`", v)),
        }
    }
}

impl<T: Field> TryFrom<serde_json::Value> for Value<T> {
    type Error = String;
    fn try_from(v: serde_json::Value) -> Result<Value<T>, Self::Error> {
        match v {
            serde_json::Value::String(s) => {
                T::try_from_dec_str(&s)
                    .map(Value::Field)
                    .or_else(|_| match s.len() {
                        4 => u8::from_str_radix(&s[2..], 16)
                            .map(Value::U8)
                            .map_err(|_| format!("Expected u8 value, found {}", s)),
                        6 => u16::from_str_radix(&s[2..], 16)
                            .map(Value::U16)
                            .map_err(|_| format!("Expected u16 value, found {}", s)),
                        10 => u32::from_str_radix(&s[2..], 16)
                            .map(Value::U32)
                            .map_err(|_| format!("Expected u32 value, found {}", s)),
                        18 => u64::from_str_radix(&s[2..], 16)
                            .map(Value::U64)
                            .map_err(|_| format!("Expected u64 value, found {}", s)),
                        _ => Err(format!("Cannot parse {} to any type", s)),
                    })
            }
            serde_json::Value::Bool(b) => Ok(Value::Boolean(b)),
            serde_json::Value::Number(n) => Err(format!(
                "Value `{}` isn't allowed, did you mean `\"{}\"`?",
                n, n
            )),
            serde_json::Value::Array(a) => a
                .into_iter()
                .map(Value::try_from)
                .collect::<Result<_, _>>()
                .map(Value::Array),
            serde_json::Value::Object(o) => o
                .into_iter()
                .map(|(k, v)| Value::try_from(v).map(|v| (k, v)))
                .collect::<Result<Map<_, _>, _>>()
                .map(Value::Struct),
            v => Err(format!("Value `{}` isn't allowed", v)),
        }
    }
}

impl<T: Field> CheckedValue<T> {
    pub fn into_serde_json(self) -> serde_json::Value {
        match self {
            CheckedValue::Field(f) => serde_json::Value::String(f.to_dec_string()),
            CheckedValue::U8(u) => serde_json::Value::String(format!("{:#04x}", u)),
            CheckedValue::U16(u) => serde_json::Value::String(format!("{:#06x}", u)),
            CheckedValue::U32(u) => serde_json::Value::String(format!("{:#010x}", u)),
            CheckedValue::U64(u) => serde_json::Value::String(format!("{:#018x}", u)),
            CheckedValue::Boolean(b) => serde_json::Value::Bool(b),
            CheckedValue::Array(a) => {
                serde_json::Value::Array(a.into_iter().map(|e| e.into_serde_json()).collect())
            }
            CheckedValue::Struct(s) => serde_json::Value::Object(
                s.into_iter()
                    .map(|(k, v)| (k, v.into_serde_json()))
                    .collect(),
            ),
        }
    }
}

impl<T: Field> CheckedValues<T> {
    pub fn into_serde_json(self) -> serde_json::Value {
        serde_json::Value::Array(self.0.into_iter().map(|e| e.into_serde_json()).collect())
    }
}

fn parse<T: Field>(s: &str) -> Result<Values<T>, Error> {
    let json_values: serde_json::Value =
        serde_json::from_str(s).map_err(|e| Error::Json(e.to_string()))?;
    Values::try_from(json_values).map_err(Error::Conversion)
}

pub fn parse_strict<T: Field>(
    s: &str,
    types: Vec<ConcreteType>,
) -> Result<CheckedValues<T>, Error> {
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
        .map_err(Error::Type)?;
    Ok(CheckedValues(checked))
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::Bn128Field;

    #[test]
    fn numbers() {
        let s = "[1, 2]";
        assert_eq!(
            parse::<Bn128Field>(s).unwrap_err(),
            Error::Conversion(String::from(
                "Value `1` isn't allowed, did you mean `\"1\"`?"
            ))
        );
    }

    #[test]
    fn fields() {
        let s = r#"["1", "2"]"#;
        assert_eq!(
            parse::<Bn128Field>(s).unwrap(),
            Values(vec![Value::Field(1.into()), Value::Field(2.into())])
        );
    }

    #[test]
    fn bools() {
        let s = "[true, false]";
        assert_eq!(
            parse::<Bn128Field>(s).unwrap(),
            Values(vec![Value::Boolean(true), Value::Boolean(false)])
        );
    }

    #[test]
    fn array() {
        let s = "[[true, false]]";
        assert_eq!(
            parse::<Bn128Field>(s).unwrap(),
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
            parse::<Bn128Field>(s).unwrap(),
            Values(vec![Value::Struct(
                vec![("a".to_string(), Value::Field(42.into()))]
                    .into_iter()
                    .collect()
            )])
        );
    }

    mod strict {
        use super::*;
        use zokrates_core::typed_absy::types::{
            ConcreteStructMember, ConcreteStructType, ConcreteType,
        };

        #[test]
        fn fields() {
            let s = r#"["1", "2"]"#;
            assert_eq!(
                parse_strict::<Bn128Field>(
                    s,
                    vec![ConcreteType::FieldElement, ConcreteType::FieldElement]
                )
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
                parse_strict::<Bn128Field>(s, vec![ConcreteType::Boolean, ConcreteType::Boolean])
                    .unwrap(),
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
                parse_strict::<Bn128Field>(
                    s,
                    vec![ConcreteType::array((ConcreteType::Boolean, 2usize))]
                )
                .unwrap(),
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
                parse_strict::<Bn128Field>(
                    s,
                    vec![ConcreteType::Struct(ConcreteStructType::new(
                        "".into(),
                        "".into(),
                        vec![ConcreteStructMember::new(
                            "a".into(),
                            ConcreteType::FieldElement
                        )]
                    ))]
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
                parse_strict::<Bn128Field>(
                    s,
                    vec![ConcreteType::Struct(ConcreteStructType::new(
                        "".into(),
                        "".into(),
                        vec![ConcreteStructMember::new(
                            "a".into(),
                            ConcreteType::FieldElement
                        )]
                    ))]
                )
                .unwrap_err(),
                Error::Type("Member with id `a` not found".into())
            );

            let s = r#"[{}]"#;
            assert_eq!(
                parse_strict::<Bn128Field>(
                    s,
                    vec![ConcreteType::Struct(ConcreteStructType::new(
                        "".into(),
                        "".into(),
                        vec![ConcreteStructMember::new(
                            "a".into(),
                            ConcreteType::FieldElement
                        )]
                    ))]
                )
                .unwrap_err(),
                Error::Type("Expected 1 member(s), found 0".into())
            );

            let s = r#"[{"a": false}]"#;
            assert_eq!(
                parse_strict::<Bn128Field>(
                    s,
                    vec![ConcreteType::Struct(ConcreteStructType::new(
                        "".into(),
                        "".into(),
                        vec![ConcreteStructMember::new(
                            "a".into(),
                            ConcreteType::FieldElement
                        )]
                    ))]
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
        fn u8s() {
            let v = CheckedValues::<usize>(vec![CheckedValue::U8(1), CheckedValue::U8(2)]);
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
