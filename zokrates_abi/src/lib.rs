#![feature(box_patterns, box_syntax)]

pub enum Inputs<T> {
    Raw(Vec<T>),
    Abi(Values<T>),
}

impl<T: Field> Encode<T> for Inputs<T> {
    fn encode(self) -> Vec<T> {
        match self {
            Inputs::Raw(v) => v,
            Inputs::Abi(v) => v.encode(),
        }
    }
}

use std::fmt;
use zokrates_ast::typed::types::{ConcreteType, UBitwidth};

use zokrates_field::Field;

#[derive(Debug, PartialEq, Eq)]
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
pub enum Value<T> {
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    Field(T),
    Boolean(bool),
    Array(Vec<Value<T>>),
    Struct(Vec<(String, Value<T>)>),
    Tuple(Vec<Value<T>>),
}

#[derive(PartialEq, Debug)]
pub struct Values<T>(pub Vec<Value<T>>);

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
            Value::Tuple(elements) => {
                write!(f, "(")?;
                match elements.len() {
                    1 => write!(f, "{},", elements[0]),
                    _ => write!(
                        f,
                        "{}",
                        elements
                            .iter()
                            .map(|e| e.to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                }?;
                write!(f, ")")
            }
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

impl<T: Field> Encode<T> for Value<T> {
    fn encode(self) -> Vec<T> {
        match self {
            Value::Field(t) => vec![t],
            Value::U8(v) => vec![T::from(v)],
            Value::U16(v) => vec![T::from(v)],
            Value::U32(v) => vec![T::from(v)],
            Value::U64(v) => vec![T::from(v)],
            Value::Boolean(b) => vec![T::from(b)],
            Value::Array(a) => a.into_iter().flat_map(|v| v.encode()).collect(),
            Value::Tuple(t) => t.into_iter().flat_map(|v| v.encode()).collect(),
            Value::Struct(s) => s.into_iter().flat_map(|(_, v)| v.encode()).collect(),
        }
    }
}

impl<T: Field> Decode<T> for Values<T> {
    type Expected = Vec<ConcreteType>;

    fn decode(raw: Vec<T>, expected: Self::Expected) -> Self {
        Values(
            expected
                .into_iter()
                .scan(0, |state, e| {
                    let new_state = *state + e.get_primitive_count();
                    let res = Value::decode(raw[*state..new_state].to_vec(), e);
                    *state = new_state;
                    Some(res)
                })
                .collect(),
        )
    }
}

impl<T: Field> Decode<T> for Value<T> {
    type Expected = ConcreteType;

    fn decode(raw: Vec<T>, expected: Self::Expected) -> Self {
        let mut raw = raw;

        match expected {
            ConcreteType::Int => unreachable!(),
            ConcreteType::FieldElement => Value::Field(raw.pop().unwrap()),
            ConcreteType::Uint(UBitwidth::B8) => {
                Value::U8(raw.pop().unwrap().to_dec_string().parse().unwrap())
            }
            ConcreteType::Uint(UBitwidth::B16) => {
                Value::U16(raw.pop().unwrap().to_dec_string().parse().unwrap())
            }
            ConcreteType::Uint(UBitwidth::B32) => {
                Value::U32(raw.pop().unwrap().to_dec_string().parse().unwrap())
            }
            ConcreteType::Uint(UBitwidth::B64) => {
                Value::U64(raw.pop().unwrap().to_dec_string().parse().unwrap())
            }
            ConcreteType::Boolean => {
                let v = raw.pop().unwrap();
                Value::Boolean(if v == 0.into() {
                    false
                } else if v == 1.into() {
                    true
                } else {
                    unreachable!()
                })
            }
            ConcreteType::Array(array_type) => Value::Array(
                raw.chunks(array_type.ty.get_primitive_count())
                    .map(|c| Value::decode(c.to_vec(), *array_type.ty.clone()))
                    .collect(),
            ),
            ConcreteType::Struct(members) => Value::Struct(
                members
                    .into_iter()
                    .scan(0, |state, member| {
                        let new_state = *state + member.ty.get_primitive_count();
                        let res = Value::decode(raw[*state..new_state].to_vec(), *member.ty);
                        *state = new_state;
                        Some((member.id, res))
                    })
                    .collect(),
            ),
            ConcreteType::Tuple(tuple_type) => Value::Tuple(
                tuple_type
                    .elements
                    .into_iter()
                    .scan(0, |state, ty| {
                        let new_state = *state + ty.get_primitive_count();
                        let res = Value::decode(raw[*state..new_state].to_vec(), ty);
                        *state = new_state;
                        Some(res)
                    })
                    .collect(),
            ),
        }
    }
}

impl<T: Field> Encode<T> for Values<T> {
    fn encode(self) -> Vec<T> {
        self.0.into_iter().flat_map(|v| v.encode()).collect()
    }
}

impl<T: Field> Value<T> {
    pub fn into_serde_json(self) -> serde_json::Value {
        match self {
            Value::Field(f) => serde_json::Value::String(f.to_dec_string()),
            Value::U8(u) => serde_json::Value::String(format!("{:#04x}", u)),
            Value::U16(u) => serde_json::Value::String(format!("{:#06x}", u)),
            Value::U32(u) => serde_json::Value::String(format!("{:#010x}", u)),
            Value::U64(u) => serde_json::Value::String(format!("{:#018x}", u)),
            Value::Boolean(b) => serde_json::Value::Bool(b),
            Value::Array(a) => {
                serde_json::Value::Array(a.into_iter().map(|e| e.into_serde_json()).collect())
            }
            Value::Tuple(t) => {
                serde_json::Value::Array(t.into_iter().map(|e| e.into_serde_json()).collect())
            }
            Value::Struct(s) => serde_json::Value::Object(
                s.into_iter()
                    .map(|(k, v)| (k, v.into_serde_json()))
                    .collect(),
            ),
        }
    }
}

impl<T: Field> Values<T> {
    pub fn into_serde_json(self) -> serde_json::Value {
        serde_json::Value::Array(self.0.into_iter().map(|e| e.into_serde_json()).collect())
    }
}

fn parse_value<T: Field>(
    value: serde_json::Value,
    expected_type: ConcreteType,
) -> Result<Value<T>, Error> {
    match (&expected_type, value) {
        (ConcreteType::FieldElement, serde_json::Value::String(s)) => {
            T::try_from_dec_str(s.as_str())
                .or_else(|_| T::try_from_str(s.as_str().trim_start_matches("0x"), 16))
                .map(Value::Field)
                .map_err(|_| Error::Type(format!("Could not parse `{}` to field type", s)))
        }
        (ConcreteType::Uint(UBitwidth::B8), serde_json::Value::String(s)) => s
            .as_str()
            .parse::<u8>()
            .or_else(|_| u8::from_str_radix(s.as_str().trim_start_matches("0x"), 16))
            .map(Value::U8)
            .map_err(|_| Error::Type(format!("Could not parse `{}` to u8 type", s))),
        (ConcreteType::Uint(UBitwidth::B16), serde_json::Value::String(s)) => s
            .as_str()
            .parse::<u16>()
            .or_else(|_| u16::from_str_radix(s.as_str().trim_start_matches("0x"), 16))
            .map(Value::U16)
            .map_err(|_| Error::Type(format!("Could not parse `{}` to u16 type", s))),
        (ConcreteType::Uint(UBitwidth::B32), serde_json::Value::String(s)) => s
            .as_str()
            .parse::<u32>()
            .or_else(|_| u32::from_str_radix(s.as_str().trim_start_matches("0x"), 16))
            .map(Value::U32)
            .map_err(|_| Error::Type(format!("Could not parse `{}` to u32 type", s))),
        (ConcreteType::Uint(UBitwidth::B64), serde_json::Value::String(s)) => s
            .as_str()
            .parse::<u64>()
            .or_else(|_| u64::from_str_radix(s.as_str().trim_start_matches("0x"), 16))
            .map(Value::U64)
            .map_err(|_| Error::Type(format!("Could not parse `{}` to u64 type", s))),
        (ConcreteType::Boolean, serde_json::Value::Bool(b)) => Ok(Value::Boolean(b)),
        (ConcreteType::Array(array_type), serde_json::Value::Array(a)) => {
            let size = *array_type.size;
            if a.len() != size as usize {
                Err(Error::Type(format!(
                    "Expected array of size {}, found array of size {}",
                    size,
                    a.len()
                )))
            } else {
                a.into_iter()
                    .map(|v| parse_value(v, *array_type.ty.clone()))
                    .collect::<Result<_, _>>()
                    .map(Value::Array)
            }
        }
        (ConcreteType::Tuple(tuple_type), serde_json::Value::Array(a)) => {
            let size = tuple_type.elements.len();
            if a.len() != size {
                Err(Error::Type(format!(
                    "Expected tuple of size {}, found array of size {}",
                    size,
                    a.len()
                )))
            } else {
                a.into_iter()
                    .zip(tuple_type.elements.iter())
                    .map(|(v, ty)| parse_value(v, ty.clone()))
                    .collect::<Result<_, _>>()
                    .map(Value::Tuple)
            }
        }
        (ConcreteType::Struct(struct_type), serde_json::Value::Object(mut o)) => {
            if o.len() != struct_type.members_count() {
                Err(Error::Type(format!(
                    "Expected {} member(s), found {}",
                    struct_type.members_count(),
                    o.len()
                )))
            } else {
                Ok(Value::Struct(
                    struct_type
                        .members
                        .iter()
                        .map(|m| {
                            o.remove(&m.id)
                                .ok_or_else(|| {
                                    Error::Type(format!("Member with id `{}` not found", m.id))
                                })
                                .map(|v| parse_value(v, *m.ty.clone()).map(|v| (m.id.clone(), v)))
                        })
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .collect::<Result<_, _>>()?,
                ))
            }
        }
        (_, serde_json::Value::Number(n)) => Err(Error::Conversion(format!(
            "Value `{}` isn't allowed, did you mean `\"{}\"`?",
            n, n
        ))),
        (_, v) => Err(Error::Type(format!(
            "Value `{}` doesn't match expected type `{}`",
            v, expected_type
        ))),
    }
}

pub fn parse_strict<T: Field>(s: &str, types: Vec<ConcreteType>) -> Result<Values<T>, Error> {
    let values: serde_json::Value =
        serde_json::from_str(s).map_err(|e| Error::Json(e.to_string()))?;

    match values {
        serde_json::Value::Array(values) => parse_strict_json(values, types),
        _ => Err(Error::Type(format!(
            "Expected an array of values, found `{}`",
            values
        ))),
    }
}

pub fn parse_strict_json<T: Field>(
    values: Vec<serde_json::Value>,
    types: Vec<ConcreteType>,
) -> Result<Values<T>, Error> {
    if values.len() != types.len() {
        return Err(Error::Type(format!(
            "Expected {} inputs, found {}",
            types.len(),
            values.len()
        )));
    }

    Ok(Values(
        types
            .into_iter()
            .zip(values.into_iter())
            .map(|(ty, v)| parse_value(v, ty))
            .collect::<Result<_, _>>()?,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_ast::typed::types::{ConcreteStructMember, ConcreteStructType, ConcreteType};
    use zokrates_field::Bn128Field;

    #[test]
    fn numbers() {
        let s = "[1, 2]";
        assert_eq!(
            parse_strict::<Bn128Field>(
                s,
                vec![ConcreteType::FieldElement, ConcreteType::FieldElement]
            )
            .unwrap_err(),
            Error::Conversion(String::from(
                "Value `1` isn't allowed, did you mean `\"1\"`?"
            ))
        );
    }

    #[test]
    fn fields() {
        let s = r#"["1", "0x42"]"#;
        assert_eq!(
            parse_strict::<Bn128Field>(
                s,
                vec![ConcreteType::FieldElement, ConcreteType::FieldElement]
            )
            .unwrap(),
            Values(vec![Value::Field(1.into()), Value::Field(66.into())])
        );
    }

    #[test]
    fn uints() {
        let s = r#"["0x12", "0x1234", "0x12345678", "0x1234567812345678"]"#;
        assert_eq!(
            parse_strict::<Bn128Field>(
                s,
                vec![
                    ConcreteType::Uint(UBitwidth::B8),
                    ConcreteType::Uint(UBitwidth::B16),
                    ConcreteType::Uint(UBitwidth::B32),
                    ConcreteType::Uint(UBitwidth::B64)
                ]
            )
            .unwrap(),
            Values(vec![
                Value::U8(18u8),
                Value::U16(4660u16),
                Value::U32(305419896u32),
                Value::U64(1311768465173141112u64)
            ])
        );

        let s = r#"["0x1234"]"#;
        assert_eq!(
            parse_strict::<Bn128Field>(s, vec![ConcreteType::Uint(UBitwidth::B32)]).unwrap(),
            Values(vec![Value::U32(4660u32)])
        );

        let s = r#"["0x1234"]"#;
        assert_eq!(
            parse_strict::<Bn128Field>(s, vec![ConcreteType::Uint(UBitwidth::B8)]).unwrap_err(),
            Error::Type("Could not parse `0x1234` to u8 type".into())
        );
    }

    #[test]
    fn bools() {
        let s = "[true, false]";
        assert_eq!(
            parse_strict::<Bn128Field>(s, vec![ConcreteType::Boolean, ConcreteType::Boolean])
                .unwrap(),
            Values(vec![Value::Boolean(true), Value::Boolean(false)])
        );
    }

    #[test]
    fn array() {
        let s = "[[true, false]]";
        assert_eq!(
            parse_strict::<Bn128Field>(s, vec![ConcreteType::array((ConcreteType::Boolean, 2u32))])
                .unwrap(),
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
            parse_strict::<Bn128Field>(
                s,
                vec![ConcreteType::Struct(ConcreteStructType::new(
                    "".into(),
                    "".into(),
                    vec![],
                    vec![ConcreteStructMember::new(
                        "a".into(),
                        ConcreteType::FieldElement
                    )]
                ))]
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
            parse_strict::<Bn128Field>(
                s,
                vec![ConcreteType::Struct(ConcreteStructType::new(
                    "".into(),
                    "".into(),
                    vec![],
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
                    vec![],
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
                    vec![],
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

    #[test]
    fn into_serde() {
        let values = Values::<Bn128Field>(vec![
            Value::Field(1.into()),
            Value::U8(2u8),
            Value::U16(3u16),
            Value::U32(4u32),
            Value::U64(5u64),
            Value::Boolean(true),
            Value::Array(vec![Value::Field(1.into()), Value::Field(2.into())]),
            Value::Struct(vec![
                ("a".to_string(), Value::Field(1.into())),
                ("b".to_string(), Value::Field(2.into())),
            ]),
        ]);

        let serde_value = values.into_serde_json();

        assert_eq!(
            serde_value,
            serde_json::Value::Array(vec![
                serde_json::Value::String("1".into()),
                serde_json::Value::String("0x02".into()),
                serde_json::Value::String("0x0003".into()),
                serde_json::Value::String("0x00000004".into()),
                serde_json::Value::String("0x0000000000000005".into()),
                serde_json::Value::Bool(true),
                serde_json::Value::Array(vec![
                    serde_json::Value::String("1".into()),
                    serde_json::Value::String("2".into())
                ]),
                serde_json::json!({ "a": "1", "b": "2" })
            ])
        )
    }

    mod encode {
        use super::*;

        #[test]
        fn fields() {
            let v = Values::<Bn128Field>(vec![Value::Field(1.into()), Value::Field(2.into())]);
            assert_eq!(v.encode(), vec![1.into(), 2.into()]);
        }

        #[test]
        fn u8s() {
            let v = Values::<Bn128Field>(vec![Value::U8(1), Value::U8(2)]);
            assert_eq!(v.encode(), vec![1.into(), 2.into()]);
        }

        #[test]
        fn bools() {
            let v: Values<Bn128Field> = Values(vec![Value::Boolean(true), Value::Boolean(false)]);
            assert_eq!(v.encode(), vec![1.into(), 0.into()]);
        }

        #[test]
        fn array() {
            let v: Values<Bn128Field> = Values(vec![Value::Array(vec![
                Value::Boolean(true),
                Value::Boolean(false),
            ])]);
            assert_eq!(v.encode(), vec![1.into(), 0.into()]);
        }

        #[test]
        fn struc() {
            let v: Values<Bn128Field> = Values(vec![Value::Struct(
                vec![("a".to_string(), Value::Field(42.into()))]
                    .into_iter()
                    .collect(),
            )]);
            assert_eq!(v.encode(), vec![42.into()]);
        }
    }
}
