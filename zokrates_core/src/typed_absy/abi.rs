use crate::typed_absy::types::{ConcreteSignature, ConcreteType};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
pub struct AbiInput {
    pub name: String,
    pub public: bool,
    #[serde(flatten)]
    pub ty: ConcreteType,
}

pub type AbiOutput = ConcreteType;

#[derive(Serialize, Deserialize, Debug, Eq, PartialEq)]
pub struct Abi {
    pub inputs: Vec<AbiInput>,
    pub outputs: Vec<AbiOutput>,
}

impl Abi {
    pub fn signature(&self) -> ConcreteSignature {
        ConcreteSignature {
            generics: vec![],
            inputs: self.inputs.iter().map(|i| i.ty.clone()).collect(),
            outputs: self.outputs.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typed_absy::types::{
        ConcreteArrayType, ConcreteFunctionKey, ConcreteStructMember, ConcreteStructType, UBitwidth,
    };
    use crate::typed_absy::{
        parameter::DeclarationParameter, variable::DeclarationVariable, ConcreteType,
        TypedFunction, TypedFunctionSymbol, TypedModule, TypedProgram,
    };
    use std::collections::HashMap;
    use zokrates_field::Bn128Field;

    #[test]
    fn generate_abi_from_typed_ast() {
        let mut functions = HashMap::new();
        functions.insert(
            ConcreteFunctionKey::with_location("main", "main").into(),
            TypedFunctionSymbol::Here(TypedFunction {
                arguments: vec![
                    DeclarationParameter {
                        id: DeclarationVariable::field_element("a"),
                        private: true,
                    },
                    DeclarationParameter {
                        id: DeclarationVariable::boolean("b"),
                        private: false,
                    },
                ],
                statements: vec![],
                signature: ConcreteSignature::new()
                    .inputs(vec![ConcreteType::FieldElement, ConcreteType::Boolean])
                    .outputs(vec![ConcreteType::FieldElement])
                    .into(),
            }),
        );

        let mut modules = HashMap::new();
        modules.insert("main".into(), TypedModule { functions });

        let typed_ast: TypedProgram<Bn128Field> = TypedProgram {
            main: "main".into(),
            modules,
        };

        let abi: Abi = typed_ast.abi();
        let expected_abi = Abi {
            inputs: vec![
                AbiInput {
                    name: String::from("a"),
                    public: false,
                    ty: ConcreteType::FieldElement,
                },
                AbiInput {
                    name: String::from("b"),
                    public: true,
                    ty: ConcreteType::Boolean,
                },
            ],
            outputs: vec![ConcreteType::FieldElement],
        };

        assert_eq!(expected_abi, abi);
    }

    #[test]
    fn serialize_empty() {
        let abi: Abi = Abi {
            inputs: vec![],
            outputs: vec![],
        };

        let json = serde_json::to_string(&abi).unwrap();
        assert_eq!(&json, r#"{"inputs":[],"outputs":[]}"#);
        let de_abi: Abi = serde_json::from_str(json.as_ref()).unwrap();
        assert_eq!(de_abi, abi);
    }

    #[test]
    #[should_panic]
    fn serialize_integer() {
        // serializing the Int type should panic as it is not allowed in signatures

        let abi: Abi = Abi {
            inputs: vec![],
            outputs: vec![ConcreteType::Int],
        };

        let _ = serde_json::to_string_pretty(&abi).unwrap();
    }

    #[test]
    fn serialize_field() {
        let abi: Abi = Abi {
            inputs: vec![
                AbiInput {
                    name: String::from("a"),
                    public: true,
                    ty: ConcreteType::FieldElement,
                },
                AbiInput {
                    name: String::from("b"),
                    public: true,
                    ty: ConcreteType::FieldElement,
                },
            ],
            outputs: vec![ConcreteType::FieldElement],
        };

        let json = serde_json::to_string_pretty(&abi).unwrap();
        assert_eq!(
            &json,
            r#"{
  "inputs": [
    {
      "name": "a",
      "public": true,
      "type": "field"
    },
    {
      "name": "b",
      "public": true,
      "type": "field"
    }
  ],
  "outputs": [
    {
      "type": "field"
    }
  ]
}"#
        );

        let de_abi: Abi = serde_json::from_str(json.as_ref()).unwrap();
        assert_eq!(de_abi, abi);
    }

    #[test]
    fn serialize_uints() {
        let abi: Abi = Abi {
            inputs: vec![
                AbiInput {
                    name: String::from("a"),
                    public: true,
                    ty: ConcreteType::Uint(UBitwidth::B8),
                },
                AbiInput {
                    name: String::from("b"),
                    public: true,
                    ty: ConcreteType::Uint(UBitwidth::B16),
                },
                AbiInput {
                    name: String::from("c"),
                    public: true,
                    ty: ConcreteType::Uint(UBitwidth::B32),
                },
            ],
            outputs: vec![],
        };

        let json = serde_json::to_string_pretty(&abi).unwrap();
        assert_eq!(
            &json,
            r#"{
  "inputs": [
    {
      "name": "a",
      "public": true,
      "type": "u8"
    },
    {
      "name": "b",
      "public": true,
      "type": "u16"
    },
    {
      "name": "c",
      "public": true,
      "type": "u32"
    }
  ],
  "outputs": []
}"#
        );

        let de_abi: Abi = serde_json::from_str(json.as_ref()).unwrap();
        assert_eq!(de_abi, abi);
    }

    #[test]
    fn serialize_struct() {
        let abi: Abi = Abi {
            inputs: vec![AbiInput {
                name: String::from("foo"),
                public: true,
                ty: ConcreteType::Struct(ConcreteStructType::new(
                    "".into(),
                    "Foo".into(),
                    vec![
                        ConcreteStructMember::new(String::from("a"), ConcreteType::FieldElement),
                        ConcreteStructMember::new(String::from("b"), ConcreteType::Boolean),
                    ],
                )),
            }],
            outputs: vec![ConcreteType::Struct(ConcreteStructType::new(
                "".into(),
                "Foo".into(),
                vec![
                    ConcreteStructMember::new(String::from("a"), ConcreteType::FieldElement),
                    ConcreteStructMember::new(String::from("b"), ConcreteType::Boolean),
                ],
            ))],
        };

        let json = serde_json::to_string_pretty(&abi).unwrap();
        assert_eq!(
            &json,
            r#"{
  "inputs": [
    {
      "name": "foo",
      "public": true,
      "type": "struct",
      "components": {
        "name": "Foo",
        "members": [
          {
            "name": "a",
            "type": "field"
          },
          {
            "name": "b",
            "type": "bool"
          }
        ]
      }
    }
  ],
  "outputs": [
    {
      "type": "struct",
      "components": {
        "name": "Foo",
        "members": [
          {
            "name": "a",
            "type": "field"
          },
          {
            "name": "b",
            "type": "bool"
          }
        ]
      }
    }
  ]
}"#
        );

        let de_abi: Abi = serde_json::from_str(json.as_ref()).unwrap();
        assert_eq!(de_abi, abi);
    }

    #[test]
    fn serialize_nested_struct() {
        let abi: Abi = Abi {
            inputs: vec![AbiInput {
                name: String::from("foo"),
                public: true,
                ty: ConcreteType::Struct(ConcreteStructType::new(
                    "".into(),
                    "Foo".into(),
                    vec![ConcreteStructMember::new(
                        String::from("bar"),
                        ConcreteType::Struct(ConcreteStructType::new(
                            "".into(),
                            "Bar".into(),
                            vec![
                                ConcreteStructMember::new(
                                    String::from("a"),
                                    ConcreteType::FieldElement,
                                ),
                                ConcreteStructMember::new(
                                    String::from("b"),
                                    ConcreteType::FieldElement,
                                ),
                            ],
                        )),
                    )],
                )),
            }],
            outputs: vec![],
        };

        let json = serde_json::to_string_pretty(&abi).unwrap();
        assert_eq!(
            &json,
            r#"{
  "inputs": [
    {
      "name": "foo",
      "public": true,
      "type": "struct",
      "components": {
        "name": "Foo",
        "members": [
          {
            "name": "bar",
            "type": "struct",
            "components": {
              "name": "Bar",
              "members": [
                {
                  "name": "a",
                  "type": "field"
                },
                {
                  "name": "b",
                  "type": "field"
                }
              ]
            }
          }
        ]
      }
    }
  ],
  "outputs": []
}"#
        );

        let de_abi: Abi = serde_json::from_str(json.as_ref()).unwrap();
        assert_eq!(de_abi, abi);
    }

    #[test]
    fn serialize_struct_array() {
        let abi: Abi = Abi {
            inputs: vec![AbiInput {
                name: String::from("a"),
                public: false,
                ty: ConcreteType::Array(ConcreteArrayType::new(
                    ConcreteType::Struct(ConcreteStructType::new(
                        "".into(),
                        "Foo".into(),
                        vec![
                            ConcreteStructMember::new(
                                String::from("b"),
                                ConcreteType::FieldElement,
                            ),
                            ConcreteStructMember::new(String::from("c"), ConcreteType::Boolean),
                        ],
                    )),
                    2,
                )),
            }],
            outputs: vec![ConcreteType::Boolean],
        };

        let json = serde_json::to_string_pretty(&abi).unwrap();
        assert_eq!(
            &json,
            r#"{
  "inputs": [
    {
      "name": "a",
      "public": false,
      "type": "array",
      "components": {
        "size": 2,
        "type": "struct",
        "components": {
          "name": "Foo",
          "members": [
            {
              "name": "b",
              "type": "field"
            },
            {
              "name": "c",
              "type": "bool"
            }
          ]
        }
      }
    }
  ],
  "outputs": [
    {
      "type": "bool"
    }
  ]
}"#
        );

        let de_abi: Abi = serde_json::from_str(json.as_ref()).unwrap();
        assert_eq!(de_abi, abi);
    }

    #[test]
    fn serialize_multi_dimensional_array() {
        let abi: Abi = Abi {
            inputs: vec![AbiInput {
                name: String::from("a"),
                public: false,
                ty: ConcreteType::Array(ConcreteArrayType::new(
                    ConcreteType::Array(ConcreteArrayType::new(ConcreteType::FieldElement, 2)),
                    2,
                )),
            }],
            outputs: vec![ConcreteType::FieldElement],
        };

        let json = serde_json::to_string_pretty(&abi).unwrap();
        assert_eq!(
            &json,
            r#"{
  "inputs": [
    {
      "name": "a",
      "public": false,
      "type": "array",
      "components": {
        "size": 2,
        "type": "array",
        "components": {
          "size": 2,
          "type": "field"
        }
      }
    }
  ],
  "outputs": [
    {
      "type": "field"
    }
  ]
}"#
        );

        let de_abi: Abi = serde_json::from_str(json.as_ref()).unwrap();
        assert_eq!(de_abi, abi);
    }
}
