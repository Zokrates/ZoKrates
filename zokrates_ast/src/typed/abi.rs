use crate::typed::types::{ConcreteSignature, ConcreteType};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct AbiInput {
    pub name: String,
    pub public: bool,
    #[serde(flatten)]
    pub ty: ConcreteType,
}

pub type AbiOutput = ConcreteType;

#[derive(Serialize, Deserialize, Debug, Clone, Eq, PartialEq)]
pub struct Abi {
    pub inputs: Vec<AbiInput>,
    pub output: AbiOutput,
}

impl Abi {
    pub fn signature(&self) -> ConcreteSignature {
        ConcreteSignature {
            generics: vec![],
            inputs: self.inputs.iter().map(|i| i.ty.clone()).collect(),
            output: Box::new(self.output.clone()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::typed::types::{
        ConcreteArrayType, ConcreteFunctionKey, ConcreteStructMember, ConcreteStructType,
        GTupleType, UBitwidth,
    };
    use crate::typed::DeclarationType;
    use crate::typed::{
        parameter::DeclarationParameter, variable::DeclarationVariable, ConcreteTupleType,
        ConcreteType, TypedFunction, TypedFunctionSymbol, TypedFunctionSymbolDeclaration,
        TypedModule, TypedProgram,
    };
    use std::collections::BTreeMap;
    use zokrates_field::Bn128Field;

    #[test]
    fn generate_abi_from_typed_ast() {
        let symbols = vec![TypedFunctionSymbolDeclaration::new(
            ConcreteFunctionKey::with_location("main", "main").into(),
            TypedFunctionSymbol::Here(TypedFunction {
                arguments: vec![
                    DeclarationParameter::private(DeclarationVariable::new(
                        "a",
                        DeclarationType::FieldElement,
                    )),
                    DeclarationParameter::public(DeclarationVariable::new(
                        "b",
                        DeclarationType::Boolean,
                    )),
                ],
                statements: vec![],
                signature: ConcreteSignature::new()
                    .inputs(vec![ConcreteType::FieldElement, ConcreteType::Boolean])
                    .output(ConcreteType::FieldElement)
                    .into(),
            }),
        )
        .into()];

        let mut modules = BTreeMap::new();
        modules.insert("main".into(), TypedModule { symbols });

        let typed_ast: TypedProgram<Bn128Field> = TypedProgram {
            main: "main".into(),
            modules,
            module_map: Default::default(),
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
            output: ConcreteType::FieldElement,
        };

        assert_eq!(expected_abi, abi);
    }

    #[test]
    fn serialize_empty() {
        let abi: Abi = Abi {
            inputs: vec![],
            output: ConcreteType::Tuple(GTupleType::new(vec![])),
        };

        let json = serde_json::to_string(&abi).unwrap();
        assert_eq!(
            &json,
            r#"{"inputs":[],"output":{"type":"tuple","components":{"elements":[]}}}"#
        );
        let de_abi: Abi = serde_json::from_str(json.as_ref()).unwrap();
        assert_eq!(de_abi, abi);
    }

    #[test]
    #[should_panic]
    fn serialize_integer() {
        // serializing the Int type should panic as it is not allowed in signatures

        let abi: Abi = Abi {
            inputs: vec![],
            output: ConcreteType::Int,
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
            output: ConcreteType::FieldElement,
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
  "output": {
    "type": "field"
  }
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
            output: ConcreteType::Tuple(GTupleType::new(vec![])),
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
  "output": {
    "type": "tuple",
    "components": {
      "elements": []
    }
  }
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
                    "Bar".into(),
                    vec![Some(1u32)],
                    vec![ConcreteStructMember::new(
                        String::from("a"),
                        ConcreteType::Array(ConcreteArrayType::new(
                            ConcreteType::FieldElement,
                            1u32,
                        )),
                    )],
                )),
            }],
            output: ConcreteType::Struct(ConcreteStructType::new(
                "".into(),
                "Foo".into(),
                vec![],
                vec![
                    ConcreteStructMember::new(String::from("a"), ConcreteType::FieldElement),
                    ConcreteStructMember::new(String::from("b"), ConcreteType::Boolean),
                ],
            )),
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
        "name": "Bar",
        "generics": [
          1
        ],
        "members": [
          {
            "name": "a",
            "type": "array",
            "components": {
              "size": 1,
              "type": "field"
            }
          }
        ]
      }
    }
  ],
  "output": {
    "type": "struct",
    "components": {
      "name": "Foo",
      "generics": [],
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
                    vec![],
                    vec![ConcreteStructMember::new(
                        String::from("bar"),
                        ConcreteType::Struct(ConcreteStructType::new(
                            "".into(),
                            "Bar".into(),
                            vec![],
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
            output: ConcreteType::Tuple(GTupleType::new(vec![])),
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
        "generics": [],
        "members": [
          {
            "name": "bar",
            "type": "struct",
            "components": {
              "name": "Bar",
              "generics": [],
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
  "output": {
    "type": "tuple",
    "components": {
      "elements": []
    }
  }
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
                        vec![],
                        vec![
                            ConcreteStructMember::new(
                                String::from("b"),
                                ConcreteType::FieldElement,
                            ),
                            ConcreteStructMember::new(String::from("c"), ConcreteType::Boolean),
                        ],
                    )),
                    2u32,
                )),
            }],
            output: ConcreteType::Boolean,
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
          "generics": [],
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
  "output": {
    "type": "bool"
  }
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
                    ConcreteType::Array(ConcreteArrayType::new(ConcreteType::FieldElement, 2u32)),
                    2u32,
                )),
            }],
            output: ConcreteType::FieldElement,
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
  "output": {
    "type": "field"
  }
}"#
        );

        let de_abi: Abi = serde_json::from_str(json.as_ref()).unwrap();
        assert_eq!(de_abi, abi);
    }

    #[test]
    fn serialize_tuple() {
        let abi: Abi = Abi {
            inputs: vec![AbiInput {
                name: String::from("a"),
                public: false,
                ty: ConcreteType::Tuple(ConcreteTupleType::new(vec![
                    ConcreteType::FieldElement,
                    ConcreteType::Boolean,
                ])),
            }],
            output: ConcreteType::Tuple(ConcreteTupleType::new(vec![ConcreteType::FieldElement])),
        };

        let json = serde_json::to_string_pretty(&abi).unwrap();
        assert_eq!(
            &json,
            r#"{
  "inputs": [
    {
      "name": "a",
      "public": false,
      "type": "tuple",
      "components": {
        "elements": [
          {
            "type": "field"
          },
          {
            "type": "bool"
          }
        ]
      }
    }
  ],
  "output": {
    "type": "tuple",
    "components": {
      "elements": [
        {
          "type": "field"
        }
      ]
    }
  }
}"#
        );

        let de_abi: Abi = serde_json::from_str(json.as_ref()).unwrap();
        assert_eq!(de_abi, abi);
    }
}
