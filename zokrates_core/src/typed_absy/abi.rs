use typed_absy::types::Signature;
use typed_absy::{Type, TypedFunctionSymbol, TypedProgram};
use zokrates_field::field::Field;

#[derive(Serialize, Deserialize, Debug, Eq, PartialEq)]
pub struct AbiInput {
    pub name: String,
    pub public: bool,
    #[serde(flatten)]
    pub ty: Type,
}

pub type AbiOutput = Type;

#[derive(Serialize, Deserialize, Debug, Eq, PartialEq)]
pub struct Abi {
    pub inputs: Vec<AbiInput>,
    pub outputs: Vec<AbiOutput>,
}

pub trait Generator {
    fn abi(&self) -> Abi;
}

impl<'ast, T: Field> Generator for TypedProgram<'ast, T> {
    fn abi(&self) -> Abi {
        let main = self.modules[&self.main]
            .functions
            .iter()
            .find(|(id, _)| id.id == "main")
            .unwrap()
            .1;
        let main = match main {
            TypedFunctionSymbol::Here(main) => main,
            _ => unreachable!(),
        };

        Abi {
            inputs: main
                .arguments
                .iter()
                .map(|p| AbiInput {
                    public: !p.private,
                    name: p.id.id.to_string(),
                    ty: p.id._type.clone(),
                })
                .collect(),
            outputs: main.signature.outputs.clone(),
        }
    }
}

impl Abi {
    pub fn signature(&self) -> Signature {
        Signature {
            inputs: self.inputs.iter().map(|i| i.ty.clone()).collect(),
            outputs: self.outputs.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    use typed_absy::types::{ArrayType, FunctionKey, StructMember};
    use typed_absy::{Identifier, Parameter, Type, TypedFunction, TypedModule, Variable};
    use zokrates_field::field::FieldPrime;

    #[test]
    fn generate_abi_from_typed_ast() {
        let mut functions = HashMap::new();
        functions.insert(
            FunctionKey::with_id("main"),
            TypedFunctionSymbol::Here(TypedFunction {
                arguments: vec![
                    Parameter {
                        id: Variable::field_element(Identifier {
                            id: "a",
                            version: 0,
                            stack: vec![],
                        }),
                        private: true,
                    },
                    Parameter {
                        id: Variable::boolean(Identifier {
                            id: "b",
                            version: 0,
                            stack: vec![],
                        }),
                        private: false,
                    },
                ],
                statements: vec![],
                signature: Signature::new()
                    .inputs(vec![Type::FieldElement, Type::Boolean])
                    .outputs(vec![Type::FieldElement]),
            }),
        );

        let mut modules = HashMap::new();
        modules.insert(String::from("main"), TypedModule { functions });

        let typed_ast: TypedProgram<FieldPrime> = TypedProgram {
            main: String::from("main"),
            modules,
        };

        let abi: Abi = typed_ast.abi();
        let expected_abi = Abi {
            inputs: vec![
                AbiInput {
                    name: String::from("a"),
                    public: false,
                    ty: Type::FieldElement,
                },
                AbiInput {
                    name: String::from("b"),
                    public: true,
                    ty: Type::Boolean,
                },
            ],
            outputs: vec![Type::FieldElement],
        };

        assert_eq!(expected_abi, abi);
    }

    #[test]
    fn serialize_abi_to_proper_json() {
        let abi: Abi = Abi {
            inputs: vec![
                AbiInput {
                    name: String::from("a"),
                    public: false,
                    ty: Type::FieldElement,
                },
                AbiInput {
                    name: String::from("b"),
                    public: true,
                    ty: Type::Struct(vec![
                        StructMember::new(String::from("c"), Type::FieldElement),
                        StructMember::new(String::from("d"), Type::Boolean),
                    ]),
                },
            ],
            outputs: vec![Type::Array(ArrayType::new(Type::FieldElement, 2))],
        };

        let json = serde_json::to_string(&abi).unwrap();
        assert_eq!(&json, r#"{"inputs":[{"name":"a","public":false,"type":"field"},{"name":"b","public":true,"type":"struct","components":[{"name":"c","type":"field"},{"name":"d","type":"bool"}]}],"outputs":[{"type":"array","components":{"size":2,"type":"field"}}]}"#)
    }
}
