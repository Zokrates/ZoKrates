use crate::typed_absy::Folder;
use crate::typed_absy::*;
use crate::types::{FunctionKey, Signature, Type};
use types::conversions::cast;
use zokrates_field::field::Field;

pub struct CoreLibInjector {}

impl CoreLibInjector {
    fn new() -> Self {
        CoreLibInjector {}
    }

    pub fn inject<T: Field>(p: TypedProgram<T>) -> TypedProgram<T> {
        CoreLibInjector::new().fold_program(p)
    }
}

impl<T: Field> Folder<T> for CoreLibInjector {
    fn fold_program(&mut self, p: TypedProgram<T>) -> TypedProgram<T> {
        // instanciate core lib functions

        // IfElse

        let signature = Signature::new()
            .inputs(vec![Type::Boolean, Type::FieldElement, Type::FieldElement])
            .outputs(vec![Type::FieldElement]);

        let ie = TypedFunction {
            arguments: vec![
                Parameter {
                    id: Variable {
                        id: "condition".to_string(),
                        _type: Type::Boolean,
                    },
                    private: true,
                },
                Parameter {
                    id: Variable {
                        id: "consequence".to_string(),
                        _type: Type::FieldElement,
                    },
                    private: true,
                },
                Parameter {
                    id: Variable {
                        id: "alternative".to_string(),
                        _type: Type::FieldElement,
                    },
                    private: true,
                },
            ],
            statements: vec![
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element("condition_as_field")),
                    FieldElementExpression::FunctionCall(
                        FunctionKey::with_id("_bool_to_field").signature(
                            Signature::new()
                                .inputs(vec![Type::Boolean])
                                .outputs(vec![Type::FieldElement]),
                        ),
                        vec![BooleanExpression::Identifier("condition".to_string()).into()],
                    )
                    .into(),
                ),
                TypedStatement::Return(vec![FieldElementExpression::Add(
                    box FieldElementExpression::Mult(
                        box FieldElementExpression::Identifier("condition_as_field".to_string()),
                        box FieldElementExpression::Identifier("consequence".to_string()),
                    ),
                    box FieldElementExpression::Mult(
                        box FieldElementExpression::Sub(
                            box FieldElementExpression::Number(T::one()),
                            box FieldElementExpression::Identifier(
                                "condition_as_field".to_string(),
                            ),
                        ),
                        box FieldElementExpression::Identifier("alternative".to_string()),
                    ),
                )
                .into()]),
            ],
            signature: signature.clone(),
        };

        let ie_key = FunctionKey::with_id("_if_else_field").signature(signature);

        // cast
        let bool_to_field = cast(&Type::Boolean, &Type::FieldElement);
        let bool_to_field_key = FunctionKey::with_id("_bool_to_field").signature(
            Signature::new()
                .inputs(vec![Type::Boolean])
                .outputs(vec![Type::FieldElement]),
        );

        // create corelib module
        let core_lib_module = TypedModule {
            functions: vec![
                (ie_key, TypedFunctionSymbol::Here(ie)),
                (bool_to_field_key, TypedFunctionSymbol::Flat(bool_to_field)),
            ]
            .into_iter()
            .collect(),
            imports: vec![],
        };

        TypedProgram {
            main: p.main,
            modules: p
                .modules
                .into_iter()
                .map(|(k, m)| (k, self.fold_module(m)))
                .chain(std::iter::once((
                    String::from("#corelib#"),
                    core_lib_module,
                )))
                .collect(),
        }
    }

    fn fold_module(&mut self, m: TypedModule<T>) -> TypedModule<T> {
        let mut functions = m.functions;
        functions.extend(vec![
            (
                FunctionKey::with_id("_if_else_field").signature(
                    Signature::new()
                        .inputs(vec![Type::Boolean, Type::FieldElement, Type::FieldElement])
                        .outputs(vec![Type::FieldElement]),
                ),
                TypedFunctionSymbol::There(
                    FunctionKey::with_id("_if_else_field").signature(
                        Signature::new()
                            .inputs(vec![Type::Boolean, Type::FieldElement, Type::FieldElement])
                            .outputs(vec![Type::FieldElement]),
                    ),
                    String::from("#corelib#"),
                ),
            ),
            (
                FunctionKey::with_id("_bool_to_field").signature(
                    Signature::new()
                        .inputs(vec![Type::Boolean])
                        .outputs(vec![Type::FieldElement]),
                ),
                TypedFunctionSymbol::There(
                    FunctionKey::with_id("_bool_to_field").signature(
                        Signature::new()
                            .inputs(vec![Type::Boolean])
                            .outputs(vec![Type::FieldElement]),
                    ),
                    String::from("#corelib#"),
                ),
            ),
        ]);

        TypedModule { functions, ..m }
    }
}
