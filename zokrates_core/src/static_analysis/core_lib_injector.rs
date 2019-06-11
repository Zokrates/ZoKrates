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

impl<'ast, T: Field> Folder<'ast, T> for CoreLibInjector {
    fn fold_program(&mut self, p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        // instanciate core lib functions

        // IfElse

        let signature = Signature::new()
            .inputs(vec![Type::Boolean, Type::FieldElement, Type::FieldElement])
            .outputs(vec![Type::FieldElement]);

        let ie = TypedFunction {
            arguments: vec![
                Parameter {
                    id: Variable {
                        id: "condition".into(),
                        _type: Type::Boolean,
                    },
                    private: true,
                },
                Parameter {
                    id: Variable {
                        id: "consequence".into(),
                        _type: Type::FieldElement,
                    },
                    private: true,
                },
                Parameter {
                    id: Variable {
                        id: "alternative".into(),
                        _type: Type::FieldElement,
                    },
                    private: true,
                },
            ],
            statements: vec![
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element("condition_as_field".into())),
                    FieldElementExpression::FunctionCall(
                        FunctionKey::with_id("_bool_to_field").signature(
                            Signature::new()
                                .inputs(vec![Type::Boolean])
                                .outputs(vec![Type::FieldElement]),
                        ),
                        vec![BooleanExpression::Identifier("condition".into()).into()],
                    )
                    .into(),
                ),
                TypedStatement::Return(vec![FieldElementExpression::Add(
                    box FieldElementExpression::Mult(
                        box FieldElementExpression::Identifier("condition_as_field".into()),
                        box FieldElementExpression::Identifier("consequence".into()),
                    ),
                    box FieldElementExpression::Mult(
                        box FieldElementExpression::Sub(
                            box FieldElementExpression::Number(T::one()),
                            box FieldElementExpression::Identifier("condition_as_field".into()),
                        ),
                        box FieldElementExpression::Identifier("alternative".into()),
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

    fn fold_module(&mut self, m: TypedModule<'ast, T>) -> TypedModule<'ast, T> {
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
