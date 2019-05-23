use std::collections::HashMap;
use typed_absy::{folder::*, *};
use types::FunctionKey;
use zokrates_field::field::Field;

#[derive(Debug)]
pub struct Inliner<'a, T: Field> {
    modules: &'a TypedModules<T>,
    module_id: TypedModuleId,
    statement_buffer: Vec<TypedStatement<T>>,
    context: Vec<(TypedModuleId, FunctionKey, usize)>,
    call_count: HashMap<(TypedModuleId, FunctionKey), usize>,
}

impl<'a, T: Field> Inliner<'a, T> {
    fn with_modules_and_module_id_and_call_count_and_context<S: Into<TypedModuleId>>(
        modules: &'a TypedModules<T>,
        module_id: S,
        call_count: HashMap<(TypedModuleId, FunctionKey), usize>,
        context: Vec<(TypedModuleId, FunctionKey, usize)>,
    ) -> Self {
        Inliner {
            modules,
            module_id: module_id.into(),
            statement_buffer: vec![],
            call_count,
            context,
        }
    }

    pub fn inline(p: TypedProgram<T>) -> TypedProgram<T> {
        let modules = p.modules.clone();
        let context = vec![];
        let call_count = HashMap::new();
        Inliner::with_modules_and_module_id_and_call_count_and_context(
            &modules,
            p.main.clone(),
            call_count,
            context,
        )
        .fold_program(p)
    }

    fn inline_call(
        &mut self,
        function: &TypedFunction<T>,
        expressions: Vec<TypedExpression<T>>,
    ) -> Vec<TypedExpression<T>> {
        // add definitions for the inputs
        let inputs_bindings: Vec<_> = function
            .arguments
            .iter()
            .zip(expressions)
            .map(|(a, e)| {
                TypedStatement::Definition(
                    TypedAssignee::Identifier(self.fold_variable(a.id.clone())),
                    e,
                )
            })
            .collect();

        self.statement_buffer.extend(inputs_bindings);

        // filter out the return statement and keep it aside
        let (statements, ret): (Vec<_>, Vec<_>) = function
            .statements
            .clone()
            .into_iter()
            .flat_map(|s| self.fold_statement(s))
            .partition(|s| match s {
                TypedStatement::Return(..) => false,
                _ => true,
            });

        // add all statements to the buffer
        self.statement_buffer.extend(statements);

        self.context.pop();

        match ret[0].clone() {
            TypedStatement::Return(exprs) => exprs,
            _ => panic!(""),
        }
    }

    fn fork(&mut self, module_id: TypedModuleId) -> Self {
        Self::with_modules_and_module_id_and_call_count_and_context(
            &self.modules,
            module_id,
            std::mem::replace(&mut self.call_count, HashMap::new()),
            std::mem::replace(&mut self.context, vec![]),
        )
    }

    fn merge(&mut self, other: Inliner<T>) {
        self.statement_buffer.extend(other.statement_buffer);
        self.call_count = other.call_count;
        self.context = other.context;
    }

    fn module(&self) -> &TypedModule<T> {
        self.modules.get(&self.module_id).unwrap()
    }
}

impl<'a, T: Field> Folder<T> for Inliner<'a, T> {
    fn fold_program(&mut self, p: TypedProgram<T>) -> TypedProgram<T> {
        let main_module = p.modules.get(&p.main).unwrap().clone();

        let (main_key, main) = main_module
            .functions
            .iter()
            .find(|(k, _)| k.id == "main")
            .unwrap();

        let main = self.fold_function_symbol(main.clone());

        // TODO import flat used anywhere here :/
        // maybe flag them when we find a call to them and then add them here with the correct path

        let split = crate::types::conversions::split();
        let split_key = FunctionKey::with_id("split").signature(split.signature.clone());

        let sha_round = crate::standard::sha_round();
        let sha_round_key = FunctionKey::with_id("sha256").signature(sha_round.signature.clone());

        TypedProgram {
            main: String::from("main"),
            modules: vec![(
                String::from("main"),
                TypedModule {
                    functions: vec![
                        (split_key, TypedFunctionSymbol::Flat(split)),
                        (sha_round_key, TypedFunctionSymbol::Flat(sha_round)),
                        (main_key.clone(), main),
                    ]
                    .into_iter()
                    .collect(),
                    imports: vec![],
                },
            )]
            .into_iter()
            .collect(),
        }
    }

    fn fold_statement(&mut self, s: TypedStatement<T>) -> Vec<TypedStatement<T>> {
        let folded = match s {
            TypedStatement::MultipleDefinition(variables, elist) => {
                match elist {
                    TypedExpressionList::FunctionCall(key, expressions, types) => {
                        let expressions: Vec<_> = expressions
                            .into_iter()
                            .map(|e| self.fold_expression(e))
                            .collect();

                        let expressions = expressions
                            .into_iter()
                            .map(|e| self.fold_expression(e))
                            .collect();
                        // get the symbol
                        let symbol = self.module().functions.get(&key).unwrap().clone();
                        match symbol {
                            TypedFunctionSymbol::Here(function) => {
                                self.call_count
                                    .entry((self.module_id.clone(), key.clone()))
                                    .and_modify(|i| *i += 1)
                                    .or_insert(1);
                                self.context.push((
                                    self.module_id.clone(),
                                    key.clone(),
                                    *self
                                        .call_count
                                        .get(&(self.module_id.clone(), key.clone()))
                                        .unwrap(),
                                ));
                                // if it's here, we can inline the call recursively with the same checker as the context is the same
                                let ret = self.inline_call(&function, expressions);
                                let variables: Vec<_> = variables
                                    .into_iter()
                                    .map(|a| self.fold_variable(a))
                                    .collect();
                                variables
                                    .into_iter()
                                    .zip(ret.into_iter())
                                    .map(|(v, e)| {
                                        TypedStatement::Definition(TypedAssignee::Identifier(v), e)
                                    })
                                    .collect()
                            }
                            TypedFunctionSymbol::There(function_key, typed_module_id) => {
                                // if it's there, create a new Inliner, inline there and get the statements back
                                // calling `There(key, module)` is calling `key` in `module`
                                let mut inliner = self.fork(typed_module_id); // create a new inliner for `typed_module_id` with the call count starting from where we got to
                                let statements =
                                    inliner.fold_statement(TypedStatement::MultipleDefinition(
                                        variables,
                                        TypedExpressionList::FunctionCall(
                                            function_key,
                                            expressions,
                                            types,
                                        ),
                                    )); // inline the function call
                                self.merge(inliner); // merge the inliner back
                                statements
                            }
                            _ => vec![TypedStatement::MultipleDefinition(
                                variables,
                                TypedExpressionList::FunctionCall(key, expressions, types),
                            )],
                            // we do not inline flat calls as we can't do it before flattening
                        }
                    }
                }
            }
            s => fold_statement(self, s),
        };
        self.statement_buffer.drain(..).chain(folded).collect()
    }

    fn fold_field_expression(&mut self, e: FieldElementExpression<T>) -> FieldElementExpression<T> {
        match e {
            FieldElementExpression::FunctionCall(key, expressions) => {
                let expressions = expressions
                    .into_iter()
                    .map(|e| self.fold_expression(e))
                    .collect();
                // get the symbol
                let symbol = self.module().functions.get(&key).unwrap().clone();
                match symbol {
                    TypedFunctionSymbol::Here(function) => {
                        // if it's here, we can inline the call recursively with the same checker as the context is the same

                        self.call_count
                            .entry((self.module_id.clone(), key.clone()))
                            .and_modify(|i| *i += 1)
                            .or_insert(1);
                        self.context.push((
                            self.module_id.clone(),
                            key.clone(),
                            *self
                                .call_count
                                .get(&(self.module_id.clone(), key.clone()))
                                .unwrap(),
                        ));
                        let ret = self.inline_call(&function, expressions);
                        match ret[0].clone() {
                            TypedExpression::FieldElement(e) => e,
                            _ => unreachable!(),
                        }
                    }
                    TypedFunctionSymbol::There(function_key, typed_module_id) => {
                        // if it's there, create a new Inliner, inline there and get the statements back
                        // calling `There(key, module)` is calling `key` in `module`
                        let mut inliner = self.fork(typed_module_id); // create a new inliner for `typed_module_id` with the call count starting from where we got to
                        let expression = inliner.fold_field_expression(
                            FieldElementExpression::FunctionCall(function_key, expressions),
                        ); // inline the function call
                        self.merge(inliner); // merge the inliner back
                        expression // return the return expression
                    }
                    _ => FieldElementExpression::FunctionCall(key, expressions), // we do not inline flat calls as we can't do it before flattening
                }
            }
            e => fold_field_expression(self, e),
        }
    }

    fn fold_field_array_expression(
        &mut self,
        e: FieldElementArrayExpression<T>,
    ) -> FieldElementArrayExpression<T> {
        match e {
            FieldElementArrayExpression::FunctionCall(size, key, expressions) => {
                // get the symbol
                let symbol = self.module().functions.get(&key).unwrap().clone();
                match symbol {
                    TypedFunctionSymbol::Here(function) => {
                        // if it's here, we can inline the call recursively with the same checker as the context is the same

                        self.call_count
                            .entry((self.module_id.clone(), key.clone()))
                            .and_modify(|i| *i += 1)
                            .or_insert(1);
                        self.context.push((
                            self.module_id.clone(),
                            key.clone(),
                            *self
                                .call_count
                                .get(&(self.module_id.clone(), key.clone()))
                                .unwrap(),
                        ));
                        let ret = self.inline_call(&function, expressions);

                        match ret[0].clone() {
                            TypedExpression::FieldElementArray(e) => e,
                            _ => unreachable!(),
                        }
                    }
                    TypedFunctionSymbol::There(function_key, typed_module_id) => {
                        // if it's there, create a new Inliner, inline there and get the statements back
                        // calling `There(key, module)` is calling `key` in `module`
                        let mut inliner = self.fork(typed_module_id); // create a new inliner for `typed_module_id` with the call count starting from where we got to
                        let expression = inliner.fold_field_array_expression(
                            FieldElementArrayExpression::FunctionCall(
                                size,
                                function_key,
                                expressions,
                            ),
                        ); // inline the function call
                        self.merge(inliner); // merge the inliner back
                        expression // return the return expression
                    }
                    _ => FieldElementArrayExpression::FunctionCall(size, key, expressions),
                }
            }
            e => fold_field_array_expression(self, e),
        }
    }

    // prefix all names with context
    fn fold_name(&mut self, n: String) -> String {
        match self.context.len() {
            0 => n,
            _ => format!(
                "{}_{}",
                self.context
                    .iter()
                    .map(|(module_id, function_key, i)| format!(
                        "{}::{}_{}",
                        module_id, function_key.to_slug(), i
                    ))
                    .collect::<Vec<_>>()
                    .join("_"),
                n
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    use types::{FunctionKey, Signature, Type};
    use zokrates_field::field::FieldPrime;

    #[test]
    fn call_other_module_without_variables() {
        // // main
        // from "foo" import foo
        // def main() -> (field):
        //    return foo()
        //
        // // foo
        // def foo() -> (field):
        //    return 42
        //
        //
        // // inlined
        // def main() -> (field):
        //    return 42

        let main = TypedModule {
            functions: vec![
                (
                    FunctionKey::with_id("main")
                        .signature(Signature::new().outputs(vec![Type::FieldElement])),
                    TypedFunctionSymbol::Here(TypedFunction {
                        arguments: vec![],
                        statements: vec![TypedStatement::Return(vec![
                            FieldElementExpression::FunctionCall(
                                FunctionKey::with_id("foo")
                                    .signature(Signature::new().outputs(vec![Type::FieldElement])),
                                vec![],
                            )
                            .into(),
                        ])],
                        signature: Signature::new().outputs(vec![Type::FieldElement]),
                    }),
                ),
                (
                    FunctionKey::with_id("foo")
                        .signature(Signature::new().outputs(vec![Type::FieldElement])),
                    TypedFunctionSymbol::There(
                        FunctionKey::with_id("foo")
                            .signature(Signature::new().outputs(vec![Type::FieldElement])),
                        String::from("foo"),
                    ),
                ),
            ]
            .into_iter()
            .collect(),
            imports: vec![],
        };

        let foo = TypedModule {
            functions: vec![(
                FunctionKey::with_id("foo")
                    .signature(Signature::new().outputs(vec![Type::FieldElement])),
                TypedFunctionSymbol::Here(TypedFunction {
                    arguments: vec![],
                    statements: vec![TypedStatement::Return(vec![
                        FieldElementExpression::Number(FieldPrime::from(42)).into(),
                    ])],
                    signature: Signature::new().outputs(vec![Type::FieldElement]),
                }),
            )]
            .into_iter()
            .collect(),
            imports: vec![],
        };

        let modules: HashMap<_, _> = vec![(String::from("main"), main), (String::from("foo"), foo)]
            .into_iter()
            .collect();

        let program = TypedProgram {
            main: String::from("main"),
            modules,
        };

        let program = Inliner::inline(program);

        assert_eq!(program.modules.len(), 1);
        assert_eq!(
            program
                .modules
                .get(&String::from("main"))
                .unwrap()
                .functions
                .get(
                    &FunctionKey::with_id("main")
                        .signature(Signature::new().outputs(vec![Type::FieldElement]))
                )
                .unwrap(),
            &TypedFunctionSymbol::Here(TypedFunction {
                arguments: vec![],
                statements: vec![TypedStatement::Return(vec![
                    FieldElementExpression::Number(FieldPrime::from(42)).into(),
                ])],
                signature: Signature::new().outputs(vec![Type::FieldElement]),
            })
        );
    }

    #[test]
    fn call_other_module_with_variables() {
        // // main
        // from "foo" import foo
        // def main(field a) -> (field):
        //    return a * foo(a)
        //
        // // foo
        // def foo(field a) -> (field):
        //    return a * a
        //
        //
        // // inlined
        // def main() -> (field):
        //    field a_0 = a
        //    return a * a_0 * a_0

        let main = TypedModule {
            functions: vec![
                (
                    FunctionKey::with_id("main").signature(
                        Signature::new()
                            .inputs(vec![Type::FieldElement])
                            .outputs(vec![Type::FieldElement]),
                    ),
                    TypedFunctionSymbol::Here(TypedFunction {
                        arguments: vec![Parameter::private(Variable::field_element("a"))],
                        statements: vec![TypedStatement::Return(vec![
                            FieldElementExpression::Mult(
                                box FieldElementExpression::Identifier(String::from("a")),
                                box FieldElementExpression::FunctionCall(
                                    FunctionKey::with_id("foo").signature(
                                        Signature::new()
                                            .inputs(vec![Type::FieldElement])
                                            .outputs(vec![Type::FieldElement]),
                                    ),
                                    vec![FieldElementExpression::Identifier(String::from("a"))
                                        .into()],
                                ),
                            )
                            .into(),
                        ])],
                        signature: Signature::new()
                            .inputs(vec![Type::FieldElement])
                            .outputs(vec![Type::FieldElement]),
                    }),
                ),
                (
                    FunctionKey::with_id("foo").signature(
                        Signature::new()
                            .inputs(vec![Type::FieldElement])
                            .outputs(vec![Type::FieldElement]),
                    ),
                    TypedFunctionSymbol::There(
                        FunctionKey::with_id("foo").signature(
                            Signature::new()
                                .inputs(vec![Type::FieldElement])
                                .outputs(vec![Type::FieldElement]),
                        ),
                        String::from("foo"),
                    ),
                ),
            ]
            .into_iter()
            .collect(),
            imports: vec![],
        };

        let foo = TypedModule {
            functions: vec![(
                FunctionKey::with_id("foo").signature(
                    Signature::new()
                        .inputs(vec![Type::FieldElement])
                        .outputs(vec![Type::FieldElement]),
                ),
                TypedFunctionSymbol::Here(TypedFunction {
                    arguments: vec![Parameter::private(Variable::field_element("a"))],
                    statements: vec![TypedStatement::Return(vec![FieldElementExpression::Mult(
                        box FieldElementExpression::Identifier(String::from("a")),
                        box FieldElementExpression::Identifier(String::from("a")),
                    )
                    .into()])],
                    signature: Signature::new()
                        .inputs(vec![Type::FieldElement])
                        .outputs(vec![Type::FieldElement]),
                }),
            )]
            .into_iter()
            .collect(),
            imports: vec![],
        };

        let modules: HashMap<_, _> = vec![(String::from("main"), main), (String::from("foo"), foo)]
            .into_iter()
            .collect();

        let program: TypedProgram<FieldPrime> = TypedProgram {
            main: String::from("main"),
            modules,
        };

        let program = Inliner::inline(program);

        assert_eq!(program.modules.len(), 1);

        assert_eq!(
            program
                .modules
                .get(&String::from("main"))
                .unwrap()
                .functions
                .get(
                    &FunctionKey::with_id("main").signature(
                        Signature::new()
                            .inputs(vec![Type::FieldElement])
                            .outputs(vec![Type::FieldElement])
                    )
                )
                .unwrap(),
            &TypedFunctionSymbol::Here(TypedFunction {
                arguments: vec![Parameter::private(Variable::field_element("a"))],
                statements: vec![
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::field_element("a_0")),
                        FieldElementExpression::Identifier(String::from("a")).into()
                    ),
                    TypedStatement::Return(vec![FieldElementExpression::Mult(
                        box FieldElementExpression::Identifier(String::from("a")),
                        box FieldElementExpression::Mult(
                            box FieldElementExpression::Identifier(String::from("a_0")),
                            box FieldElementExpression::Identifier(String::from("a_0"))
                        )
                    )
                    .into(),])
                ],
                signature: Signature::new()
                    .inputs(vec![Type::FieldElement])
                    .outputs(vec![Type::FieldElement]),
            })
        );
    }

    #[test]
    fn multi_def_from_other_module() {
        // // foo
        // def foo() -> (field):
        //     return 42

        // // main
        // def main() -> (field):
        //     field b = foo()
        //     return b

        // inlined
        // def main() -> (field)
        //     field a_0 = 42
        //     return a_0

        let main = TypedModule {
            functions: vec![
                (
                    FunctionKey::with_id("main")
                        .signature(Signature::new().outputs(vec![Type::FieldElement])),
                    TypedFunctionSymbol::Here(TypedFunction {
                        arguments: vec![],
                        statements: vec![
                            TypedStatement::MultipleDefinition(
                                vec![Variable::field_element("a")],
                                TypedExpressionList::FunctionCall(
                                    FunctionKey::with_id("foo").signature(
                                        Signature::new().outputs(vec![Type::FieldElement]),
                                    ),
                                    vec![],
                                    vec![Type::FieldElement],
                                ),
                            ),
                            TypedStatement::Return(vec![FieldElementExpression::Identifier(
                                String::from("a"),
                            )
                            .into()]),
                        ],
                        signature: Signature::new().outputs(vec![Type::FieldElement]),
                    }),
                ),
                (
                    FunctionKey::with_id("foo")
                        .signature(Signature::new().outputs(vec![Type::FieldElement])),
                    TypedFunctionSymbol::There(
                        FunctionKey::with_id("foo")
                            .signature(Signature::new().outputs(vec![Type::FieldElement])),
                        String::from("foo"),
                    ),
                ),
            ]
            .into_iter()
            .collect(),
            imports: vec![],
        };

        let foo = TypedModule {
            functions: vec![(
                FunctionKey::with_id("foo")
                    .signature(Signature::new().outputs(vec![Type::FieldElement])),
                TypedFunctionSymbol::Here(TypedFunction {
                    arguments: vec![],
                    statements: vec![TypedStatement::Return(vec![
                        FieldElementExpression::Number(FieldPrime::from(42)).into(),
                    ])],
                    signature: Signature::new().outputs(vec![Type::FieldElement]),
                }),
            )]
            .into_iter()
            .collect(),
            imports: vec![],
        };

        let modules: HashMap<_, _> = vec![(String::from("main"), main), (String::from("foo"), foo)]
            .into_iter()
            .collect();

        let program = TypedProgram {
            main: String::from("main"),
            modules,
        };

        let program = Inliner::inline(program);

        assert_eq!(program.modules.len(), 1);
        assert_eq!(
            program
                .modules
                .get(&String::from("main"))
                .unwrap()
                .functions
                .get(
                    &FunctionKey::with_id("main")
                        .signature(Signature::new().outputs(vec![Type::FieldElement]))
                )
                .unwrap(),
            &TypedFunctionSymbol::Here(TypedFunction {
                arguments: vec![],
                statements: vec![
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::field_element("a_0")),
                        FieldElementExpression::Number(FieldPrime::from(42)).into()
                    ),
                    TypedStatement::Return(vec![FieldElementExpression::Identifier(String::from(
                        "a_0"
                    ))
                    .into(),])
                ],
                signature: Signature::new().outputs(vec![Type::FieldElement]),
            })
        );
    }

    #[test]
    fn multi_def_from_same_module() {
        // // main
        // def foo() -> (field):
        //     return 42
        // def main() -> (field):
        //     field a = foo()
        //     return a

        // inlined
        // def main() -> (field)
        //     field a_0 = 42
        //     return a_0

        let main = TypedModule {
            functions: vec![
                (
                    FunctionKey::with_id("main")
                        .signature(Signature::new().outputs(vec![Type::FieldElement])),
                    TypedFunctionSymbol::Here(TypedFunction {
                        arguments: vec![],
                        statements: vec![
                            TypedStatement::MultipleDefinition(
                                vec![Variable::field_element("a")],
                                TypedExpressionList::FunctionCall(
                                    FunctionKey::with_id("foo").signature(
                                        Signature::new().outputs(vec![Type::FieldElement]),
                                    ),
                                    vec![],
                                    vec![Type::FieldElement],
                                ),
                            ),
                            TypedStatement::Return(vec![FieldElementExpression::Identifier(
                                String::from("a"),
                            )
                            .into()]),
                        ],
                        signature: Signature::new().outputs(vec![Type::FieldElement]),
                    }),
                ),
                (
                    FunctionKey::with_id("foo")
                        .signature(Signature::new().outputs(vec![Type::FieldElement])),
                    TypedFunctionSymbol::Here(TypedFunction {
                        arguments: vec![],
                        statements: vec![TypedStatement::Return(vec![
                            FieldElementExpression::Number(FieldPrime::from(42)).into(),
                        ])],
                        signature: Signature::new().outputs(vec![Type::FieldElement]),
                    }),
                ),
            ]
            .into_iter()
            .collect(),
            imports: vec![],
        };

        let modules: HashMap<_, _> = vec![(String::from("main"), main)].into_iter().collect();

        let program = TypedProgram {
            main: String::from("main"),
            modules,
        };

        let program = Inliner::inline(program);

        assert_eq!(program.modules.len(), 1);
        assert_eq!(
            program
                .modules
                .get(&String::from("main"))
                .unwrap()
                .functions
                .get(
                    &FunctionKey::with_id("main")
                        .signature(Signature::new().outputs(vec![Type::FieldElement]))
                )
                .unwrap(),
            &TypedFunctionSymbol::Here(TypedFunction {
                arguments: vec![],
                statements: vec![
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::field_element("a_0")),
                        FieldElementExpression::Number(FieldPrime::from(42)).into()
                    ),
                    TypedStatement::Return(vec![FieldElementExpression::Identifier(String::from(
                        "a_0"
                    ))
                    .into(),])
                ],
                signature: Signature::new().outputs(vec![Type::FieldElement]),
            })
        );
    }
}
