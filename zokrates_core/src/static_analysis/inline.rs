//! Module containing inlining for the typed AST
//!
//! @file inline.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2019

//! Start from the `main` function in the `main` module and inline all calls except those to flat embeds
//! The resulting program has a single module, where we define a function for each flat embed and replace the function calls with the embeds found
//! during inlining by calls to these functions, to be resolved during flattening.

//! The resulting program has a single module of the form

//! def main() -> ():
//! def _SHA_256_ROUND() -> ():
//! def _UNPACK() -> ():

//! where any call in `main` must be to `_SHA_256_ROUND` or `_UNPACK`

use std::collections::HashMap;
use typed_absy::types::{FunctionKey, StructMember, Type};
use typed_absy::{folder::*, *};
use zokrates_field::field::Field;

/// An inliner
#[derive(Debug)]
pub struct Inliner<'ast, T: Field> {
    modules: TypedModules<'ast, T>, // the modules in which to look for functions when inlining
    module_id: TypedModuleId,       // the current module we're visiting
    statement_buffer: Vec<TypedStatement<'ast, T>>, // a buffer of statements to be added to the inlined statements
    stack: Vec<(TypedModuleId, FunctionKey<'ast>, usize)>, // the current call stack
    call_count: HashMap<(TypedModuleId, FunctionKey<'ast>), usize>, // the call count for each function
}

impl<'ast, T: Field> Inliner<'ast, T> {
    fn with_modules_and_module_id<S: Into<TypedModuleId>>(
        modules: TypedModules<'ast, T>,
        module_id: S,
    ) -> Self {
        Inliner {
            modules,
            module_id: module_id.into(),
            statement_buffer: vec![],
            stack: vec![],
            call_count: HashMap::new(),
        }
    }

    pub fn inline(p: TypedProgram<T>) -> TypedProgram<T> {
        let main_module_id = p.main;

        // get the main module
        let main_module = p.modules.get(&main_module_id).unwrap().clone();

        // get the main function in the main module
        let (main_key, main) = main_module
            .functions
            .into_iter()
            .find(|(k, _)| k.id == "main")
            .unwrap();

        // initialize an inliner over all modules, starting from the main module
        let mut inliner = Inliner::with_modules_and_module_id(p.modules, main_module_id);

        // inline all calls in the main function, recursively
        let main = inliner.fold_function_symbol(main);

        // define a function in the main module for the `unpack` embed
        let unpack = crate::embed::FlatEmbed::Unpack;
        let unpack_key = unpack.key::<T>();

        // define a function in the main module for the `sha256_round` embed
        let sha256_round = crate::embed::FlatEmbed::Sha256Round;
        let sha256_round_key = sha256_round.key::<T>();

        // return a program with a single module containing `main`, `_UNPACK`, and `_SHA256_ROUND
        TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![
                        (unpack_key, TypedFunctionSymbol::Flat(unpack)),
                        (sha256_round_key, TypedFunctionSymbol::Flat(sha256_round)),
                        (main_key, main),
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
        }
    }

    /// try to inline a call to function with key `key` in the stack of `self`
    /// if inlining succeeds, return the expressions returned by the function call
    /// if inlining fails (as in the case of flat function symbols), return the arguments to the function call for further processing
    fn try_inline_call(
        &mut self,
        key: &FunctionKey<'ast>,
        expressions: Vec<TypedExpression<'ast, T>>,
    ) -> Result<Vec<TypedExpression<'ast, T>>, (FunctionKey<'ast>, Vec<TypedExpression<'ast, T>>)>
    {
        // here we clone a function symbol, which is cheap except when it contains the function body, in which case we'd clone anyways
        match self.module().functions.get(&key).unwrap().clone() {
            // if the function called is in the same module, we can go ahead and inline in this module
            TypedFunctionSymbol::Here(function) => {
                // increase the number of calls for this function by one
                let count = self
                    .call_count
                    .entry((self.module_id.clone(), key.clone()))
                    .and_modify(|i| *i += 1)
                    .or_insert(1);
                // push this call to the stack
                self.stack
                    .push((self.module_id.clone(), key.clone(), *count));
                // add definitions for the inputs
                let inputs_bindings: Vec<_> = function
                    .arguments
                    .iter()
                    .zip(expressions)
                    .map(|(a, e)| {
                        TypedStatement::Definition(
                            self.fold_assignee(TypedAssignee::Identifier(a.id.clone())),
                            e,
                        )
                    })
                    .collect();

                self.statement_buffer.extend(inputs_bindings);

                // filter out the return statement and keep it aside
                let (statements, mut ret): (Vec<_>, Vec<_>) = function
                    .statements
                    .into_iter()
                    .flat_map(|s| self.fold_statement(s))
                    .partition(|s| match s {
                        TypedStatement::Return(..) => false,
                        _ => true,
                    });

                // add all statements to the buffer
                self.statement_buffer.extend(statements);

                // pop this call from the stack
                self.stack.pop();

                match ret.pop().unwrap() {
                    TypedStatement::Return(exprs) => Ok(exprs),
                    _ => unreachable!(""),
                }
            }
            // if the function called is in some other module, we switch focus to that module and call the function locally there
            TypedFunctionSymbol::There(function_key, module_id) => {
                // switch focus to `module_id`
                let current_module = self.change_module(module_id);
                // inline the call there
                let res = self.try_inline_call(&function_key, expressions)?;
                // switch back focus
                self.change_module(current_module);
                Ok(res)
            }
            // if the function is a flat symbol, replace the call with a call to the local function we provide so it can be inlined in flattening
            TypedFunctionSymbol::Flat(embed) => Err((embed.key::<T>(), expressions)),
        }
    }

    // Focus the inliner on another module with id `module_id` and return the current `module_id`
    fn change_module(&mut self, module_id: TypedModuleId) -> TypedModuleId {
        std::mem::replace(&mut self.module_id, module_id)
    }

    fn module(&self) -> &TypedModule<'ast, T> {
        self.modules.get(&self.module_id).unwrap()
    }
}

impl<'ast, T: Field> Folder<'ast, T> for Inliner<'ast, T> {
    // add extra statements before the modified statement
    fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        let folded = match s {
            TypedStatement::MultipleDefinition(variables, elist) => match elist {
                TypedExpressionList::FunctionCall(key, exps, types) => {
                    let variables: Vec<_> = variables
                        .into_iter()
                        .map(|a| self.fold_variable(a))
                        .collect();
                    let exps: Vec<_> = exps.into_iter().map(|e| self.fold_expression(e)).collect();

                    match self.try_inline_call(&key, exps) {
                        Ok(ret) => variables
                            .into_iter()
                            .zip(ret.into_iter())
                            .map(|(v, e)| {
                                TypedStatement::Definition(TypedAssignee::Identifier(v), e)
                            })
                            .collect(),
                        Err((key, expressions)) => vec![TypedStatement::MultipleDefinition(
                            variables,
                            TypedExpressionList::FunctionCall(key, expressions, types),
                        )],
                    }
                }
            },
            s => fold_statement(self, s),
        };
        self.statement_buffer.drain(..).chain(folded).collect()
    }

    // prefix all names with the stack
    fn fold_name(&mut self, n: Identifier<'ast>) -> Identifier<'ast> {
        Identifier {
            stack: self.stack.clone(),
            ..n
        }
    }

    // inline calls which return a field element
    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> FieldElementExpression<'ast, T> {
        match e {
            FieldElementExpression::FunctionCall(key, exps) => {
                let exps: Vec<_> = exps.into_iter().map(|e| self.fold_expression(e)).collect();

                match self.try_inline_call(&key, exps) {
                    Ok(mut ret) => match ret.pop().unwrap() {
                        TypedExpression::FieldElement(e) => e,
                        _ => unreachable!(),
                    },
                    Err((key, expressions)) => {
                        FieldElementExpression::FunctionCall(key, expressions)
                    }
                }
            }
            e => fold_field_expression(self, e),
        }
    }

    // inline calls which return a boolean element
    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> BooleanExpression<'ast, T> {
        match e {
            BooleanExpression::FunctionCall(key, exps) => {
                let exps: Vec<_> = exps.into_iter().map(|e| self.fold_expression(e)).collect();

                match self.try_inline_call(&key, exps) {
                    Ok(mut ret) => match ret.pop().unwrap() {
                        TypedExpression::Boolean(e) => e,
                        _ => unreachable!(),
                    },
                    Err((key, expressions)) => BooleanExpression::FunctionCall(key, expressions),
                }
            }
            e => fold_boolean_expression(self, e),
        }
    }

    // inline calls which return an array
    fn fold_array_expression_inner(
        &mut self,
        ty: &Type,
        size: usize,
        e: ArrayExpressionInner<'ast, T>,
    ) -> ArrayExpressionInner<'ast, T> {
        match e {
            ArrayExpressionInner::FunctionCall(key, exps) => {
                let exps: Vec<_> = exps.into_iter().map(|e| self.fold_expression(e)).collect();

                match self.try_inline_call(&key, exps) {
                    Ok(mut ret) => match ret.pop().unwrap() {
                        TypedExpression::Array(e) => e.into_inner(),
                        _ => unreachable!(),
                    },
                    Err((key, expressions)) => ArrayExpressionInner::FunctionCall(key, expressions),
                }
            }
            // default
            e => fold_array_expression_inner(self, ty, size, e),
        }
    }

    fn fold_struct_expression_inner(
        &mut self,
        ty: &Vec<StructMember>,
        e: StructExpressionInner<'ast, T>,
    ) -> StructExpressionInner<'ast, T> {
        match e {
            StructExpressionInner::FunctionCall(key, exps) => {
                let exps: Vec<_> = exps.into_iter().map(|e| self.fold_expression(e)).collect();

                match self.try_inline_call(&key, exps) {
                    Ok(mut ret) => match ret.pop().unwrap() {
                        TypedExpression::Struct(e) => e.into_inner(),
                        _ => unreachable!(),
                    },
                    Err((key, expressions)) => {
                        StructExpressionInner::FunctionCall(key, expressions)
                    }
                }
            }
            // default
            e => fold_struct_expression_inner(self, ty, e),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;
    use typed_absy::types::{FunctionKey, Signature, Type};
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
                        "foo".into(),
                    ),
                ),
            ]
            .into_iter()
            .collect(),
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
        };

        let modules: HashMap<_, _> = vec![("main".into(), main), ("foo".into(), foo)]
            .into_iter()
            .collect();

        let program = TypedProgram {
            main: "main".into(),
            modules,
        };

        let program = Inliner::inline(program);

        assert_eq!(program.modules.len(), 1);
        assert_eq!(
            program
                .modules
                .get(&PathBuf::from("main"))
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
        // def main(a) -> (field):
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
                        arguments: vec![Parameter::private(Variable::field_element("a".into()))],
                        statements: vec![TypedStatement::Return(vec![
                            FieldElementExpression::Mult(
                                box FieldElementExpression::Identifier("a".into()),
                                box FieldElementExpression::FunctionCall(
                                    FunctionKey::with_id("foo").signature(
                                        Signature::new()
                                            .inputs(vec![Type::FieldElement])
                                            .outputs(vec![Type::FieldElement]),
                                    ),
                                    vec![FieldElementExpression::Identifier("a".into()).into()],
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
                        "foo".into(),
                    ),
                ),
            ]
            .into_iter()
            .collect(),
        };

        let foo = TypedModule {
            functions: vec![(
                FunctionKey::with_id("foo").signature(
                    Signature::new()
                        .inputs(vec![Type::FieldElement])
                        .outputs(vec![Type::FieldElement]),
                ),
                TypedFunctionSymbol::Here(TypedFunction {
                    arguments: vec![Parameter::private(Variable::field_element("a".into()))],
                    statements: vec![TypedStatement::Return(vec![FieldElementExpression::Mult(
                        box FieldElementExpression::Identifier("a".into()),
                        box FieldElementExpression::Identifier("a".into()),
                    )
                    .into()])],
                    signature: Signature::new()
                        .inputs(vec![Type::FieldElement])
                        .outputs(vec![Type::FieldElement]),
                }),
            )]
            .into_iter()
            .collect(),
        };

        let modules: HashMap<_, _> = vec![("main".into(), main), ("foo".into(), foo)]
            .into_iter()
            .collect();

        let program: TypedProgram<FieldPrime> = TypedProgram {
            main: "main".into(),
            modules,
        };

        let program = Inliner::inline(program);

        assert_eq!(program.modules.len(), 1);

        let stack = vec![(
            "foo".into(),
            FunctionKey::with_id("foo").signature(
                Signature::new()
                    .inputs(vec![Type::FieldElement])
                    .outputs(vec![Type::FieldElement]),
            ),
            1,
        )];

        assert_eq!(
            program
                .modules
                .get(&PathBuf::from("main"))
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
                arguments: vec![Parameter::private(Variable::field_element("a".into()))],
                statements: vec![
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::field_element(
                            Identifier::from("a").stack(stack.clone())
                        )),
                        FieldElementExpression::Identifier("a".into()).into()
                    ),
                    TypedStatement::Return(vec![FieldElementExpression::Mult(
                        box FieldElementExpression::Identifier("a".into()),
                        box FieldElementExpression::Mult(
                            box FieldElementExpression::Identifier(
                                Identifier::from("a").stack(stack.clone())
                            ),
                            box FieldElementExpression::Identifier(
                                Identifier::from("a").stack(stack.clone())
                            )
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
        //     field _0 = 42
        //     return _0

        let main = TypedModule {
            functions: vec![
                (
                    FunctionKey::with_id("main")
                        .signature(Signature::new().outputs(vec![Type::FieldElement])),
                    TypedFunctionSymbol::Here(TypedFunction {
                        arguments: vec![],
                        statements: vec![
                            TypedStatement::MultipleDefinition(
                                vec![Variable::field_element("a".into())],
                                TypedExpressionList::FunctionCall(
                                    FunctionKey::with_id("foo").signature(
                                        Signature::new().outputs(vec![Type::FieldElement]),
                                    ),
                                    vec![],
                                    vec![Type::FieldElement],
                                ),
                            ),
                            TypedStatement::Return(vec![FieldElementExpression::Identifier(
                                "a".into(),
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
                        "foo".into(),
                    ),
                ),
            ]
            .into_iter()
            .collect(),
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
        };

        let modules: HashMap<_, _> = vec![("main".into(), main), ("foo".into(), foo)]
            .into_iter()
            .collect();

        let program = TypedProgram {
            main: "main".into(),
            modules,
        };

        let program = Inliner::inline(program);

        assert_eq!(program.modules.len(), 1);
        assert_eq!(
            program
                .modules
                .get(&PathBuf::from("main"))
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
                        TypedAssignee::Identifier(Variable::field_element("a".into())),
                        FieldElementExpression::Number(FieldPrime::from(42)).into()
                    ),
                    TypedStatement::Return(vec![
                        FieldElementExpression::Identifier("a".into()).into(),
                    ])
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
        //     field _0 = 42
        //     return _0

        let main = TypedModule {
            functions: vec![
                (
                    FunctionKey::with_id("main")
                        .signature(Signature::new().outputs(vec![Type::FieldElement])),
                    TypedFunctionSymbol::Here(TypedFunction {
                        arguments: vec![],
                        statements: vec![
                            TypedStatement::MultipleDefinition(
                                vec![Variable::field_element("a".into())],
                                TypedExpressionList::FunctionCall(
                                    FunctionKey::with_id("foo").signature(
                                        Signature::new().outputs(vec![Type::FieldElement]),
                                    ),
                                    vec![],
                                    vec![Type::FieldElement],
                                ),
                            ),
                            TypedStatement::Return(vec![FieldElementExpression::Identifier(
                                "a".into(),
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
        };

        let modules: HashMap<_, _> = vec![("main".into(), main)].into_iter().collect();

        let program = TypedProgram {
            main: "main".into(),
            modules,
        };

        let program = Inliner::inline(program);

        assert_eq!(program.modules.len(), 1);
        assert_eq!(
            program
                .modules
                .get(&PathBuf::from("main"))
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
                        TypedAssignee::Identifier(Variable::field_element("a".into())),
                        FieldElementExpression::Number(FieldPrime::from(42)).into()
                    ),
                    TypedStatement::Return(vec![
                        FieldElementExpression::Identifier("a".into()).into(),
                    ])
                ],
                signature: Signature::new().outputs(vec![Type::FieldElement]),
            })
        );
    }

    #[test]
    fn recursive_call_in_other_module() {
        // // main
        // def main(field a) -> (field):
        //     return id(id(a))

        // // id
        // def main(field a) -> (field)
        //     return a

        // inlined
        // def main(field a) -> (field)
        //     id_main_0_a = a
        //     id_main_1_a = id_main_0_a
        //     return id_main_1_a

        let main = TypedModule {
            functions: vec![
                (
                    FunctionKey::with_id("main").signature(
                        Signature::new()
                            .inputs(vec![Type::FieldElement])
                            .outputs(vec![Type::FieldElement]),
                    ),
                    TypedFunctionSymbol::Here(TypedFunction {
                        arguments: vec![Parameter::private(Variable::field_element("a".into()))],
                        statements: vec![TypedStatement::Return(vec![
                            FieldElementExpression::FunctionCall(
                                FunctionKey::with_id("id").signature(
                                    Signature::new()
                                        .inputs(vec![Type::FieldElement])
                                        .outputs(vec![Type::FieldElement]),
                                ),
                                vec![FieldElementExpression::FunctionCall(
                                    FunctionKey::with_id("id").signature(
                                        Signature::new()
                                            .inputs(vec![Type::FieldElement])
                                            .outputs(vec![Type::FieldElement]),
                                    ),
                                    vec![FieldElementExpression::Identifier("a".into()).into()],
                                )
                                .into()],
                            )
                            .into(),
                        ])],
                        signature: Signature::new()
                            .inputs(vec![Type::FieldElement])
                            .outputs(vec![Type::FieldElement]),
                    }),
                ),
                (
                    FunctionKey::with_id("id").signature(
                        Signature::new()
                            .inputs(vec![Type::FieldElement])
                            .outputs(vec![Type::FieldElement]),
                    ),
                    TypedFunctionSymbol::There(
                        FunctionKey::with_id("main").signature(
                            Signature::new()
                                .inputs(vec![Type::FieldElement])
                                .outputs(vec![Type::FieldElement]),
                        ),
                        "id".into(),
                    ),
                ),
            ]
            .into_iter()
            .collect(),
        };

        let id = TypedModule {
            functions: vec![(
                FunctionKey::with_id("main").signature(
                    Signature::new()
                        .inputs(vec![Type::FieldElement])
                        .outputs(vec![Type::FieldElement]),
                ),
                TypedFunctionSymbol::Here(TypedFunction {
                    arguments: vec![Parameter::private(Variable::field_element("a".into()))],
                    statements: vec![TypedStatement::Return(vec![
                        FieldElementExpression::Identifier("a".into()).into(),
                    ])],
                    signature: Signature::new()
                        .inputs(vec![Type::FieldElement])
                        .outputs(vec![Type::FieldElement]),
                }),
            )]
            .into_iter()
            .collect(),
        };

        let modules = vec![("main".into(), main), ("id".into(), id)]
            .into_iter()
            .collect();

        let program: TypedProgram<FieldPrime> = TypedProgram {
            main: "main".into(),
            modules,
        };

        let program = Inliner::inline(program);

        let stack0 = vec![(
            "id".into(),
            FunctionKey::with_id("main").signature(
                Signature::new()
                    .inputs(vec![Type::FieldElement])
                    .outputs(vec![Type::FieldElement]),
            ),
            1,
        )];
        let stack1 = vec![(
            "id".into(),
            FunctionKey::with_id("main").signature(
                Signature::new()
                    .inputs(vec![Type::FieldElement])
                    .outputs(vec![Type::FieldElement]),
            ),
            2,
        )];

        assert_eq!(program.modules.len(), 1);
        assert_eq!(
            program
                .modules
                .get(&PathBuf::from("main"))
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
                arguments: vec![Parameter::private(Variable::field_element("a".into()))],
                statements: vec![
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::field_element(
                            Identifier::from("a").stack(stack0.clone())
                        )),
                        FieldElementExpression::Identifier("a".into()).into()
                    ),
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::field_element(
                            Identifier::from("a").stack(stack1.clone())
                        )),
                        FieldElementExpression::Identifier(
                            Identifier::from("a").stack(stack0.clone())
                        )
                        .into()
                    ),
                    TypedStatement::Return(vec![FieldElementExpression::Identifier(
                        Identifier::from("a").stack(stack1.clone())
                    )
                    .into(),])
                ],
                signature: Signature::new()
                    .inputs(vec![Type::FieldElement])
                    .outputs(vec![Type::FieldElement]),
            })
        );
    }
}
