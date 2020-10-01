//! Module containing inlining for the typed AST
//!
//! @file inline.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2019

//! Start from the `main` function in the `main` module and inline all calls except those to flat embeds
//! The resulting program has a single module, where we define a function for each flat embed and replace the function calls with the embeds found
//! during inlining by calls to these functions, to be resolved during flattening.

//! The resulting program has a single module of the form

//! def main():
//! def _SHA_256_ROUND():
//! def _UNPACK():

//! where any call in `main` must be to `_SHA_256_ROUND` or `_UNPACK`

use static_analysis::propagate_unroll::Blocked;
use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};
use typed_absy::types::{
    ConcreteFunctionKey, DeclarationFunctionKey, FunctionKey, Type, UBitwidth,
};
use typed_absy::{folder::*, *};
use zokrates_field::Field;

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
struct Location<'ast> {
    module: TypedModuleId,
    key: DeclarationFunctionKey<'ast>,
}

impl<'ast> Location<'ast> {
    fn module(&self) -> &TypedModuleId {
        &self.module
    }
}

type CallCache<'ast, T> = HashMap<
    Location<'ast>,
    HashMap<
        ConcreteFunctionKey<'ast>,
        HashMap<Vec<TypedExpression<'ast, T>>, Vec<TypedExpression<'ast, T>>>,
    >,
>;

enum InlineError<'ast, T> {
    Flat(ConcreteFunctionKey<'ast>, Vec<TypedExpression<'ast, T>>),
    NonConstant(FunctionKey<'ast, T>, Vec<TypedExpression<'ast, T>>),
}

/// An inliner
#[derive(Debug)]
pub struct Inliner<'ast, T: Field> {
    /// the modules in which to look for functions when inlining
    modules: TypedModules<'ast, T>,
    /// the current module we're visiting
    location: Location<'ast>,
    /// a buffer of statements to be added to the inlined statements
    statement_buffer: Vec<TypedStatement<'ast, T>>,
    /// the current call stack
    stack: Vec<(TypedModuleId, ConcreteFunctionKey<'ast>, usize)>,
    /// the call count for each function
    call_count: HashMap<(TypedModuleId, ConcreteFunctionKey<'ast>), usize>,
    /// the cache for memoization: for each function body, tracks function calls
    call_cache: CallCache<'ast, T>,
    /// whether the inliner is blocked, and why
    blocked: Option<Blocked>,
    /// whether we made progress so far
    made_progress: bool,
}

impl<'ast, T: Field> Inliner<'ast, T> {
    fn with_modules_and_module_id_and_key<S: Into<TypedModuleId>>(
        modules: TypedModules<'ast, T>,
        module_id: S,
        key: DeclarationFunctionKey<'ast>,
    ) -> Self {
        Inliner {
            modules,
            location: Location {
                module: module_id.into(),
                key,
            },
            statement_buffer: vec![],
            stack: vec![],
            call_count: HashMap::new(),
            call_cache: HashMap::new(),
            blocked: None,
            made_progress: false,
        }
    }

    pub fn init(p: TypedProgram<'ast, T>) -> Self {
        let main_module_id = p.main.clone();

        let mut p = p;

        // get the main module
        let main_module = p.modules.get(&main_module_id).unwrap().clone();

        let main_key = main_module
            .functions
            .iter()
            .find(|(k, _)| k.id == "main")
            .unwrap()
            .0
            .clone();

        let mut main_module = main_module;

        // define a function in the main module for the `unpack` embed
        let unpack = crate::embed::FlatEmbed::Unpack(T::get_required_bits());
        let unpack_key = unpack.key::<T>();

        // define a function in the main module for the `u32_to_bits` embed
        let u32_to_bits = crate::embed::FlatEmbed::U32ToBits;
        let u32_to_bits_key = u32_to_bits.key::<T>();

        // define a function in the main module for the `u16_to_bits` embed
        let u16_to_bits = crate::embed::FlatEmbed::U16ToBits;
        let u16_to_bits_key = u16_to_bits.key::<T>();

        // define a function in the main module for the `u8_to_bits` embed
        let u8_to_bits = crate::embed::FlatEmbed::U8ToBits;
        let u8_to_bits_key = u8_to_bits.key::<T>();

        // define a function in the main module for the `u32_from_bits` embed
        let u32_from_bits = crate::embed::FlatEmbed::U32FromBits;
        let u32_from_bits_key = u32_from_bits.key::<T>();

        // define a function in the main module for the `u16_from_bits` embed
        let u16_from_bits = crate::embed::FlatEmbed::U16FromBits;
        let u16_from_bits_key = u16_from_bits.key::<T>();

        // define a function in the main module for the `u8_from_bits` embed
        let u8_from_bits = crate::embed::FlatEmbed::U8FromBits;
        let u8_from_bits_key = u8_from_bits.key::<T>();

        main_module.functions.extend(vec![
            (unpack_key.into(), TypedFunctionSymbol::Flat(unpack)),
            (
                u32_from_bits_key.into(),
                TypedFunctionSymbol::Flat(u32_from_bits),
            ),
            (
                u16_from_bits_key.into(),
                TypedFunctionSymbol::Flat(u16_from_bits),
            ),
            (
                u8_from_bits_key.into(),
                TypedFunctionSymbol::Flat(u8_from_bits),
            ),
            (
                u32_to_bits_key.into(),
                TypedFunctionSymbol::Flat(u32_to_bits),
            ),
            (
                u16_to_bits_key.into(),
                TypedFunctionSymbol::Flat(u16_to_bits),
            ),
            (u8_to_bits_key.into(), TypedFunctionSymbol::Flat(u8_to_bits)),
        ]);

        p.modules.insert(main_module_id.clone(), main_module);

        // initialize an inliner over all modules, starting from the main module
        Inliner::with_modules_and_module_id_and_key(
            p.modules,
            main_module_id,
            main_key.clone().try_into().unwrap(),
        )
    }

    pub fn inline(&mut self, p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        let main_module_id = p.main;

        // get the main module
        let main_module = p.modules.get(&main_module_id).unwrap().clone();

        // get the main function in the main module
        let functions = main_module
            .functions
            .into_iter()
            .map(|(k, f)| {
                if k.id == "main" {
                    // inline all calls in the main function, recursively
                    let main = self.fold_function_symbol(f);
                    (k, main)
                } else {
                    (k, f)
                }
            })
            .collect();

        let program = TypedProgram {
            main: "main".into(),
            modules: vec![("main".into(), TypedModule { functions })]
                .into_iter()
                .collect(),
        };

        // match self.blocked.clone() {
        //     None => Output::Complete(program),
        //     Some(blocked) => Output::Blocked(program, blocked, self.made_progress),
        // }

        program
    }

    fn try_inline_call(
        &mut self,
        key: &FunctionKey<'ast, T>,
        expressions: Vec<TypedExpression<'ast, T>>,
    ) -> Result<Vec<TypedExpression<'ast, T>>, InlineError<'ast, T>> {
        match ConcreteFunctionKey::try_from(key.clone()) {
            Ok(concrete_key) => {
                // match self
                //     .call_cache()
                //     .get(&concrete_key)
                //     .map(|m| m.get(&expressions))
                // {
                //     Some(Some(res)) => {
                //         Some(res.clone())
                //     },
                //     _ => None
                // }.map(|res| {
                //     self.statement_buffer.extend(vec![
                //         TypedStatement::PushCallLog(self.module_id().clone(), concrete_key.clone()),
                //         TypedStatement::PopCallLog
                //     ]);
                //     return res;
                // });

                // then, inline the generic function associated with this DeclarationFunctionKey
                let res = self
                    .try_inline_declaration_call(concrete_key.clone(), expressions.clone())
                    .map_err(|e| InlineError::Flat(e.0.into(), e.1));

                res
                // .map(|exprs| {
                //     self.call_cache_mut()
                //         .entry(concrete_key.clone())
                //         .or_insert_with(|| HashMap::new())
                //         .insert(expressions, exprs.clone());
                //     exprs
                // })
            }
            Err(()) => {
                self.blocked = Some(Blocked::Inline);
                Err(InlineError::NonConstant(key.clone(), expressions))
            }
        }
    }

    /// try to inline a call to function with key `key` in the stack of `self`
    /// if inlining succeeds, return the expressions returned by the function call
    /// if inlining fails (as in the case of flat function symbols), return the arguments to the function call for further processing
    fn try_inline_declaration_call(
        &mut self,
        concrete_key: ConcreteFunctionKey<'ast>,
        expressions: Vec<TypedExpression<'ast, T>>,
    ) -> Result<
        Vec<TypedExpression<'ast, T>>,
        (ConcreteFunctionKey<'ast>, Vec<TypedExpression<'ast, T>>),
    > {
        // here we clone a function symbol, which is cheap except when it contains the function body, in which case we'd clone anyways
        match self
            .module()
            .functions
            .iter()
            .find(|(decl_key, _)| concrete_key == **decl_key)
            .map(|(k, v)| (k.clone(), v.clone()))
            .unwrap()
        {
            // if the function called is in the same module, we can inline in this module
            (decl_key, TypedFunctionSymbol::Here(function)) => {
                // if we execute this, it means that we made progress
                self.made_progress = true;

                // get an assignment of generics for this call site
                let assignment = decl_key.signature.specialize(&concrete_key.signature);

                let module_id = self.module_id().clone();

                let call_log = self
                    .fold_statement(TypedStatement::PushCallLog(module_id, concrete_key.clone()));

                self.statement_buffer.extend(call_log);

                for (id, value) in assignment {
                    let assignee = self.fold_assignee(TypedAssignee::Identifier(
                        Variable::with_id_and_type(id, Type::Uint(UBitwidth::B32)),
                    ));
                    self.statement_buffer.push(TypedStatement::Definition(
                        assignee,
                        UExpression::from(value).into(),
                    ))
                }

                let (current_module, current_key) =
                    self.change_context(self.module_id().clone(), decl_key.clone());

                // add definitions for the inputs
                let inputs_bindings: Vec<_> = function
                    .arguments
                    .iter()
                    .zip(expressions.clone())
                    .map(|(a, e)| {
                        TypedStatement::Definition(
                            self.fold_assignee(TypedAssignee::Identifier(a.id.clone().into())),
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

                self.change_context(current_module, current_key);

                // add all statements to the buffer
                self.statement_buffer.extend(statements);

                // pop this call from the stack
                let pop_log = self.fold_statement(TypedStatement::PopCallLog);
                self.statement_buffer.extend(pop_log);

                match ret.pop().unwrap() {
                    TypedStatement::Return(exprs) => Ok(exprs),
                    _ => unreachable!(""),
                }
            }
            // if the function called is in some other module, we switch focus to that module and call the function locally there
            (_, TypedFunctionSymbol::There(function_key, module_id)) => {
                // switch focus to `module_id`
                let (current_module, current_key) =
                    self.change_context(module_id.clone(), function_key.clone());
                // inline the call there
                let res = self
                    .try_inline_declaration_call(function_key.try_into().unwrap(), expressions)?;
                // switch back focus
                self.change_context(current_module, current_key);
                Ok(res)
            }
            // if the function is a flat symbol, replace the call with a call to the local function we provide so it can be inlined in flattening
            (_, TypedFunctionSymbol::Flat(embed)) => {
                Err((embed.key::<T>().try_into().unwrap(), expressions.clone()))
            }
        }

        // res.map(|exprs| {
        //     self.call_cache_mut()
        //         .entry(key.clone())
        //         .or_insert_with(|| HashMap::new())
        //         .insert(expressions, exprs.clone());
        //     exprs
        // })
    }

    // Focus the inliner on another module with id `module_id` and return the current `module_id`
    fn change_context(
        &mut self,
        module_id: TypedModuleId,
        function_key: DeclarationFunctionKey<'ast>,
    ) -> (TypedModuleId, DeclarationFunctionKey<'ast>) {
        let current_module = std::mem::replace(&mut self.location.module, module_id);
        let current_key = std::mem::replace(&mut self.location.key, function_key);
        (current_module, current_key)
    }

    fn module(&self) -> &TypedModule<'ast, T> {
        self.modules.get(self.module_id()).unwrap()
    }

    fn call_cache(
        &mut self,
    ) -> &HashMap<
        ConcreteFunctionKey<'ast>,
        HashMap<Vec<TypedExpression<'ast, T>>, Vec<TypedExpression<'ast, T>>>,
    > {
        self.call_cache
            .entry(self.location.clone())
            .or_insert_with(|| HashMap::new())
    }

    fn call_cache_mut(
        &mut self,
    ) -> &mut HashMap<
        ConcreteFunctionKey<'ast>,
        HashMap<Vec<TypedExpression<'ast, T>>, Vec<TypedExpression<'ast, T>>>,
    > {
        self.call_cache.get_mut(&self.location).unwrap()
    }

    fn module_id(&self) -> &TypedModuleId {
        self.location.module()
    }
}

impl<'ast, T: Field> Folder<'ast, T> for Inliner<'ast, T> {
    // add extra statements before the modified statement
    fn fold_statement<'a>(
        &'a mut self,
        s: TypedStatement<'ast, T>,
    ) -> Vec<TypedStatement<'ast, T>> {
        let folded = match s {
            TypedStatement::PushCallLog(module_id, key) => {
                // increase the number of calls for this function by one
                let count = self
                    .call_count
                    .entry((self.module_id().clone(), key.clone()))
                    .and_modify(|i| *i += 1)
                    .or_insert(1);
                // push this call to the stack
                self.stack.push((module_id.clone(), key.clone(), *count));
                vec![TypedStatement::PushCallLog(module_id, key)]
            }
            TypedStatement::PopCallLog => {
                // push this call to the stack
                self.stack.pop().unwrap();
                vec![TypedStatement::PopCallLog]
            }
            TypedStatement::For(v, from, to, statements) => {
                self.blocked = Some(Blocked::Unroll);
                fold_statement(self, TypedStatement::For(v, from, to, statements))
            }
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
                        Err(e) => match e {
                            InlineError::Flat(key, expressions) => {
                                vec![TypedStatement::MultipleDefinition(
                                    variables,
                                    TypedExpressionList::FunctionCall(
                                        key.into(),
                                        expressions,
                                        types,
                                    ),
                                )]
                            }
                            InlineError::NonConstant(key, expressions) => {
                                vec![TypedStatement::MultipleDefinition(
                                    variables,
                                    TypedExpressionList::FunctionCall(key, expressions, types),
                                )]
                            }
                        },
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

                let key = FunctionKey {
                    signature: Signature {
                        inputs: exps
                            .iter()
                            .map(|e| e.clone().get_type())
                            .collect::<Vec<_>>(),
                        ..key.signature
                    },
                    ..key
                };

                match self.try_inline_call(&key, exps) {
                    Ok(mut ret) => match ret.pop().unwrap() {
                        TypedExpression::FieldElement(e) => e,
                        _ => unreachable!(),
                    },
                    Err(e) => match e {
                        InlineError::Flat(embed_key, expressions) => {
                            let tys = key.signature.outputs.clone();
                            let id = Identifier {
                                id: CoreIdentifier::Call(
                                    embed_key.clone(),
                                    *self
                                        .call_count
                                        .entry((self.module_id().clone(), embed_key.clone()))
                                        .and_modify(|i| *i += 1)
                                        .or_insert(1),
                                ),
                                version: 0,
                                stack: self.stack.clone(),
                            };
                            self.statement_buffer
                                .push(TypedStatement::MultipleDefinition(
                                    vec![Variable::with_id_and_type(id.clone(), tys[0].clone())],
                                    TypedExpressionList::FunctionCall(
                                        embed_key.clone().into(),
                                        expressions.clone(),
                                        tys,
                                    ),
                                ));

                            // self.call_cache_mut()
                            //     .entry(embed_key.clone().into())
                            //     .or_insert_with(|| HashMap::new())
                            //     .insert(
                            //         expressions,
                            //         vec![FieldElementExpression::Identifier(id.clone()).into()],
                            //     );

                            FieldElementExpression::Identifier(id)
                        }
                        InlineError::NonConstant(key, expressions) => {
                            FieldElementExpression::FunctionCall(key, expressions)
                        }
                    },
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
                    Err(e) => match e {
                        InlineError::Flat(embed_key, expressions) => {
                            let tys = key.signature.outputs.clone();
                            let id = Identifier {
                                id: CoreIdentifier::Call(
                                    embed_key.clone(),
                                    *self
                                        .call_count
                                        .entry((self.module_id().clone(), embed_key.clone()))
                                        .and_modify(|i| *i += 1)
                                        .or_insert(1),
                                ),
                                version: 0,
                                stack: self.stack.clone(),
                            };
                            self.statement_buffer
                                .push(TypedStatement::MultipleDefinition(
                                    vec![Variable::with_id_and_type(id.clone(), tys[0].clone())],
                                    TypedExpressionList::FunctionCall(
                                        embed_key.clone().into(),
                                        expressions.clone(),
                                        tys,
                                    ),
                                ));

                            // self.call_cache_mut()
                            //     .entry(embed_key.clone().into())
                            //     .or_insert_with(|| HashMap::new())
                            //     .insert(
                            //         expressions,
                            //         vec![BooleanExpression::Identifier(id.clone()).into()],
                            //     );

                            BooleanExpression::Identifier(id)
                        }
                        InlineError::NonConstant(key, expressions) => {
                            BooleanExpression::FunctionCall(key, expressions)
                        }
                    },
                }
            }
            e => fold_boolean_expression(self, e),
        }
    }

    // inline calls which return an array
    fn fold_array_expression_inner(
        &mut self,
        ty: &Type<'ast, T>,
        size: UExpression<'ast, T>,
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
                    Err(e) => match e {
                        InlineError::Flat(embed_key, expressions) => {
                            let tys = key.signature.outputs.clone();
                            let id = Identifier {
                                id: CoreIdentifier::Call(
                                    embed_key.clone().into(),
                                    *self
                                        .call_count
                                        .entry((self.module_id().clone(), embed_key.clone()))
                                        .and_modify(|i| *i += 1)
                                        .or_insert(1),
                                ),
                                version: 0,
                                stack: self.stack.clone(),
                            };
                            self.statement_buffer
                                .push(TypedStatement::MultipleDefinition(
                                    vec![Variable::with_id_and_type(id.clone(), tys[0].clone())],
                                    TypedExpressionList::FunctionCall(
                                        embed_key.clone().into(),
                                        expressions.clone(),
                                        tys,
                                    ),
                                ));

                            let out = ArrayExpressionInner::Identifier(id);

                            // self.call_cache_mut()
                            //     .entry(embed_key.clone().into())
                            //     .or_insert_with(|| HashMap::new())
                            //     .insert(
                            //         expressions,
                            //         vec![out.clone().annotate(ty.clone(), size).into()],
                            //     );

                            out
                        }
                        InlineError::NonConstant(key, expressions) => {
                            ArrayExpressionInner::FunctionCall(key, expressions)
                        }
                    },
                }
            }
            // default
            e => fold_array_expression_inner(self, ty, size, e),
        }
    }

    fn fold_struct_expression_inner(
        &mut self,
        ty: &StructType<'ast, T>,
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
                    Err(e) => match e {
                        InlineError::Flat(embed_key, expressions) => {
                            let tys = key.signature.outputs.clone();
                            let id = Identifier {
                                id: CoreIdentifier::Call(
                                    embed_key.clone().into(),
                                    *self
                                        .call_count
                                        .entry((self.module_id().clone(), embed_key.clone()))
                                        .and_modify(|i| *i += 1)
                                        .or_insert(1),
                                ),
                                version: 0,
                                stack: self.stack.clone(),
                            };
                            self.statement_buffer
                                .push(TypedStatement::MultipleDefinition(
                                    vec![Variable::with_id_and_type(id.clone(), tys[0].clone())],
                                    TypedExpressionList::FunctionCall(
                                        key.clone(),
                                        expressions.clone(),
                                        tys,
                                    ),
                                ));

                            let out = StructExpressionInner::Identifier(id);

                            // self.call_cache_mut()
                            //     .entry(embed_key.clone().into())
                            //     .or_insert_with(|| HashMap::new())
                            //     .insert(expressions, vec![out.clone().annotate(ty.clone()).into()]);

                            out
                        }
                        InlineError::NonConstant(key, expressions) => {
                            StructExpressionInner::FunctionCall(key, expressions)
                        }
                    },
                }
            }
            // default
            e => fold_struct_expression_inner(self, ty, e),
        }
    }

    fn fold_uint_expression_inner(
        &mut self,
        size: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> UExpressionInner<'ast, T> {
        match e {
            UExpressionInner::FunctionCall(key, exps) => {
                let exps: Vec<_> = exps.into_iter().map(|e| self.fold_expression(e)).collect();

                match self.try_inline_call(&key, exps) {
                    Ok(mut ret) => match ret.pop().unwrap() {
                        TypedExpression::Uint(e) => e.into_inner(),
                        _ => unreachable!(),
                    },
                    Err(e) => match e {
                        InlineError::Flat(embed_key, expressions) => {
                            let tys = key.signature.outputs.clone();
                            let id = Identifier {
                                id: CoreIdentifier::Call(
                                    embed_key.clone().into(),
                                    *self
                                        .call_count
                                        .entry((self.module_id().clone(), embed_key.clone()))
                                        .and_modify(|i| *i += 1)
                                        .or_insert(1),
                                ),
                                version: 0,
                                stack: self.stack.clone(),
                            };
                            self.statement_buffer
                                .push(TypedStatement::MultipleDefinition(
                                    vec![Variable::with_id_and_type(id.clone(), tys[0].clone())],
                                    TypedExpressionList::FunctionCall(
                                        embed_key.clone().into(),
                                        expressions.clone(),
                                        tys,
                                    ),
                                ));

                            let out = UExpressionInner::Identifier(id);

                            // self.call_cache_mut()
                            //     .entry(embed_key.clone().into())
                            //     .or_insert_with(|| HashMap::new())
                            //     .insert(expressions, vec![out.clone().annotate(size).into()]);

                            out
                        }
                        InlineError::NonConstant(key, expressions) => {
                            UExpressionInner::FunctionCall(key, expressions)
                        }
                    },
                }
            }
            // default
            e => fold_uint_expression_inner(self, size, e),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;
    use typed_absy::types::{DeclarationFunctionKey, DeclarationSignature};
    use zokrates_field::Bn128Field;

    #[test]
    fn call_other_module_without_variables() {
        // // main
        // from "foo" import foo
        // def main() -> field:
        //    return foo()
        //
        // // foo
        // def foo() -> field:
        //    return 42
        //
        //
        // // inlined
        // def main() -> field:
        //    // CALL foo
        //    // POP
        //    return 42

        let main = TypedModule {
            functions: vec![
                (
                    DeclarationFunctionKey::with_id("main").signature(
                        DeclarationSignature::new().outputs(vec![DeclarationType::FieldElement]),
                    ),
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
                        signature: DeclarationSignature::new()
                            .outputs(vec![DeclarationType::FieldElement]),
                    }),
                ),
                (
                    DeclarationFunctionKey::with_id("foo").signature(
                        DeclarationSignature::new().outputs(vec![DeclarationType::FieldElement]),
                    ),
                    TypedFunctionSymbol::There(
                        DeclarationFunctionKey::with_id("foo").signature(
                            DeclarationSignature::new()
                                .outputs(vec![DeclarationType::FieldElement]),
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
                DeclarationFunctionKey::with_id("foo").signature(
                    DeclarationSignature::new().outputs(vec![DeclarationType::FieldElement]),
                ),
                TypedFunctionSymbol::Here(TypedFunction {
                    arguments: vec![],
                    statements: vec![TypedStatement::Return(vec![
                        FieldElementExpression::Number(Bn128Field::from(42)).into(),
                    ])],
                    signature: DeclarationSignature::new()
                        .outputs(vec![DeclarationType::FieldElement]),
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

        let program = Inliner::init(program.clone()).inline(program);

        assert_eq!(program.modules.len(), 1);
        assert_eq!(
            program
                .modules
                .get(&PathBuf::from("main"))
                .unwrap()
                .functions
                .get(&DeclarationFunctionKey::with_id("main").signature(
                    DeclarationSignature::new().outputs(vec![DeclarationType::FieldElement])
                ))
                .unwrap(),
            &TypedFunctionSymbol::Here(TypedFunction {
                arguments: vec![],
                statements: vec![
                    TypedStatement::PushCallLog(
                        "foo".into(),
                        ConcreteFunctionKey::with_id("foo").signature(
                            ConcreteSignature::new().outputs(vec![ConcreteType::FieldElement]),
                        )
                    ),
                    TypedStatement::PopCallLog,
                    TypedStatement::Return(vec![FieldElementExpression::Number(Bn128Field::from(
                        42
                    ))
                    .into(),])
                ],
                signature: DeclarationSignature::new().outputs(vec![DeclarationType::FieldElement]),
            })
        );
    }

    #[test]
    fn call_other_module_with_variables() {
        // // main
        // from "foo" import foo
        // def main(field a) -> field:
        //    return a * foo(a)
        //
        // // foo
        // def foo(field a) -> field:
        //    return a * a
        //
        //
        // // inlined
        // def main(a) -> field:
        //    // CALL foo
        //    field a_0 = a
        //    // POP
        //    return a * a_0 * a_0

        let main = TypedModule {
            functions: vec![
                (
                    DeclarationFunctionKey::with_id("main").signature(
                        DeclarationSignature::new()
                            .inputs(vec![DeclarationType::FieldElement])
                            .outputs(vec![DeclarationType::FieldElement]),
                    ),
                    TypedFunctionSymbol::Here(TypedFunction {
                        arguments: vec![DeclarationParameter::private(
                            DeclarationVariable::field_element("a"),
                        )],
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
                        signature: DeclarationSignature::new()
                            .inputs(vec![DeclarationType::FieldElement])
                            .outputs(vec![DeclarationType::FieldElement]),
                    }),
                ),
                (
                    DeclarationFunctionKey::with_id("foo").signature(
                        DeclarationSignature::new()
                            .inputs(vec![DeclarationType::FieldElement])
                            .outputs(vec![DeclarationType::FieldElement]),
                    ),
                    TypedFunctionSymbol::There(
                        DeclarationFunctionKey::with_id("foo").signature(
                            DeclarationSignature::new()
                                .inputs(vec![DeclarationType::FieldElement])
                                .outputs(vec![DeclarationType::FieldElement]),
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
                DeclarationFunctionKey::with_id("foo").signature(
                    DeclarationSignature::new()
                        .inputs(vec![DeclarationType::FieldElement])
                        .outputs(vec![DeclarationType::FieldElement]),
                ),
                TypedFunctionSymbol::Here(TypedFunction {
                    arguments: vec![DeclarationParameter::private(
                        DeclarationVariable::field_element("a"),
                    )],
                    statements: vec![TypedStatement::Return(vec![FieldElementExpression::Mult(
                        box FieldElementExpression::Identifier("a".into()),
                        box FieldElementExpression::Identifier("a".into()),
                    )
                    .into()])],
                    signature: DeclarationSignature::new()
                        .inputs(vec![DeclarationType::FieldElement])
                        .outputs(vec![DeclarationType::FieldElement]),
                }),
            )]
            .into_iter()
            .collect(),
        };

        let modules: HashMap<_, _> = vec![("main".into(), main), ("foo".into(), foo)]
            .into_iter()
            .collect();

        let program: TypedProgram<Bn128Field> = TypedProgram {
            main: "main".into(),
            modules,
        };

        let program = Inliner::init(program.clone()).inline(program);

        assert_eq!(program.modules.len(), 1);

        let stack = vec![(
            "foo".into(),
            ConcreteFunctionKey::with_id("foo").signature(
                ConcreteSignature::new()
                    .inputs(vec![ConcreteType::FieldElement])
                    .outputs(vec![ConcreteType::FieldElement]),
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
                    &DeclarationFunctionKey::with_id("main").signature(
                        DeclarationSignature::new()
                            .inputs(vec![DeclarationType::FieldElement])
                            .outputs(vec![DeclarationType::FieldElement])
                    )
                )
                .unwrap(),
            &TypedFunctionSymbol::Here(TypedFunction {
                arguments: vec![DeclarationParameter::private(
                    DeclarationVariable::field_element("a")
                )],
                statements: vec![
                    TypedStatement::PushCallLog(
                        "foo".into(),
                        ConcreteFunctionKey::with_id("foo").signature(
                            ConcreteSignature::new()
                                .inputs(vec![ConcreteType::FieldElement])
                                .outputs(vec![ConcreteType::FieldElement]),
                        )
                    ),
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::field_element(
                            Identifier::from("a").stack(stack.clone())
                        )),
                        FieldElementExpression::Identifier("a".into()).into()
                    ),
                    TypedStatement::PopCallLog,
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
                signature: DeclarationSignature::new()
                    .inputs(vec![DeclarationType::FieldElement])
                    .outputs(vec![DeclarationType::FieldElement]),
            })
        );
    }

    #[test]
    fn memoize_local_call() {
        // // foo
        // def foo(field a) -> field:
        //     return a

        // // main
        // def main(field a) -> field:
        //     field b = foo(a) + foo(a)
        //     return b

        // inlined
        // def main(field a) -> field
        //     field foo_0_a = a
        //     field b = foo_0_a + foo_0_a
        //     return b

        let signature = ConcreteSignature::new()
            .outputs(vec![ConcreteType::FieldElement])
            .inputs(vec![ConcreteType::FieldElement]);

        let main: TypedModule<Bn128Field> = TypedModule {
            functions: vec![
                (
                    DeclarationFunctionKey::with_id("main").signature(signature.clone().into()),
                    TypedFunctionSymbol::Here(TypedFunction {
                        arguments: vec![DeclarationParameter {
                            id: DeclarationVariable::field_element("a"),
                            private: true,
                        }],
                        statements: vec![
                            TypedStatement::Definition(
                                TypedAssignee::Identifier(Variable::field_element("b")),
                                FieldElementExpression::Add(
                                    box FieldElementExpression::FunctionCall(
                                        FunctionKey::with_id("foo")
                                            .signature(signature.clone().into()),
                                        vec![FieldElementExpression::Identifier("a".into()).into()],
                                    ),
                                    box FieldElementExpression::FunctionCall(
                                        FunctionKey::with_id("foo")
                                            .signature(signature.clone().into()),
                                        vec![FieldElementExpression::Identifier("a".into()).into()],
                                    ),
                                )
                                .into(),
                            ),
                            TypedStatement::Return(vec![FieldElementExpression::Identifier(
                                "b".into(),
                            )
                            .into()]),
                        ],
                        signature: signature.clone().into(),
                    }),
                ),
                (
                    DeclarationFunctionKey::with_id("foo").signature(signature.clone().into()),
                    TypedFunctionSymbol::There(
                        DeclarationFunctionKey::with_id("foo").signature(signature.clone().into()),
                        "foo".into(),
                    ),
                ),
            ]
            .into_iter()
            .collect(),
        };

        let foo: TypedModule<Bn128Field> = TypedModule {
            functions: vec![(
                DeclarationFunctionKey::with_id("foo").signature(signature.clone().into()),
                TypedFunctionSymbol::Here(TypedFunction {
                    arguments: vec![DeclarationParameter {
                        id: DeclarationVariable::field_element("a"),
                        private: true,
                    }],
                    statements: vec![TypedStatement::Return(vec![
                        FieldElementExpression::Identifier("a".into()).into(),
                    ])],
                    signature: signature.clone().into(),
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

        let program = Inliner::init(program.clone()).inline(program);

        assert_eq!(program.modules.len(), 1);
        assert_eq!(
            program
                .modules
                .get(&PathBuf::from("main"))
                .unwrap()
                .functions
                .get(&DeclarationFunctionKey::with_id("main").signature(signature.clone().into()))
                .unwrap(),
            &TypedFunctionSymbol::Here(TypedFunction {
                arguments: vec![DeclarationParameter {
                    id: DeclarationVariable::field_element("a"),
                    private: true,
                }],
                statements: vec![
                    TypedStatement::PushCallLog(
                        "foo".into(),
                        ConcreteFunctionKey::with_id("foo").signature(
                            ConcreteSignature::new()
                                .inputs(vec![ConcreteType::FieldElement])
                                .outputs(vec![ConcreteType::FieldElement]),
                        )
                    ),
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::field_element(
                            Identifier::from("a").stack(vec![(
                                "foo".into(),
                                ConcreteFunctionKey::with_id("foo").signature(signature.clone()),
                                1
                            )])
                        )),
                        FieldElementExpression::Identifier("a".into()).into()
                    ),
                    TypedStatement::PopCallLog,
                    TypedStatement::PushCallLog(
                        "foo".into(),
                        ConcreteFunctionKey::with_id("foo").signature(
                            ConcreteSignature::new()
                                .inputs(vec![ConcreteType::FieldElement])
                                .outputs(vec![ConcreteType::FieldElement]),
                        )
                    ),
                    TypedStatement::PopCallLog,
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::field_element("b")),
                        FieldElementExpression::Add(
                            box FieldElementExpression::Identifier(Identifier::from("a").stack(
                                vec![(
                                    "foo".into(),
                                    ConcreteFunctionKey::with_id("foo")
                                        .signature(signature.clone()),
                                    1
                                )]
                            )),
                            box FieldElementExpression::Identifier(Identifier::from("a").stack(
                                vec![(
                                    "foo".into(),
                                    ConcreteFunctionKey::with_id("foo")
                                        .signature(signature.clone()),
                                    1
                                )]
                            ))
                        )
                        .into()
                    ),
                    TypedStatement::Return(vec![
                        FieldElementExpression::Identifier("b".into()).into(),
                    ])
                ],
                signature: signature.clone().into(),
            })
        );
    }

    #[test]
    fn only_memoize_in_same_function() {
        // // foo
        // def foo(field a) -> field:
        //     return a

        // // main
        // def main(field a) -> field:
        //     field b = foo(a) + bar(a)
        //     return b
        //
        // def bar(field a) -> field:
        //     return foo(a)

        // inlined
        // def main(field a) -> field
        //     field _0 = a + a
        //     return _0

        let signature = ConcreteSignature::new()
            .outputs(vec![ConcreteType::FieldElement])
            .inputs(vec![ConcreteType::FieldElement]);

        let main: TypedModule<Bn128Field> = TypedModule {
            functions: vec![
                (
                    DeclarationFunctionKey::with_id("main").signature(signature.clone().into()),
                    TypedFunctionSymbol::Here(TypedFunction {
                        arguments: vec![DeclarationParameter {
                            id: DeclarationVariable::field_element("a"),
                            private: true,
                        }],
                        statements: vec![
                            TypedStatement::Definition(
                                TypedAssignee::Identifier(Variable::field_element("b")),
                                FieldElementExpression::Add(
                                    box FieldElementExpression::FunctionCall(
                                        FunctionKey::with_id("foo")
                                            .signature(signature.clone().into()),
                                        vec![FieldElementExpression::Identifier("a".into()).into()],
                                    ),
                                    box FieldElementExpression::FunctionCall(
                                        FunctionKey::with_id("bar")
                                            .signature(signature.clone().into()),
                                        vec![FieldElementExpression::Identifier("a".into()).into()],
                                    ),
                                )
                                .into(),
                            ),
                            TypedStatement::Return(vec![FieldElementExpression::Identifier(
                                "b".into(),
                            )
                            .into()]),
                        ],
                        signature: signature.clone().into(),
                    }),
                ),
                (
                    DeclarationFunctionKey::with_id("bar").signature(signature.clone().into()),
                    TypedFunctionSymbol::Here(TypedFunction {
                        arguments: vec![DeclarationParameter {
                            id: DeclarationVariable::field_element("a"),
                            private: true,
                        }],
                        statements: vec![TypedStatement::Return(vec![
                            FieldElementExpression::FunctionCall(
                                FunctionKey::with_id("foo").signature(signature.clone().into()),
                                vec![FieldElementExpression::Identifier("a".into()).into()],
                            )
                            .into(),
                        ])],
                        signature: signature.clone().into(),
                    }),
                ),
                (
                    DeclarationFunctionKey::with_id("foo").signature(signature.clone().into()),
                    TypedFunctionSymbol::There(
                        DeclarationFunctionKey::with_id("foo").signature(signature.clone().into()),
                        "foo".into(),
                    ),
                ),
            ]
            .into_iter()
            .collect(),
        };

        let foo: TypedModule<Bn128Field> = TypedModule {
            functions: vec![(
                DeclarationFunctionKey::with_id("foo").signature(signature.clone().into()),
                TypedFunctionSymbol::Here(TypedFunction {
                    arguments: vec![DeclarationParameter {
                        id: DeclarationVariable::field_element("a"),
                        private: true,
                    }],
                    statements: vec![TypedStatement::Return(vec![
                        FieldElementExpression::Identifier("a".into()).into(),
                    ])],
                    signature: signature.clone().into(),
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

        let program = Inliner::init(program.clone()).inline(program);

        assert_eq!(program.modules.len(), 1);
        assert_eq!(
            program
                .modules
                .get(&PathBuf::from("main"))
                .unwrap()
                .functions
                .get(&DeclarationFunctionKey::with_id("main").signature(signature.clone().into()))
                .unwrap(),
            &TypedFunctionSymbol::Here(TypedFunction {
                arguments: vec![DeclarationParameter {
                    id: DeclarationVariable::field_element("a"),
                    private: true,
                }],
                statements: vec![
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::field_element(
                            Identifier::from("a").stack(vec![(
                                "foo".into(),
                                ConcreteFunctionKey::with_id("foo").signature(signature.clone()),
                                1
                            )])
                        )),
                        FieldElementExpression::Identifier("a".into()).into()
                    ),
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::field_element(
                            Identifier::from("a").stack(vec![(
                                "main".into(),
                                ConcreteFunctionKey::with_id("bar").signature(signature.clone()),
                                1
                            )])
                        )),
                        FieldElementExpression::Identifier("a".into()).into()
                    ),
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::field_element(
                            Identifier::from("a").stack(vec![
                                (
                                    "main".into(),
                                    ConcreteFunctionKey::with_id("bar")
                                        .signature(signature.clone()),
                                    1
                                ),
                                (
                                    "foo".into(),
                                    ConcreteFunctionKey::with_id("foo")
                                        .signature(signature.clone()),
                                    2
                                )
                            ])
                        )),
                        FieldElementExpression::Identifier(Identifier::from("a").stack(vec![(
                            "main".into(),
                            ConcreteFunctionKey::with_id("bar").signature(signature.clone()),
                            1
                        )]))
                        .into()
                    ),
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::field_element("b")),
                        FieldElementExpression::Add(
                            box FieldElementExpression::Identifier(Identifier::from("a").stack(
                                vec![(
                                    "foo".into(),
                                    ConcreteFunctionKey::with_id("foo")
                                        .signature(signature.clone()),
                                    1
                                )]
                            )),
                            box FieldElementExpression::Identifier(Identifier::from("a").stack(
                                vec![
                                    (
                                        "main".into(),
                                        ConcreteFunctionKey::with_id("bar")
                                            .signature(signature.clone()),
                                        1
                                    ),
                                    (
                                        "foo".into(),
                                        ConcreteFunctionKey::with_id("foo")
                                            .signature(signature.clone()),
                                        2
                                    )
                                ]
                            ))
                        )
                        .into()
                    ),
                    TypedStatement::Return(vec![
                        FieldElementExpression::Identifier("b".into()).into(),
                    ])
                ],
                signature: signature.clone().into(),
            })
        );
    }

    #[test]
    fn multi_def_from_other_module() {
        // // foo
        // def foo() -> field:
        //     return 42

        // // main
        // def main() -> field:
        //     field a = foo()
        //     return a

        // inlined
        // def main() -> field
        //     // CALL foo
        //     // POP
        //     field a = 42
        //     return a

        let main = TypedModule {
            functions: vec![
                (
                    DeclarationFunctionKey::with_id("main").signature(
                        DeclarationSignature::new().outputs(vec![DeclarationType::FieldElement]),
                    ),
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
                                "a".into(),
                            )
                            .into()]),
                        ],
                        signature: DeclarationSignature::new()
                            .outputs(vec![DeclarationType::FieldElement]),
                    }),
                ),
                (
                    DeclarationFunctionKey::with_id("foo").signature(
                        DeclarationSignature::new().outputs(vec![DeclarationType::FieldElement]),
                    ),
                    TypedFunctionSymbol::There(
                        DeclarationFunctionKey::with_id("foo").signature(
                            DeclarationSignature::new()
                                .outputs(vec![DeclarationType::FieldElement]),
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
                DeclarationFunctionKey::with_id("foo").signature(
                    DeclarationSignature::new().outputs(vec![DeclarationType::FieldElement]),
                ),
                TypedFunctionSymbol::Here(TypedFunction {
                    arguments: vec![],
                    statements: vec![TypedStatement::Return(vec![
                        FieldElementExpression::Number(Bn128Field::from(42)).into(),
                    ])],
                    signature: DeclarationSignature::new()
                        .outputs(vec![DeclarationType::FieldElement]),
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

        let program = Inliner::init(program.clone()).inline(program);

        assert_eq!(program.modules.len(), 1);
        assert_eq!(
            program
                .modules
                .get(&PathBuf::from("main"))
                .unwrap()
                .functions
                .get(&DeclarationFunctionKey::with_id("main").signature(
                    DeclarationSignature::new().outputs(vec![DeclarationType::FieldElement])
                ))
                .unwrap(),
            &TypedFunctionSymbol::Here(TypedFunction {
                arguments: vec![],
                statements: vec![
                    TypedStatement::PushCallLog(
                        "foo".into(),
                        ConcreteFunctionKey::with_id("foo").signature(
                            ConcreteSignature::new().outputs(vec![ConcreteType::FieldElement]),
                        )
                    ),
                    TypedStatement::PopCallLog,
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::field_element("a")),
                        FieldElementExpression::Number(Bn128Field::from(42)).into()
                    ),
                    TypedStatement::Return(vec![
                        FieldElementExpression::Identifier("a".into()).into(),
                    ])
                ],
                signature: DeclarationSignature::new().outputs(vec![DeclarationType::FieldElement]),
            })
        );
    }

    #[test]
    fn multi_def_from_same_module() {
        // // main
        // def foo() -> field:
        //     return 42
        // def main() -> field:
        //     field a = foo()
        //     return a

        // inlined
        // def main() -> field
        //     field _0 = 42
        //     return _0

        let main = TypedModule {
            functions: vec![
                (
                    DeclarationFunctionKey::with_id("main").signature(
                        DeclarationSignature::new().outputs(vec![DeclarationType::FieldElement]),
                    ),
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
                                "a".into(),
                            )
                            .into()]),
                        ],
                        signature: DeclarationSignature::new()
                            .outputs(vec![DeclarationType::FieldElement]),
                    }),
                ),
                (
                    DeclarationFunctionKey::with_id("foo").signature(
                        DeclarationSignature::new().outputs(vec![DeclarationType::FieldElement]),
                    ),
                    TypedFunctionSymbol::Here(TypedFunction {
                        arguments: vec![],
                        statements: vec![TypedStatement::Return(vec![
                            FieldElementExpression::Number(Bn128Field::from(42)).into(),
                        ])],
                        signature: DeclarationSignature::new()
                            .outputs(vec![DeclarationType::FieldElement]),
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

        let program = Inliner::init(program.clone()).inline(program);

        assert_eq!(program.modules.len(), 1);
        assert_eq!(
            program
                .modules
                .get(&PathBuf::from("main"))
                .unwrap()
                .functions
                .get(&DeclarationFunctionKey::with_id("main").signature(
                    DeclarationSignature::new().outputs(vec![DeclarationType::FieldElement])
                ))
                .unwrap(),
            &TypedFunctionSymbol::Here(TypedFunction {
                arguments: vec![],
                statements: vec![
                    TypedStatement::PushCallLog(
                        "main".into(),
                        ConcreteFunctionKey::with_id("foo").signature(
                            ConcreteSignature::new().outputs(vec![ConcreteType::FieldElement]),
                        )
                    ),
                    TypedStatement::PopCallLog,
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::field_element("a")),
                        FieldElementExpression::Number(Bn128Field::from(42)).into()
                    ),
                    TypedStatement::Return(vec![
                        FieldElementExpression::Identifier("a".into()).into(),
                    ])
                ],
                signature: DeclarationSignature::new().outputs(vec![DeclarationType::FieldElement]),
            })
        );
    }

    #[test]
    fn recursive_call_in_other_module() {
        // // main
        // def main(field a) -> field:
        //     return id(id(a))

        // // id
        // def main(field a) -> field
        //     return a

        // inlined
        // def main(field a) -> field
        //     // CALL id
        //     id_main_0_a = a
        //     // CALL id
        //     id_main_1_a = id_main_0_a
        //     // POP
        //     // POP
        //     return id_main_1_a

        let main = TypedModule {
            functions: vec![
                (
                    DeclarationFunctionKey::with_id("main").signature(
                        DeclarationSignature::new()
                            .inputs(vec![DeclarationType::FieldElement])
                            .outputs(vec![DeclarationType::FieldElement]),
                    ),
                    TypedFunctionSymbol::Here(TypedFunction {
                        arguments: vec![DeclarationParameter::private(
                            DeclarationVariable::field_element("a"),
                        )],
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
                        signature: DeclarationSignature::new()
                            .inputs(vec![DeclarationType::FieldElement])
                            .outputs(vec![DeclarationType::FieldElement]),
                    }),
                ),
                (
                    DeclarationFunctionKey::with_id("id").signature(
                        DeclarationSignature::new()
                            .inputs(vec![DeclarationType::FieldElement])
                            .outputs(vec![DeclarationType::FieldElement]),
                    ),
                    TypedFunctionSymbol::There(
                        DeclarationFunctionKey::with_id("main").signature(
                            DeclarationSignature::new()
                                .inputs(vec![DeclarationType::FieldElement])
                                .outputs(vec![DeclarationType::FieldElement]),
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
                DeclarationFunctionKey::with_id("main").signature(
                    DeclarationSignature::new()
                        .inputs(vec![DeclarationType::FieldElement])
                        .outputs(vec![DeclarationType::FieldElement]),
                ),
                TypedFunctionSymbol::Here(TypedFunction {
                    arguments: vec![DeclarationParameter::private(
                        DeclarationVariable::field_element("a"),
                    )],
                    statements: vec![TypedStatement::Return(vec![
                        FieldElementExpression::Identifier("a".into()).into(),
                    ])],
                    signature: DeclarationSignature::new()
                        .inputs(vec![DeclarationType::FieldElement])
                        .outputs(vec![DeclarationType::FieldElement]),
                }),
            )]
            .into_iter()
            .collect(),
        };

        let modules = vec![("main".into(), main), ("id".into(), id)]
            .into_iter()
            .collect();

        let program: TypedProgram<Bn128Field> = TypedProgram {
            main: "main".into(),
            modules,
        };

        let program = Inliner::init(program.clone()).inline(program);

        let stack0 = vec![(
            "id".into(),
            ConcreteFunctionKey::with_id("main").signature(
                ConcreteSignature::new()
                    .inputs(vec![ConcreteType::FieldElement])
                    .outputs(vec![ConcreteType::FieldElement]),
            ),
            1,
        )];
        let stack1 = vec![(
            "id".into(),
            ConcreteFunctionKey::with_id("main").signature(
                ConcreteSignature::new()
                    .inputs(vec![ConcreteType::FieldElement])
                    .outputs(vec![ConcreteType::FieldElement]),
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
                    &DeclarationFunctionKey::with_id("main").signature(
                        DeclarationSignature::new()
                            .inputs(vec![DeclarationType::FieldElement])
                            .outputs(vec![DeclarationType::FieldElement])
                    )
                )
                .unwrap(),
            &TypedFunctionSymbol::Here(TypedFunction {
                arguments: vec![DeclarationParameter::private(
                    DeclarationVariable::field_element("a")
                )],
                statements: vec![
                    TypedStatement::PushCallLog(
                        "id".into(),
                        ConcreteFunctionKey::with_id("main").signature(
                            ConcreteSignature::new()
                                .inputs(vec![ConcreteType::FieldElement])
                                .outputs(vec![ConcreteType::FieldElement]),
                        )
                    ),
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::field_element(
                            Identifier::from("a").stack(stack0.clone())
                        )),
                        FieldElementExpression::Identifier("a".into()).into()
                    ),
                    TypedStatement::PopCallLog,
                    TypedStatement::PushCallLog(
                        "id".into(),
                        ConcreteFunctionKey::with_id("main").signature(
                            ConcreteSignature::new()
                                .inputs(vec![ConcreteType::FieldElement])
                                .outputs(vec![ConcreteType::FieldElement]),
                        )
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
                    TypedStatement::PopCallLog,
                    TypedStatement::Return(vec![FieldElementExpression::Identifier(
                        Identifier::from("a").stack(stack1.clone())
                    )
                    .into(),])
                ],
                signature: DeclarationSignature::new()
                    .inputs(vec![DeclarationType::FieldElement])
                    .outputs(vec![DeclarationType::FieldElement]),
            })
        );
    }
}
