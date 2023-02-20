// The reducer reduces the program to a single function which is:
// - in SSA form
// - free of function calls (except for low level calls) thanks to inlining
// - free of for-loops thanks to unrolling

// The process happens in two steps
// 1. Shallow SSA for the `main` function
// We turn the `main` function into SSA form, but ignoring function calls and for loops
// 2. Unroll and inline
// We go through the shallow-SSA program and
// - unroll loops
// - inline function calls. This includes applying shallow-ssa on the target function

mod constants_reader;
mod constants_writer;
mod inline;
mod shallow_ssa;

use self::inline::{inline_call, InlineError};
use std::collections::HashMap;
use zokrates_ast::typed::identifier::FrameIdentifier;
use zokrates_ast::typed::result_folder::*;
use zokrates_ast::typed::types::ConcreteGenericsAssignment;
use zokrates_ast::typed::types::GGenericsAssignment;
use zokrates_ast::typed::DeclarationParameter;
use zokrates_ast::typed::Folder;
use zokrates_ast::typed::Typed;
use zokrates_ast::typed::TypedAssignee;
use zokrates_ast::typed::{CanonicalConstantIdentifier, EmbedCall, Variable};

use zokrates_ast::typed::{
    ArrayExpressionInner, ArrayType, BlockExpression, CoreIdentifier, Expr, FunctionCall,
    FunctionCallExpression, FunctionCallOrExpression, Id, Identifier, OwnedTypedModuleId,
    TypedExpression, TypedFunction, TypedFunctionSymbol, TypedFunctionSymbolDeclaration,
    TypedModule, TypedProgram, TypedStatement, UExpression, UExpressionInner,
};

use zokrates_ast::zir::result_folder::fold_assembly_statement;
use zokrates_field::Field;

use self::constants_writer::ConstantsWriter;
use self::shallow_ssa::ShallowTransformer;

use crate::propagation::{Constants, Propagator};

use std::fmt;

const MAX_FOR_LOOP_SIZE: u128 = 2u128.pow(20);

// A map to register the canonical value of all constants. The values must be literals.
pub type ConstantDefinitions<'ast, T> =
    HashMap<CanonicalConstantIdentifier<'ast>, TypedExpression<'ast, T>>;

// An SSA version map, giving access to the latest version number for each identifier
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Versions<'ast> {
    map: HashMap<usize, HashMap<CoreIdentifier<'ast>, usize>>,
    frame: usize,
}

impl<'ast> Versions<'ast> {
    fn insert_in_frame(
        &mut self,
        id: CoreIdentifier<'ast>,
        version: usize,
        frame: usize,
    ) -> Option<usize> {
        self.map.entry(frame).or_default().insert(id, version)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    Incompatible(String),
    GenericsInMain,
    // TODO: give more details about what's blocking the progress
    NoProgress,
    LoopTooLarge(u128),
    ConstantReduction(String, OwnedTypedModuleId),
    Type(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Incompatible(s) => write!(
                f,
                "{}",
                s
            ),
            Error::GenericsInMain => write!(f, "Cannot generate code for generic function"),
            Error::NoProgress => write!(f, "Failed to unroll or inline program. Check that main function arguments aren't used as array size or for-loop bounds"),
            Error::LoopTooLarge(size) => write!(f, "Found a loop of size {}, which is larger than the maximum allowed of {}. Check the loop bounds, especially for underflows", size, MAX_FOR_LOOP_SIZE),
            Error::ConstantReduction(name, module) => write!(f, "Failed to reduce constant `{}` in module `{}` to a literal, try simplifying its declaration", name, module.display()),
            Error::Type(message) => write!(f, "{}", message),
        }
    }
}

#[derive(Debug)]
struct Reducer<'ast, 'a, T> {
    propagator: Propagator<'ast, 'a, T>,
    statement_buffer: Vec<TypedStatement<'ast, T>>,
    latest_frame: usize,
    versions: &'a mut Versions<'ast>,
    program: &'a TypedProgram<'ast, T>,
}

impl<'ast, 'a, T: Field> Reducer<'ast, 'a, T> {
    fn new(
        program: &'a TypedProgram<'ast, T>,
        versions: &'a mut Versions<'ast>,
        constants: &'a mut Constants<'ast, T>,
    ) -> Self {
        // println!("create reducer with");
        // println!("{} versions", versions.len());
        // println!("{} constants", constants.len());

        Reducer {
            propagator: Propagator::with_constants(constants),
            statement_buffer: vec![],
            latest_frame: 0,
            program,
            versions,
        }
    }
}

impl<'ast, 'a, T: Field> ResultFolder<'ast, T> for Reducer<'ast, 'a, T> {
    type Error = Error;

    fn fold_parameter(
        &mut self,
        p: DeclarationParameter<'ast, T>,
    ) -> Result<DeclarationParameter<'ast, T>, Self::Error> {
        let id = p.id.id.id.id.clone();
        assert!(self.versions.insert_in_frame(id, 0, 0).is_none());
        Ok(p)
    }

    fn fold_function_call_expression<
        E: Id<'ast, T> + From<TypedExpression<'ast, T>> + Expr<'ast, T> + FunctionCall<'ast, T>,
    >(
        &mut self,
        ty: &E::Ty,
        e: FunctionCallExpression<'ast, T, E>,
    ) -> Result<FunctionCallOrExpression<'ast, T, E>, Self::Error> {
        let generics = e
            .generics
            .into_iter()
            .map(|g| {
                g.map(|g| {
                    let g =
                        ShallowTransformer::with_versions(self.versions).fold_uint_expression(g);
                    let g = self.propagator.fold_uint_expression(g).unwrap();

                    self.fold_uint_expression(g)
                })
                .transpose()
            })
            .collect::<Result<_, _>>()?;

        let arguments = e
            .arguments
            .into_iter()
            .map(|e| {
                let e = ShallowTransformer::with_versions(self.versions).fold_expression(e);
                let e = self.propagator.fold_expression(e).unwrap();

                self.fold_expression(e)
            })
            .collect::<Result<_, _>>()?;

        // back up the current frame
        let frame_backup = self.versions.frame;

        // create a new frame
        self.latest_frame += 1;

        // point the versions to this frame
        self.versions.frame = self.latest_frame;
        self.versions
            .map
            .insert(self.versions.frame, Default::default());

        // println!("GENERICS {:?}", generics);

        let res = inline_call::<_, E>(&e.function_key, generics, arguments, ty, self.program);

        let res = match res {
            Ok((input_variables, arguments, generics_bindings, statements, expression)) => {
                let generics_bindings: Vec<_> = generics_bindings
                    .into_iter()
                    .flat_map(|s| {
                        ShallowTransformer::with_versions(self.versions).fold_statement(s)
                    })
                    .flat_map(|s| self.propagator.fold_statement(s).unwrap())
                    .collect::<Vec<_>>()
                    .into_iter()
                    .flat_map(|s| self.fold_statement(s).unwrap())
                    .collect();

                // println!("{:#?}", propagator);

                self.statement_buffer.extend(generics_bindings);

                // the lhs is from the inner call frame, the rhs is from the outer one, so only fld the lhs
                let input_bindings: Vec<_> = input_variables
                    .into_iter()
                    .zip(arguments)
                    .map(|(v, a)| {
                        TypedStatement::definition(
                            ShallowTransformer::with_versions(self.versions)
                                .fold_assignee(v.into()),
                            a,
                        )
                    })
                    .collect();

                let input_bindings: Vec<_> = input_bindings
                    .into_iter()
                    .flat_map(|s| self.propagator.fold_statement(s).unwrap())
                    .collect();

                self.statement_buffer.extend(input_bindings);

                let statements: Vec<_> = statements
                    .into_iter()
                    .flat_map(|s| self.fold_statement(s).unwrap())
                    .collect();

                // println!("FRAME READY TO SSA {}", self.versions.frame);

                let mut transformer = ShallowTransformer::with_versions(self.versions);
                let propagator = &mut self.propagator;

                self.statement_buffer.extend(statements);

                // println!("call result {}", expression);

                let expression = transformer.fold_expression(expression);

                let expression = propagator.fold_expression(expression).unwrap();

                let expression = self.fold_expression(expression).unwrap();

                // println!("call result reduced {}", expression);

                Ok(FunctionCallOrExpression::Expression(
                    E::from(expression).into_inner(),
                ))
            }
            Err(InlineError::Generic(decl, conc)) => Err(Error::Incompatible(format!(
                "Call site `{}` incompatible with declaration `{}`",
                conc, decl
            ))),
            Err(InlineError::NonConstant(key, generics, arguments, _)) => Err(Error::NoProgress),
            Err(InlineError::Flat(embed, generics, arguments, output_type)) => {
                let identifier =
                    Identifier::from(CoreIdentifier::Call(0).in_frame(self.versions.frame))
                        .version(
                            *self
                                .versions
                                .map
                                .entry(self.versions.frame)
                                .or_default()
                                .entry(CoreIdentifier::Call(0))
                                .and_modify(|e| *e += 1) // if it was already declared, we increment
                                .or_insert(0),
                        );

                let var = Variable::immutable(identifier.clone(), output_type);

                let v: TypedAssignee<'ast, T> = var.clone().into();

                self.statement_buffer
                    .push(TypedStatement::embed_call_definition(
                        v,
                        EmbedCall::new(embed, generics, arguments),
                    ));
                Ok(FunctionCallOrExpression::Expression(E::identifier(
                    identifier,
                )))
            }
        };

        // clean versions
        self.versions.map.remove(&self.versions.frame);

        // restore the original frame
        // println!("RESTORING BACKUP {}", frame_backup);
        self.versions.frame = frame_backup;

        res
    }

    fn fold_block_expression<E: ResultFold<'ast, T>>(
        &mut self,
        b: BlockExpression<'ast, T, E>,
    ) -> Result<BlockExpression<'ast, T, E>, Self::Error> {
        // // backup the statements and continue with a fresh state
        // let statement_buffer = std::mem::take(&mut self.statement_buffer);

        // let block = fold_block_expression(self, b)?;

        // // put the original statements back and extract the statements created by visiting the block
        // let extra_statements = std::mem::replace(&mut self.statement_buffer, statement_buffer);

        // // return the visited block, augmented with the statements created while visiting it
        // Ok(BlockExpression {
        //     statements: block
        //         .statements
        //         .into_iter()
        //         .chain(extra_statements)
        //         .collect(),
        //     ..block
        // })
        todo!()
    }

    fn fold_canonical_constant_identifier(
        &mut self,
        _: CanonicalConstantIdentifier<'ast>,
    ) -> Result<CanonicalConstantIdentifier<'ast>, Self::Error> {
        unreachable!("canonical constant identifiers should not be folded, they should be inlined")
    }

    fn fold_statement(
        &mut self,
        s: TypedStatement<'ast, T>,
    ) -> Result<Vec<TypedStatement<'ast, T>>, Self::Error> {
        let res = match s {
            TypedStatement::Definition(a, rhs) => {
                // usually we transform and then propagate
                // for definitions we need special treatment: we transform and propagate the rhs (which can contain function calls)
                // then we reduce the rhs to remove the function calls
                // only then we transform and propagate the assignee

                let mut transformer = ShallowTransformer::with_versions(self.versions);
                // println!("rhs {}", rhs);
                let rhs = transformer.fold_definition_rhs(rhs);
                // println!("ssa-ed {}", rhs);
                let rhs = self.propagator.fold_definition_rhs(rhs).unwrap();
                // println!("propagated {}", rhs);
                let rhs = self.fold_definition_rhs(rhs).unwrap();
                // println!("reduced {}", rhs);

                // println!("ASSIGNEE {}", a);

                // println!("{:?}", self.versions);

                let a = ShallowTransformer::with_versions(self.versions).fold_assignee(a);

                // println!("{:?}", self.versions);

                // println!("definition before propagation {}", TypedStatement::Definition(a.clone(), rhs.clone()));

                self.propagator
                    .fold_statement(TypedStatement::Definition(a, rhs))
                    .unwrap()

                // println!("final definition size: {}", s.len());
            }
            TypedStatement::For(v, from, to, statements) => {
                let from =
                    ShallowTransformer::with_versions(self.versions).fold_uint_expression(from);
                let from = self.propagator.fold_uint_expression(from).unwrap();
                let from = self.fold_uint_expression(from).unwrap();
                let to = ShallowTransformer::with_versions(self.versions).fold_uint_expression(to);
                let to = self.propagator.fold_uint_expression(to).unwrap();
                let to = self.fold_uint_expression(to).unwrap();

                match (from.as_inner(), to.as_inner()) {
                    (UExpressionInner::Value(from), UExpressionInner::Value(to)) => (*from..*to)
                        .flat_map(|index| {
                            std::iter::once(TypedStatement::definition(
                                v.clone().into(),
                                UExpression::from(index as u32).into(),
                            ))
                            .chain(statements.clone())
                            .flat_map(|s| self.fold_statement(s).unwrap())
                            .collect::<Vec<_>>()
                        })
                        .collect::<Vec<_>>(),
                    _ => unimplemented!(),
                }
            }
            TypedStatement::Assembly(_) => todo!(),
            TypedStatement::Return(e) => {
                let mut transformer = ShallowTransformer::with_versions(self.versions);

                let e = transformer.fold_expression(e);
                let e = self.propagator.fold_expression(e).unwrap();
                vec![TypedStatement::Return(self.fold_expression(e).unwrap())]
            }
            TypedStatement::Assertion(e, error) => {
                let mut transformer = ShallowTransformer::with_versions(self.versions);

                let e = transformer.fold_boolean_expression(e);
                let e = self.propagator.fold_boolean_expression(e).unwrap();

                vec![TypedStatement::Assertion(
                    self.fold_boolean_expression(e).unwrap(),
                    error,
                )]
            }
            s => {
                let mut transformer = ShallowTransformer::with_versions(self.versions);
                let propagator = &mut self.propagator;
                transformer
                    .fold_statement(s)
                    .into_iter()
                    // .inspect(|s| println!("ssa {}\n", s))
                    .flat_map(|s| propagator.fold_statement(s).unwrap())
                    .collect::<Vec<_>>()
                    .into_iter()
                    .flat_map(|s| fold_statement(self, s).unwrap())
                    // .inspect(|s| println!("propagated {}\n", s))
                    .collect()
            }
        };

        Ok(self
            .statement_buffer
            .drain(..)
            .chain(res)
            .collect::<Vec<_>>())
    }

    // fn fold_statement(
    //     &mut self,
    //     s: TypedStatement<'ast, T>,
    // ) -> Result<Vec<TypedStatement<'ast, T>>, Self::Error> {
    //     let mut transformer = ShallowTransformer::with_versions(self.versions);
    //     let propagator = &mut self.propagator;

    //     println!("FOLD_STATEMENT: {}", s);

    //     let s: Vec<_> = transformer
    //         .fold_statement(s)
    //         .into_iter()
    //         // .inspect(|s| println!("ssa {}\n", s))
    //         .flat_map(|s| propagator.fold_statement(s).unwrap())
    //         // .inspect(|s| println!("propagated {}\n", s))
    //         .collect();

    //     for s in &s {
    //         println!("OUTER: {}", s);
    //     }

    //     let res: Vec<_> = s
    //         .into_iter()
    //         .flat_map(|s| match s {
    //             TypedStatement::For(v, from, to, statements) => {
    //                 match (from.as_inner(), to.as_inner()) {
    //                     (UExpressionInner::Value(from), UExpressionInner::Value(to)) => (*from
    //                         ..*to)
    //                         .flat_map(|index| {
    //                             std::iter::once(TypedStatement::definition(
    //                                 v.clone().into(),
    //                                 UExpression::from(index as u32).into(),
    //                             ))
    //                             .chain(statements.clone())
    //                             .flat_map(|s| self.fold_statement(s).unwrap())
    //                             .collect::<Vec<_>>()
    //                         })
    //                         .collect(),
    //                     _ => unimplemented!(),
    //                 }
    //             }
    //             s => {
    //                 println!("UNROLL/INLINE STATEMENT {}", s);

    //                 let s = fold_statement(self, s).unwrap();

    //                 for s in &self.statement_buffer {
    //                     println!("BUFFER {}", s);
    //                 }

    //                 for s in &s {
    //                     println!("RESULT {}", s);
    //                 }

    //                 self.statement_buffer.drain(..).chain(s).collect::<Vec<_>>()
    //             }
    //         })
    //         .collect();

    //     for s in &res {
    //         // println!("DONE: {}", s);
    //     }

    //     Ok(res)
    // }

    fn fold_array_expression_inner(
        &mut self,
        array_ty: &ArrayType<'ast, T>,
        e: ArrayExpressionInner<'ast, T>,
    ) -> Result<ArrayExpressionInner<'ast, T>, Self::Error> {
        match e {
            ArrayExpressionInner::Slice(box array, box from, box to) => {
                let array =
                    ShallowTransformer::with_versions(self.versions).fold_array_expression(array);
                let array = self.propagator.fold_array_expression(array).unwrap();
                let array = self.fold_array_expression(array).unwrap();
                let from =
                    ShallowTransformer::with_versions(self.versions).fold_uint_expression(from);
                let from = self.propagator.fold_uint_expression(from).unwrap();
                let from = self.fold_uint_expression(from).unwrap();
                let to = ShallowTransformer::with_versions(self.versions).fold_uint_expression(to);
                let to = self.propagator.fold_uint_expression(to).unwrap();
                let to = self.fold_uint_expression(to).unwrap();

                match (from.as_inner(), to.as_inner()) {
                    (UExpressionInner::Value(..), UExpressionInner::Value(..)) => {
                        Ok(ArrayExpressionInner::Slice(box array, box from, box to))
                    }
                    _ => {
                        todo!("non constant slice bounds")
                    }
                }
            }
            _ => fold_array_expression_inner(self, array_ty, e),
        }
    }
}

pub fn reduce_program<T: Field>(p: TypedProgram<T>) -> Result<TypedProgram<T>, Error> {
    // inline all constants and replace them in the program

    let mut constants_writer = ConstantsWriter::with_program(p.clone());

    let p = constants_writer.fold_program(p)?;

    // inline starting from main
    let main_module = p.modules.get(&p.main).unwrap().clone();

    let decl = main_module
        .functions_iter()
        .find(|d| d.key.id == "main")
        .unwrap();

    let main_function = match &decl.symbol {
        TypedFunctionSymbol::Here(f) => f.clone(),
        _ => unreachable!(),
    };

    match main_function.signature.generics.len() {
        0 => {
            let main_function = reduce_function(main_function, &p)?;

            Ok(TypedProgram {
                main: p.main.clone(),
                modules: vec![(
                    p.main.clone(),
                    TypedModule {
                        symbols: vec![TypedFunctionSymbolDeclaration::new(
                            decl.key.clone(),
                            TypedFunctionSymbol::Here(main_function),
                        )
                        .into()],
                    },
                )]
                .into_iter()
                .collect(),
            })
        }
        _ => Err(Error::GenericsInMain),
    }
}

fn reduce_function<'ast, T: Field>(
    f: TypedFunction<'ast, T>,
    program: &TypedProgram<'ast, T>,
) -> Result<TypedFunction<'ast, T>, Error> {
    let mut versions = Versions::default();
    let mut constants = Constants::default();

    assert!(f.signature.generics.is_empty());

    // let f = match ShallowTransformer::transform(f, &generics, &mut versions) {
    //     Output::Complete(f) => Ok(f),
    //     Output::Incomplete(new_f, new_for_loop_versions) => {
    //         let mut for_loop_versions = new_for_loop_versions;

    //         let mut f = Propagator::with_constants(&mut constants)
    //             .fold_function(new_f)
    //             .map_err(|e| Error::Incompatible(format!("{}", e)))?;

    //         let mut substitutions = Substitutions::default();

    //         let mut hash = None;

    //         let mut len = f.statements.len();

    //         // println!("{}", f);

    //         loop {
    //             let mut reducer = Reducer::new(
    //                 program,
    //                 &mut versions,
    //                 &mut substitutions,
    //                 for_loop_versions,
    //                 &mut constants,
    //             );

    //             println!("reduce");

    //             let new_f = TypedFunction {
    //                 statements: f
    //                     .statements
    //                     .into_iter()
    //                     .map(|s| reducer.fold_statement(s))
    //                     .collect::<Result<Vec<_>, _>>()?
    //                     .into_iter()
    //                     .flatten()
    //                     .collect(),
    //                 ..f
    //             };

    //             println!("done");

    //             // println!("after reduction {}", new_f);

    //             println!(
    //                 "count {}, unrolled {} loops",
    //                 new_f.statements.len(),
    //                 reducer.credits
    //             );

    //             assert!(reducer.for_loop_versions.is_empty());

    //             match reducer.complete {
    //                 true => {
    //                     substitutions = substitutions.canonicalize();

    //                     let new_f = Sub::new(&substitutions).fold_function(new_f);

    //                     // println!("after last sub {}", new_f);

    //                     // let new_f = Propagator::with_constants(&mut constants)
    //                     //     .fold_function(new_f)
    //                     //     .map_err(|e| Error::Incompatible(format!("{}", e)))?;

    //                     // println!("after last prop {}", new_f);

    //                     break Ok(new_f);
    //                 }
    //                 false => {
    //                     for_loop_versions = reducer.for_loop_versions_after;

    //                     println!("canonicalize");

    //                     // substitutions = substitutions.canonicalize();

    //                     // let new_f = Sub::new(&substitutions).fold_function(new_f);

    //                     println!("done");
    //                     // println!("after sub {}", new_f);

    //                     println!("propagate");

    //                     // f = Propagator::with_constants(&mut constants)
    //                     //     .fold_function(new_f)
    //                     //     .map_err(|e| Error::Incompatible(format!("{}", e)))?;

    //                     println!("done");

    //                     f = new_f;

    //                     // println!("after prop {}", f);

    //                     let new_len = f.statements.len();

    //                     if new_len == len {
    //                         let new_hash = Some(compute_hash(&f));

    //                         if new_hash == hash {
    //                             break Err(Error::NoProgress);
    //                         } else {
    //                             hash = new_hash;
    //                         }
    //                     } else {
    //                         len = new_len;
    //                     }
    //                 }
    //             }
    //         }
    //     }
    // }?;

    // Propagator::with_constants(&mut constants)
    //     .fold_function(f)
    //     .map_err(|e| Error::Incompatible(format!("{}", e)))

    Reducer::new(program, &mut versions, &mut constants).fold_function(f)
}

fn compute_hash<T: Field>(f: &TypedFunction<T>) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut s = DefaultHasher::new();
    f.hash(&mut s);
    s.finish()
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_ast::typed::types::DeclarationSignature;
    use zokrates_ast::typed::types::{DeclarationConstant, GTupleType};
    use zokrates_ast::typed::{
        ArrayExpression, ArrayExpressionInner, DeclarationFunctionKey, DeclarationType,
        DeclarationVariable, FieldElementExpression, GenericIdentifier, Identifier,
        OwnedTypedModuleId, Select, TupleExpressionInner, TupleType, Type, TypedExpression,
        TypedExpressionOrSpread, UBitwidth, UExpressionInner, Variable,
    };
    use zokrates_field::Bn128Field;

    use lazy_static::lazy_static;

    lazy_static! {
        static ref MAIN_MODULE_ID: OwnedTypedModuleId = OwnedTypedModuleId::from("main");
    }

    #[test]
    fn no_generics() {
        // def foo(field a) -> field {
        //     return a;
        // }
        // def main(field a) -> field {
        //     u32 n = 42;
        //     n = n;
        //     a = a;
        //     a = foo(a);
        //     n = n;
        //     return a;
        // }

        // expected:
        // def main(field a_0) -> field {
        //     a_1 = a_0;
        //     # PUSH CALL to foo
        //         a_3 := a_1; // input binding
        //         #RETURN_AT_INDEX_0_0 := a_3;
        //     # POP CALL
        //     a_2 = #RETURN_AT_INDEX_0_0;
        //     return a_2;
        // }

        let foo: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![DeclarationVariable::field_element("a").into()],
            statements: vec![TypedStatement::Return(
                FieldElementExpression::identifier("a".into()).into(),
            )],
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .output(DeclarationType::FieldElement),
        };

        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![DeclarationVariable::field_element("a").into()],
            statements: vec![
                TypedStatement::definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    TypedExpression::Uint(42u32.into()),
                ),
                TypedStatement::definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    UExpression::identifier("n".into())
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::definition(
                    Variable::field_element("a").into(),
                    FieldElementExpression::identifier("a".into()).into(),
                ),
                TypedStatement::definition(
                    Variable::field_element("a").into(),
                    FieldElementExpression::function_call(
                        DeclarationFunctionKey::with_location("main", "foo").signature(
                            DeclarationSignature::new()
                                .inputs(vec![DeclarationType::FieldElement])
                                .output(DeclarationType::FieldElement),
                        ),
                        vec![],
                        vec![FieldElementExpression::identifier("a".into()).into()],
                    )
                    .into(),
                ),
                TypedStatement::definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    UExpression::identifier("n".into())
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::Return(FieldElementExpression::identifier("a".into()).into()),
            ],
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .output(DeclarationType::FieldElement),
        };

        let p = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    symbols: vec![
                        TypedFunctionSymbolDeclaration::new(
                            DeclarationFunctionKey::with_location("main", "foo").signature(
                                DeclarationSignature::new()
                                    .inputs(vec![DeclarationType::FieldElement])
                                    .output(DeclarationType::FieldElement),
                            ),
                            TypedFunctionSymbol::Here(foo),
                        )
                        .into(),
                        TypedFunctionSymbolDeclaration::new(
                            DeclarationFunctionKey::with_location("main", "main").signature(
                                DeclarationSignature::new()
                                    .inputs(vec![DeclarationType::FieldElement])
                                    .output(DeclarationType::FieldElement),
                            ),
                            TypedFunctionSymbol::Here(main),
                        )
                        .into(),
                    ],
                },
            )]
            .into_iter()
            .collect(),
        };

        let reduced = reduce_program(p);

        let expected_main = TypedFunction {
            arguments: vec![DeclarationVariable::field_element("a").into()],
            statements: vec![
                TypedStatement::definition(
                    Variable::field_element(Identifier::from("a").version(1)).into(),
                    FieldElementExpression::identifier("a".into()).into(),
                ),
                TypedStatement::PushCallLog(
                    DeclarationFunctionKey::with_location("main", "foo").signature(
                        DeclarationSignature::new()
                            .inputs(vec![DeclarationType::FieldElement])
                            .output(DeclarationType::FieldElement),
                    ),
                    GGenericsAssignment::default(),
                ),
                TypedStatement::definition(
                    Variable::field_element(Identifier::from("a").version(3)).into(),
                    FieldElementExpression::identifier(Identifier::from("a").version(1)).into(),
                ),
                TypedStatement::definition(
                    Variable::field_element(Identifier::from(CoreIdentifier::Call(0)).version(0))
                        .into(),
                    FieldElementExpression::identifier(Identifier::from("a").version(3)).into(),
                ),
                TypedStatement::PopCallLog,
                TypedStatement::definition(
                    Variable::field_element(Identifier::from("a").version(2)).into(),
                    FieldElementExpression::identifier(
                        Identifier::from(CoreIdentifier::Call(0)).version(0),
                    )
                    .into(),
                ),
                TypedStatement::Return(
                    FieldElementExpression::identifier(Identifier::from("a").version(2)).into(),
                ),
            ],
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .output(DeclarationType::FieldElement),
        };

        let expected: TypedProgram<Bn128Field> = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    symbols: vec![TypedFunctionSymbolDeclaration::new(
                        DeclarationFunctionKey::with_location("main", "main").signature(
                            DeclarationSignature::new()
                                .inputs(vec![DeclarationType::FieldElement])
                                .output(DeclarationType::FieldElement),
                        ),
                        TypedFunctionSymbol::Here(expected_main),
                    )
                    .into()],
                },
            )]
            .into_iter()
            .collect(),
        };

        assert_eq!(reduced.unwrap(), expected);
    }

    #[test]
    fn with_generics() {
        // def foo<K>(field[K] a) -> field[K] {
        //     return a;
        // }
        // def main(field a) -> field {
        //     u32 n = 42;
        //     n = n;
        //     field[1] b = [a];
        //     b = foo(b);
        //     n = n;
        //     return a + b[0];
        // }

        // expected:
        // def main(field a_0) -> field {
        //     field[1] b_0 = [42];
        //     # PUSH CALL to foo::<1>
        //         a_0 = b_0;
        //         #RETURN_AT_INDEX_0_0 := a_0;
        //     # POP CALL
        //     b_1 = #RETURN_AT_INDEX_0_0;
        //     return a_2 + b_1[0];
        // }

        let foo_signature = DeclarationSignature::new()
            .generics(vec![Some(
                GenericIdentifier::with_name("K").with_index(0).into(),
            )])
            .inputs(vec![DeclarationType::array((
                DeclarationType::FieldElement,
                DeclarationConstant::Generic(GenericIdentifier::with_name("K").with_index(0)),
            ))])
            .output(DeclarationType::array((
                DeclarationType::FieldElement,
                DeclarationConstant::Generic(GenericIdentifier::with_name("K").with_index(0)),
            )));

        let foo: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![DeclarationVariable::array(
                "a",
                DeclarationType::FieldElement,
                GenericIdentifier::with_name("K").with_index(0),
            )
            .into()],
            statements: vec![TypedStatement::Return(
                ArrayExpression::identifier("a".into())
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
            )],
            signature: foo_signature.clone(),
        };

        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![DeclarationVariable::field_element("a").into()],
            statements: vec![
                TypedStatement::definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    TypedExpression::Uint(42u32.into()),
                ),
                TypedStatement::definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    UExpression::identifier("n".into())
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::definition(
                    Variable::array("b", Type::FieldElement, 1u32).into(),
                    ArrayExpressionInner::Value(
                        vec![FieldElementExpression::identifier("a".into()).into()].into(),
                    )
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
                ),
                TypedStatement::definition(
                    Variable::array("b", Type::FieldElement, 1u32).into(),
                    ArrayExpression::function_call(
                        DeclarationFunctionKey::with_location("main", "foo")
                            .signature(foo_signature.clone()),
                        vec![None],
                        vec![ArrayExpression::identifier("b".into())
                            .annotate(Type::FieldElement, 1u32)
                            .into()],
                    )
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
                ),
                TypedStatement::definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    UExpression::identifier("n".into())
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::Return(
                    (FieldElementExpression::identifier("a".into())
                        + FieldElementExpression::select(
                            ArrayExpression::identifier("b".into())
                                .annotate(Type::FieldElement, 1u32),
                            0u32,
                        ))
                    .into(),
                ),
            ],
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .output(DeclarationType::FieldElement),
        };

        let p = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    symbols: vec![
                        TypedFunctionSymbolDeclaration::new(
                            DeclarationFunctionKey::with_location("main", "foo")
                                .signature(foo_signature.clone()),
                            TypedFunctionSymbol::Here(foo),
                        )
                        .into(),
                        TypedFunctionSymbolDeclaration::new(
                            DeclarationFunctionKey::with_location("main", "main").signature(
                                DeclarationSignature::new()
                                    .inputs(vec![DeclarationType::FieldElement])
                                    .output(DeclarationType::FieldElement),
                            ),
                            TypedFunctionSymbol::Here(main),
                        )
                        .into(),
                    ],
                },
            )]
            .into_iter()
            .collect(),
        };

        let reduced = reduce_program(p);

        let expected_main = TypedFunction {
            arguments: vec![DeclarationVariable::field_element("a").into()],
            statements: vec![
                TypedStatement::definition(
                    Variable::array("b", Type::FieldElement, 1u32).into(),
                    ArrayExpressionInner::Value(
                        vec![FieldElementExpression::identifier("a".into()).into()].into(),
                    )
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
                ),
                TypedStatement::PushCallLog(
                    DeclarationFunctionKey::with_location("main", "foo")
                        .signature(foo_signature.clone()),
                    GGenericsAssignment(
                        vec![(GenericIdentifier::with_name("K").with_index(0), 1)]
                            .into_iter()
                            .collect(),
                    ),
                ),
                TypedStatement::definition(
                    Variable::array(Identifier::from("a").version(1), Type::FieldElement, 1u32)
                        .into(),
                    ArrayExpression::identifier("b".into())
                        .annotate(Type::FieldElement, 1u32)
                        .into(),
                ),
                TypedStatement::definition(
                    Variable::array(
                        Identifier::from(CoreIdentifier::Call(0)).version(0),
                        Type::FieldElement,
                        1u32,
                    )
                    .into(),
                    ArrayExpression::identifier(Identifier::from("a").version(1))
                        .annotate(Type::FieldElement, 1u32)
                        .into(),
                ),
                TypedStatement::PopCallLog,
                TypedStatement::definition(
                    Variable::array(Identifier::from("b").version(1), Type::FieldElement, 1u32)
                        .into(),
                    ArrayExpression::identifier(
                        Identifier::from(CoreIdentifier::Call(0)).version(0),
                    )
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
                ),
                TypedStatement::Return(
                    (FieldElementExpression::identifier("a".into())
                        + FieldElementExpression::select(
                            ArrayExpression::identifier(Identifier::from("b").version(1))
                                .annotate(Type::FieldElement, 1u32),
                            0u32,
                        ))
                    .into(),
                ),
            ],
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .output(DeclarationType::FieldElement),
        };

        let expected = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    symbols: vec![TypedFunctionSymbolDeclaration::new(
                        DeclarationFunctionKey::with_location("main", "main").signature(
                            DeclarationSignature::new()
                                .inputs(vec![DeclarationType::FieldElement])
                                .output(DeclarationType::FieldElement),
                        ),
                        TypedFunctionSymbol::Here(expected_main),
                    )
                    .into()],
                },
            )]
            .into_iter()
            .collect(),
        };

        assert_eq!(reduced.unwrap(), expected);
    }

    #[test]
    fn with_generics_and_propagation() {
        // def foo<K>(field[K] a) -> field[K] {
        //     return a;
        // }
        // def main(field a) -> field {
        //     u32 n = 2;
        //     n = n;
        //     field[n - 1] b = [a];
        //     b = foo(b);
        //     n = n;
        //     return a + b[0];
        // }

        // expected:
        // def main(field a_0) -> field {
        //     field[1] b_0 = [42];
        //     # PUSH CALL to foo::<1>
        //         a_0 = b_0;
        //         #RETURN_AT_INDEX_0_0 := a_0;
        //     # POP CALL
        //     b_1 = #RETURN_AT_INDEX_0_0;
        //     return a_2 + b_1[0];
        // }

        let foo_signature = DeclarationSignature::new()
            .generics(vec![Some(
                GenericIdentifier::with_name("K").with_index(0).into(),
            )])
            .inputs(vec![DeclarationType::array((
                DeclarationType::FieldElement,
                DeclarationConstant::Generic(GenericIdentifier::with_name("K").with_index(0)),
            ))])
            .output(DeclarationType::array((
                DeclarationType::FieldElement,
                DeclarationConstant::Generic(GenericIdentifier::with_name("K").with_index(0)),
            )));

        let foo: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![DeclarationVariable::array(
                "a",
                DeclarationType::FieldElement,
                GenericIdentifier::with_name("K").with_index(0),
            )
            .into()],
            statements: vec![TypedStatement::Return(
                ArrayExpression::identifier("a".into())
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
            )],
            signature: foo_signature.clone(),
        };

        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![DeclarationVariable::field_element("a").into()],
            statements: vec![
                TypedStatement::definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    TypedExpression::Uint(2u32.into()),
                ),
                TypedStatement::definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    UExpression::identifier("n".into())
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::definition(
                    Variable::array(
                        "b",
                        Type::FieldElement,
                        UExpressionInner::Sub(
                            box UExpression::identifier("n".into()).annotate(UBitwidth::B32),
                            box 1u32.into(),
                        )
                        .annotate(UBitwidth::B32),
                    )
                    .into(),
                    ArrayExpressionInner::Value(
                        vec![FieldElementExpression::identifier("a".into()).into()].into(),
                    )
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
                ),
                TypedStatement::definition(
                    Variable::array("b", Type::FieldElement, 1u32).into(),
                    ArrayExpression::function_call(
                        DeclarationFunctionKey::with_location("main", "foo")
                            .signature(foo_signature.clone()),
                        vec![None],
                        vec![ArrayExpression::identifier("b".into())
                            .annotate(Type::FieldElement, 1u32)
                            .into()],
                    )
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
                ),
                TypedStatement::definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    UExpression::identifier("n".into())
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::Return(
                    (FieldElementExpression::identifier("a".into())
                        + FieldElementExpression::select(
                            ArrayExpression::identifier("b".into())
                                .annotate(Type::FieldElement, 1u32),
                            0u32,
                        ))
                    .into(),
                ),
            ],
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .output(DeclarationType::FieldElement),
        };

        let p = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    symbols: vec![
                        TypedFunctionSymbolDeclaration::new(
                            DeclarationFunctionKey::with_location("main", "foo")
                                .signature(foo_signature.clone()),
                            TypedFunctionSymbol::Here(foo),
                        )
                        .into(),
                        TypedFunctionSymbolDeclaration::new(
                            DeclarationFunctionKey::with_location("main", "main").signature(
                                DeclarationSignature::new()
                                    .inputs(vec![DeclarationType::FieldElement])
                                    .output(DeclarationType::FieldElement),
                            ),
                            TypedFunctionSymbol::Here(main),
                        )
                        .into(),
                    ],
                },
            )]
            .into_iter()
            .collect(),
        };

        let reduced = reduce_program(p);

        let expected_main = TypedFunction {
            arguments: vec![DeclarationVariable::field_element("a").into()],
            statements: vec![
                TypedStatement::definition(
                    Variable::array("b", Type::FieldElement, 1u32).into(),
                    ArrayExpressionInner::Value(
                        vec![FieldElementExpression::identifier("a".into()).into()].into(),
                    )
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
                ),
                TypedStatement::PushCallLog(
                    DeclarationFunctionKey::with_location("main", "foo")
                        .signature(foo_signature.clone()),
                    GGenericsAssignment(
                        vec![(GenericIdentifier::with_name("K").with_index(0), 1)]
                            .into_iter()
                            .collect(),
                    ),
                ),
                TypedStatement::definition(
                    Variable::array(Identifier::from("a").version(1), Type::FieldElement, 1u32)
                        .into(),
                    ArrayExpression::identifier("b".into())
                        .annotate(Type::FieldElement, 1u32)
                        .into(),
                ),
                TypedStatement::definition(
                    Variable::array(
                        Identifier::from(CoreIdentifier::Call(0)).version(0),
                        Type::FieldElement,
                        1u32,
                    )
                    .into(),
                    ArrayExpression::identifier(Identifier::from("a").version(1))
                        .annotate(Type::FieldElement, 1u32)
                        .into(),
                ),
                TypedStatement::PopCallLog,
                TypedStatement::definition(
                    Variable::array(Identifier::from("b").version(1), Type::FieldElement, 1u32)
                        .into(),
                    ArrayExpression::identifier(
                        Identifier::from(CoreIdentifier::Call(0)).version(0),
                    )
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
                ),
                TypedStatement::Return(
                    (FieldElementExpression::identifier("a".into())
                        + FieldElementExpression::select(
                            ArrayExpression::identifier(Identifier::from("b").version(1))
                                .annotate(Type::FieldElement, 1u32),
                            0u32,
                        ))
                    .into(),
                ),
            ],
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .output(DeclarationType::FieldElement),
        };

        let expected = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    symbols: vec![TypedFunctionSymbolDeclaration::new(
                        DeclarationFunctionKey::with_location("main", "main").signature(
                            DeclarationSignature::new()
                                .inputs(vec![DeclarationType::FieldElement])
                                .output(DeclarationType::FieldElement),
                        ),
                        TypedFunctionSymbol::Here(expected_main),
                    )
                    .into()],
                },
            )]
            .into_iter()
            .collect(),
        };

        assert_eq!(reduced.unwrap(), expected);
    }

    #[test]
    fn call_in_call() {
        // we use a global ssa counter, hence reusing variable names in called functions
        // leads to counter increase

        // def bar<K>(field[K] a) -> field[K] {
        //     return a;
        // }

        // def foo<K>(field[K] a) -> field[K] {
        //     field[K] ret = bar([...a, 0])[0..K];
        //     return ret;
        // }

        // def main() {
        //     field[1] b = foo([1]);
        //     return;
        // }

        // expected:
        // def main() {
        //     # PUSH CALL to foo::<1>
        //         # PUSH CALL to bar::<2>
        //         # POP CALL
        //     # POP CALL
        //     return;
        // }

        let foo_signature = DeclarationSignature::new()
            .inputs(vec![DeclarationType::array((
                DeclarationType::FieldElement,
                DeclarationConstant::Generic(GenericIdentifier::with_name("K").with_index(0)),
            ))])
            .output(DeclarationType::array((
                DeclarationType::FieldElement,
                DeclarationConstant::Generic(GenericIdentifier::with_name("K").with_index(0)),
            )))
            .generics(vec![Some(
                GenericIdentifier::with_name("K").with_index(0).into(),
            )]);

        let foo: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![DeclarationVariable::array(
                "a",
                DeclarationType::FieldElement,
                DeclarationConstant::Generic(GenericIdentifier::with_name("K").with_index(0)),
            )
            .into()],
            statements: vec![
                TypedStatement::definition(
                    Variable::array(
                        "ret",
                        Type::FieldElement,
                        UExpression::identifier("K".into()).annotate(UBitwidth::B32),
                    )
                    .into(),
                    ArrayExpressionInner::Slice(
                        box ArrayExpression::function_call(
                            DeclarationFunctionKey::with_location("main", "bar")
                                .signature(foo_signature.clone()),
                            vec![None],
                            vec![ArrayExpressionInner::Value(
                                vec![
                                    TypedExpressionOrSpread::Spread(
                                        ArrayExpression::identifier("a".into())
                                            .annotate(Type::FieldElement, 1u32)
                                            .into(),
                                    ),
                                    FieldElementExpression::Number(Bn128Field::from(0)).into(),
                                ]
                                .into(),
                            )
                            .annotate(
                                Type::FieldElement,
                                UExpression::identifier("K".into()).annotate(UBitwidth::B32)
                                    + 1u32.into(),
                            )
                            .into()],
                        )
                        .annotate(
                            Type::FieldElement,
                            UExpression::identifier("K".into()).annotate(UBitwidth::B32)
                                + 1u32.into(),
                        ),
                        box 0u32.into(),
                        box UExpression::identifier("K".into()).annotate(UBitwidth::B32),
                    )
                    .annotate(
                        Type::FieldElement,
                        UExpression::identifier("K".into()).annotate(UBitwidth::B32),
                    )
                    .into(),
                ),
                TypedStatement::Return(
                    ArrayExpression::identifier("ret".into())
                        .annotate(
                            Type::FieldElement,
                            UExpression::identifier("K".into()).annotate(UBitwidth::B32),
                        )
                        .into(),
                ),
            ],
            signature: foo_signature.clone(),
        };

        let bar_signature = foo_signature.clone();

        let bar: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![DeclarationVariable::array(
                "a",
                DeclarationType::FieldElement,
                DeclarationConstant::Generic(GenericIdentifier::with_name("K").with_index(0)),
            )
            .into()],
            statements: vec![TypedStatement::Return(
                ArrayExpression::identifier("a".into())
                    .annotate(
                        Type::FieldElement,
                        UExpression::identifier("K".into()).annotate(UBitwidth::B32),
                    )
                    .into(),
            )],
            signature: bar_signature.clone(),
        };

        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![],
            statements: vec![
                TypedStatement::definition(
                    Variable::array("b", Type::FieldElement, 1u32).into(),
                    ArrayExpression::function_call(
                        DeclarationFunctionKey::with_location("main", "foo")
                            .signature(foo_signature.clone()),
                        vec![None],
                        vec![ArrayExpressionInner::Value(
                            vec![FieldElementExpression::Number(Bn128Field::from(1)).into()].into(),
                        )
                        .annotate(Type::FieldElement, 1u32)
                        .into()],
                    )
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
                ),
                TypedStatement::Return(
                    TupleExpressionInner::Value(vec![])
                        .annotate(TupleType::new(vec![]))
                        .into(),
                ),
            ],
            signature: DeclarationSignature::new(),
        };

        let p = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    symbols: vec![
                        TypedFunctionSymbolDeclaration::new(
                            DeclarationFunctionKey::with_location("main", "bar")
                                .signature(bar_signature.clone()),
                            TypedFunctionSymbol::Here(bar),
                        )
                        .into(),
                        TypedFunctionSymbolDeclaration::new(
                            DeclarationFunctionKey::with_location("main", "foo")
                                .signature(foo_signature.clone()),
                            TypedFunctionSymbol::Here(foo),
                        )
                        .into(),
                        TypedFunctionSymbolDeclaration::new(
                            DeclarationFunctionKey::with_location("main", "main"),
                            TypedFunctionSymbol::Here(main),
                        )
                        .into(),
                    ],
                },
            )]
            .into_iter()
            .collect(),
        };

        let reduced = reduce_program(p);

        let expected_main = TypedFunction {
            arguments: vec![],
            statements: vec![
                TypedStatement::PushCallLog(
                    DeclarationFunctionKey::with_location("main", "foo")
                        .signature(foo_signature.clone()),
                    GGenericsAssignment(
                        vec![(GenericIdentifier::with_name("K").with_index(0), 1)]
                            .into_iter()
                            .collect(),
                    ),
                ),
                TypedStatement::PushCallLog(
                    DeclarationFunctionKey::with_location("main", "bar")
                        .signature(foo_signature.clone()),
                    GGenericsAssignment(
                        vec![(GenericIdentifier::with_name("K").with_index(0), 2)]
                            .into_iter()
                            .collect(),
                    ),
                ),
                TypedStatement::PopCallLog,
                TypedStatement::PopCallLog,
                TypedStatement::Return(
                    TupleExpressionInner::Value(vec![])
                        .annotate(TupleType::new(vec![]))
                        .into(),
                ),
            ],
            signature: DeclarationSignature::new(),
        };

        let expected = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    symbols: vec![TypedFunctionSymbolDeclaration::new(
                        DeclarationFunctionKey::with_location("main", "main")
                            .signature(DeclarationSignature::new()),
                        TypedFunctionSymbol::Here(expected_main),
                    )
                    .into()],
                },
            )]
            .into_iter()
            .collect(),
        };

        assert_eq!(reduced.unwrap(), expected);
    }

    #[test]
    fn incompatible() {
        // def foo<K>(field[K] a) -> field[K] {
        //     return a;
        // }
        // def main() {
        //     field[1] b = foo([]);
        //     return;
        // }

        // expected:
        // Error: Incompatible

        let foo_signature = DeclarationSignature::new()
            .generics(vec![Some(
                GenericIdentifier::with_name("K").with_index(0).into(),
            )])
            .inputs(vec![DeclarationType::array((
                DeclarationType::FieldElement,
                GenericIdentifier::with_name("K").with_index(0),
            ))])
            .output(DeclarationType::array((
                DeclarationType::FieldElement,
                GenericIdentifier::with_name("K").with_index(0),
            )));

        let foo: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![DeclarationVariable::array(
                "a",
                DeclarationType::FieldElement,
                GenericIdentifier::with_name("K").with_index(0),
            )
            .into()],
            statements: vec![TypedStatement::Return(
                ArrayExpression::identifier("a".into())
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
            )],
            signature: foo_signature.clone(),
        };

        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![],
            statements: vec![
                TypedStatement::definition(
                    Variable::array("b", Type::FieldElement, 1u32).into(),
                    ArrayExpression::function_call(
                        DeclarationFunctionKey::with_location("main", "foo")
                            .signature(foo_signature.clone()),
                        vec![None],
                        vec![ArrayExpressionInner::Value(vec![].into())
                            .annotate(Type::FieldElement, 0u32)
                            .into()],
                    )
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
                ),
                TypedStatement::Return(
                    TupleExpressionInner::Value(vec![])
                        .annotate(TupleType::new(vec![]))
                        .into(),
                ),
            ],
            signature: DeclarationSignature::new()
                .inputs(vec![])
                .output(DeclarationType::Tuple(GTupleType::new(vec![]))),
        };

        let p = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    symbols: vec![
                        TypedFunctionSymbolDeclaration::new(
                            DeclarationFunctionKey::with_location("main", "foo")
                                .signature(foo_signature.clone()),
                            TypedFunctionSymbol::Here(foo),
                        )
                        .into(),
                        TypedFunctionSymbolDeclaration::new(
                            DeclarationFunctionKey::with_location("main", "main").signature(
                                DeclarationSignature::new()
                                    .inputs(vec![])
                                    .output(DeclarationType::Tuple(GTupleType::new(vec![]))),
                            ),
                            TypedFunctionSymbol::Here(main),
                        )
                        .into(),
                    ],
                },
            )]
            .into_iter()
            .collect(),
        };

        let reduced = reduce_program(p);

        assert_eq!(
            reduced,
            Err(Error::Incompatible("Call site `main/foo<_>(field[0]) -> field[1]` incompatible with declaration `main/foo<K>(field[K]) -> field[K]`".into()))
        );
    }
}
