// The reducer reduces the program to a single function which is:
// - in SSA form
// - free of function calls (except for low level calls) thanks to inlining
// - free of for-loops thanks to unrolling

// The process happens in a greedy way, starting from the main function
// For each statement:
// * put it in ssa form
// * propagate it
// * inline it (calling this process recursively)
// * propagate again

// if at any time a generic parameter or loop bound is not constant, error out, because it should have been propagated to a constant by the greedy approach

mod constants_reader;
mod constants_writer;
mod inline;
mod shallow_ssa;

use self::inline::InlineValue;
use self::inline::{inline_call, InlineError};
use std::collections::HashMap;
use zokrates_ast::common::ResultFold;
use zokrates_ast::common::WithSpan;
use zokrates_ast::typed::DeclarationParameter;
use zokrates_ast::typed::Folder;
use zokrates_ast::typed::SliceExpression;
use zokrates_ast::typed::SliceOrExpression;
use zokrates_ast::typed::{result_folder::*, ArrayExpression};
use zokrates_ast::typed::{CanonicalConstantIdentifier, EmbedCall, Variable};

use zokrates_ast::typed::TypedAssignee;
use zokrates_ast::typed::{
    BlockExpression, CoreIdentifier, Expr, FunctionCall, FunctionCallExpression,
    FunctionCallOrExpression, Id, TypedExpression, TypedFunction, TypedFunctionSymbol,
    TypedFunctionSymbolDeclaration, TypedModule, TypedProgram, TypedStatement, UExpression,
    UExpressionInner,
};

use zokrates_ast::untyped::OwnedModuleId;
use zokrates_field::Field;

use self::constants_writer::ConstantsWriter;
use self::shallow_ssa::ShallowTransformer;

use crate::propagation;
use crate::propagation::Propagator;

use std::fmt;

const MAX_FOR_LOOP_SIZE: u128 = 2u128.pow(20);

// A map to register the canonical value of all constants. The values must be literals.
pub type ConstantDefinitions<'ast, T> =
    HashMap<CanonicalConstantIdentifier<'ast>, TypedExpression<'ast, T>>;

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    Incompatible(String),
    GenericsInMain,
    LoopTooLarge(u128),
    ConstantReduction(String, OwnedModuleId),
    NonConstant(String),
    Type(String),
    Propagation(propagation::Error),
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
            Error::LoopTooLarge(size) => write!(f, "Found a loop of size {}, which is larger than the maximum allowed of {}. Check the loop bounds, especially for underflows", size, MAX_FOR_LOOP_SIZE),
            Error::ConstantReduction(name, module) => write!(f, "Failed to reduce constant `{}` in module `{}` to a literal, try simplifying its declaration", name, module.display()),
            Error::NonConstant(s) => write!(f, "{}", s),
            Error::Type(s) => write!(f, "{}", s),
            Error::Propagation(e) => write!(f, "{}", e),
        }
    }
}

impl From<propagation::Error> for Error {
    fn from(e: propagation::Error) -> Self {
        Self::Propagation(e)
    }
}

#[derive(Debug)]
struct Reducer<'ast, 'a, T> {
    program: &'a TypedProgram<'ast, T>,
    propagator: Propagator<'ast, T>,
    ssa: ShallowTransformer<'ast>,
    statement_buffer: Vec<TypedStatement<'ast, T>>,
}

impl<'ast, 'a, T: Field> Reducer<'ast, 'a, T> {
    fn new(program: &'a TypedProgram<'ast, T>) -> Self {
        Reducer {
            propagator: Propagator::default(),
            ssa: ShallowTransformer::default(),
            statement_buffer: vec![],
            program,
        }
    }

    fn push_call_frame(&mut self) {
        self.ssa.push_call_frame();
    }

    fn pop_call_frame(&mut self) {
        self.propagator.clear_call_frame(self.ssa.latest_frame);
        self.ssa.pop_call_frame();
    }
}

impl<'ast, 'a, T: Field> ResultFolder<'ast, T> for Reducer<'ast, 'a, T> {
    type Error = Error;

    fn fold_parameter(
        &mut self,
        p: DeclarationParameter<'ast, T>,
    ) -> Result<DeclarationParameter<'ast, T>, Self::Error> {
        Ok(self.ssa.fold_parameter(p))
    }

    fn fold_function_call_expression<
        E: Id<'ast, T> + From<TypedExpression<'ast, T>> + Expr<'ast, T> + FunctionCall<'ast, T>,
    >(
        &mut self,
        ty: &E::Ty,
        e: FunctionCallExpression<'ast, T, E>,
    ) -> Result<FunctionCallOrExpression<'ast, T, E>, Self::Error> {
        let span = e.get_span();

        // generics are already in ssa form
        let generics: Vec<_> = e
            .generics
            .into_iter()
            .map(|g| {
                g.map(|g| {
                    let g = self.propagator.fold_uint_expression(g)?;
                    let g = self.fold_uint_expression(g)?;

                    self.propagator
                        .fold_uint_expression(g)
                        .map_err(Self::Error::from)
                })
                .transpose()
            })
            .collect::<Result<_, _>>()?;

        // arguments are already in ssa form

        let arguments: Vec<_> = e
            .arguments
            .into_iter()
            .map(|e| {
                let e = self.propagator.fold_expression(e)?;
                let e = self.fold_expression(e)?;

                self.propagator
                    .fold_expression(e)
                    .map_err(Self::Error::from)
            })
            .collect::<Result<_, _>>()?;

        self.push_call_frame();

        let res = inline_call::<_, E>(&e.function_key, &generics, &arguments, ty, self.program);

        let res = match res {
            Ok(InlineValue {
                input_variables,
                statements,
                return_value,
            }) => {
                // the lhs is from the inner call frame, the rhs is from the outer one, so only fold the lhs
                let input_bindings: Vec<_> = input_variables
                    .into_iter()
                    .zip(arguments)
                    .map(|(v, a)| {
                        TypedStatement::definition(self.ssa.fold_assignee(v.into()), a).span(span)
                    })
                    .collect();

                let input_bindings = input_bindings
                    .into_iter()
                    .map(|s| self.propagator.fold_statement(s))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .flatten()
                    .collect::<Vec<_>>();

                self.statement_buffer.extend(input_bindings);

                let statements = statements
                    .into_iter()
                    .map(|s| self.fold_statement(s))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .flatten()
                    .collect::<Vec<_>>();

                self.statement_buffer.extend(statements);

                let return_value = self.ssa.fold_expression(return_value);

                let return_value = self.propagator.fold_expression(return_value)?;

                let return_value = self.fold_expression(return_value)?;

                Ok(FunctionCallOrExpression::Expression(
                    E::from(return_value).into_inner(),
                ))
            }
            Err(InlineError::Generic(decl, conc)) => Err(Error::Incompatible(format!(
                "Call site `{}` incompatible with declaration `{}`",
                conc, decl
            ))),
            Err(InlineError::NonConstant) => Err(Error::NonConstant(format!(
                "Generic parameters must be compile-time constants, found {}",
                FunctionCallExpression::<_, E>::new(e.function_key, generics, arguments)
            ))),
            Err(InlineError::Flat(embed, generics, output_type)) => {
                let identifier = self.ssa.issue_next_identifier(CoreIdentifier::Call(0));

                let var = Variable::new(identifier.clone(), output_type);

                let v: TypedAssignee<'ast, T> = var.clone().into();

                self.statement_buffer.push(
                    TypedStatement::embed_call_definition(
                        v,
                        EmbedCall::new(embed, generics, arguments),
                    )
                    .span(span),
                );
                Ok(FunctionCallOrExpression::Expression(
                    E::identifier(identifier).span(span),
                ))
            }
        };

        self.pop_call_frame();

        res
    }

    fn fold_block_expression<E: ResultFold<Self, Self::Error>>(
        &mut self,
        b: BlockExpression<'ast, T, E>,
    ) -> Result<BlockExpression<'ast, T, E>, Self::Error> {
        // backup the statements and continue with a fresh state
        let statement_buffer = std::mem::take(&mut self.statement_buffer);

        let block = fold_block_expression(self, b)?;

        // put the original statements back and extract the statements created by visiting the block
        let extra_statements = std::mem::replace(&mut self.statement_buffer, statement_buffer);

        // return the visited block, augmented with the statements created while visiting it
        Ok(BlockExpression {
            statements: block
                .statements
                .into_iter()
                .chain(extra_statements)
                .collect(),
            ..block
        })
    }

    fn fold_canonical_constant_identifier(
        &mut self,
        _: CanonicalConstantIdentifier<'ast>,
    ) -> Result<CanonicalConstantIdentifier<'ast>, Self::Error> {
        unreachable!("canonical constant identifiers should not be folded, they should be inlined")
    }

    // here we implement fold_statement and not fold_statement_cases because we do not want the span of the input
    // to be applied to all the outputs: a statement which contains a call which gets inline should not hide the
    // inlined statements behind its own span
    fn fold_statement(
        &mut self,
        s: TypedStatement<'ast, T>,
    ) -> Result<Vec<TypedStatement<'ast, T>>, Self::Error> {
        let res = match s {
            TypedStatement::For(s) => {
                let from = self.ssa.fold_uint_expression(s.from);
                let from = self.propagator.fold_uint_expression(from)?;
                let from = self.fold_uint_expression(from)?;
                let from = self.propagator.fold_uint_expression(from)?;

                let to = self.ssa.fold_uint_expression(s.to);
                let to = self.propagator.fold_uint_expression(to)?;
                let to = self.fold_uint_expression(to)?;
                let to = self.propagator.fold_uint_expression(to)?;

                match (from.as_inner(), to.as_inner()) {
                    (UExpressionInner::Value(from), UExpressionInner::Value(to))
                        if to.value - from.value > MAX_FOR_LOOP_SIZE =>
                    {
                        Err(Error::LoopTooLarge(to.value.saturating_sub(from.value)))
                    }
                    (UExpressionInner::Value(from), UExpressionInner::Value(to)) => Ok((from.value
                        ..to.value)
                        .flat_map(|index| {
                            std::iter::once(TypedStatement::definition(
                                s.var.clone().into(),
                                UExpression::from(index as u32).into(),
                            ))
                            .chain(s.statements.clone())
                            .map(|s| self.fold_statement(s))
                            .collect::<Vec<_>>()
                        })
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .flatten()
                        .collect::<Vec<_>>()),
                    _ => Err(Error::NonConstant(format!(
                        "Expected loop bounds to be constant, found {}..{}",
                        from, to
                    ))),
                }?
            }
            s => {
                let statements = self.ssa.fold_statement(s);

                let statements = statements
                    .into_iter()
                    .map(|s| self.propagator.fold_statement(s))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .flatten();

                let statements = statements
                    .map(|s| fold_statement(self, s))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .flatten();

                let statements = statements
                    .map(|s| self.propagator.fold_statement(s))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .flatten();

                statements.collect()
            }
        };

        Ok(self.statement_buffer.drain(..).chain(res).collect())
    }

    fn fold_slice_expression(
        &mut self,
        e: zokrates_ast::typed::SliceExpression<'ast, T>,
    ) -> Result<zokrates_ast::typed::SliceOrExpression<'ast, T>, Self::Error> {
        let array = self.ssa.fold_array_expression(*e.array);
        let array = self.propagator.fold_array_expression(array)?;
        let array = self.fold_array_expression(array)?;
        let array = self.propagator.fold_array_expression(array)?;

        let from = self.ssa.fold_uint_expression(*e.from);
        let from = self.propagator.fold_uint_expression(from)?;
        let from = self.fold_uint_expression(from)?;
        let from = self.propagator.fold_uint_expression(from)?;

        let to = self.ssa.fold_uint_expression(*e.to);
        let to = self.propagator.fold_uint_expression(to)?;
        let to = self.fold_uint_expression(to)?;
        let to = self.propagator.fold_uint_expression(to)?;

        match (from.as_inner(), to.as_inner()) {
            (UExpressionInner::Value(..), UExpressionInner::Value(..)) => Ok(
                SliceOrExpression::Slice(SliceExpression::new(array, from, to)),
            ),
            _ => Err(Error::NonConstant(format!(
                "Slice bounds must be compile time constants, found {}",
                ArrayExpression::slice(array, from, to)
            ))),
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
            let main_function = Reducer::new(&p).fold_function(main_function)?;

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
                ..p
            })
        }
        _ => Err(Error::GenericsInMain),
    }
}

fn reduce_function<'ast, T: Field>(
    f: TypedFunction<'ast, T>,
    program: &TypedProgram<'ast, T>,
) -> Result<TypedFunction<'ast, T>, Error> {
    assert!(f.signature.generics.is_empty());

    Reducer::new(program).fold_function(f)
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_ast::typed::types::DeclarationSignature;
    use zokrates_ast::typed::types::{DeclarationConstant, GTupleType};
    use zokrates_ast::typed::{
        ArrayExpression, ArrayType, DeclarationFunctionKey, DeclarationType, DeclarationVariable,
        FieldElementExpression, GenericIdentifier, Identifier, Select, TupleExpression, TupleType,
        Type, TypedExpression, TypedExpressionOrSpread, UBitwidth, Variable,
    };
    use zokrates_field::Bn128Field;

    use lazy_static::lazy_static;

    lazy_static! {
        static ref MAIN_MODULE_ID: OwnedModuleId = OwnedModuleId::from("main");
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
        // def main(field a_f0_v0) -> field {
        //     a_f0_v1 = a_f0_v0; // redef
        //     a_f1_v0 = a_f0_v1; // input binding
        //     a_f0_v2 = a_f1_v0; // output binding
        //     return a_f0_v2;
        // }

        let foo: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![DeclarationVariable::field_element("a").into()],
            statements: vec![TypedStatement::ret(
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
                TypedStatement::ret(FieldElementExpression::identifier("a".into()).into()),
            ],
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .output(DeclarationType::FieldElement),
        };

        let p = TypedProgram {
            module_map: Default::default(),
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
                TypedStatement::definition(
                    Variable::field_element(Identifier::from("a").in_frame(1)).into(),
                    FieldElementExpression::identifier(Identifier::from("a").version(1)).into(),
                ),
                TypedStatement::definition(
                    Variable::field_element(Identifier::from("a").version(2)).into(),
                    FieldElementExpression::identifier(Identifier::from("a").in_frame(1)).into(),
                ),
                TypedStatement::ret(
                    FieldElementExpression::identifier(Identifier::from("a").version(2)).into(),
                ),
            ],
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .output(DeclarationType::FieldElement),
        };

        let expected: TypedProgram<Bn128Field> = TypedProgram {
            module_map: Default::default(),
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
        // def main(field a_f0_v0) -> field {
        //     field[1] b_f0_v0 = [a_f0_v0];
        //     a_f1_v0 = b_f0_v0;
        //     b_f0_v1 = a_f1_v0;
        //     return a_f0_v0 + b_f0_v1[0];
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
            statements: vec![TypedStatement::ret(
                ArrayExpression::identifier("a".into())
                    .annotate(ArrayType::new(Type::FieldElement, 1u32))
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
                    ArrayExpression::value(vec![
                        FieldElementExpression::identifier("a".into()).into()
                    ])
                    .annotate(ArrayType::new(Type::FieldElement, 1u32))
                    .into(),
                ),
                TypedStatement::definition(
                    Variable::array("b", Type::FieldElement, 1u32).into(),
                    ArrayExpression::function_call(
                        DeclarationFunctionKey::with_location("main", "foo")
                            .signature(foo_signature.clone()),
                        vec![None],
                        vec![ArrayExpression::identifier("b".into())
                            .annotate(ArrayType::new(Type::FieldElement, 1u32))
                            .into()],
                    )
                    .annotate(ArrayType::new(Type::FieldElement, 1u32))
                    .into(),
                ),
                TypedStatement::definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    UExpression::identifier("n".into())
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::ret(
                    (FieldElementExpression::identifier("a".into())
                        + FieldElementExpression::select(
                            ArrayExpression::identifier("b".into())
                                .annotate(ArrayType::new(Type::FieldElement, 1u32)),
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
            module_map: Default::default(),
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
                    ArrayExpression::value(vec![
                        FieldElementExpression::identifier("a".into()).into()
                    ])
                    .annotate(ArrayType::new(Type::FieldElement, 1u32))
                    .into(),
                ),
                TypedStatement::definition(
                    Variable::array(Identifier::from("a").in_frame(1), Type::FieldElement, 1u32)
                        .into(),
                    ArrayExpression::identifier("b".into())
                        .annotate(ArrayType::new(Type::FieldElement, 1u32))
                        .into(),
                ),
                TypedStatement::definition(
                    Variable::array(Identifier::from("b").version(1), Type::FieldElement, 1u32)
                        .into(),
                    ArrayExpression::identifier(Identifier::from("a").in_frame(1))
                        .annotate(ArrayType::new(Type::FieldElement, 1u32))
                        .into(),
                ),
                TypedStatement::ret(
                    (FieldElementExpression::identifier("a".into())
                        + FieldElementExpression::select(
                            ArrayExpression::identifier(Identifier::from("b").version(1))
                                .annotate(ArrayType::new(Type::FieldElement, 1u32)),
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
            module_map: Default::default(),
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
        // def main(field a) -> field {
        //     field[1] b = [a];
        //     a_f1 = b;
        //     b_1 = a_f1;
        //     return a + b_1[0];
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
            statements: vec![TypedStatement::ret(
                ArrayExpression::identifier("a".into())
                    .annotate(ArrayType::new(Type::FieldElement, 1u32))
                    .into(),
            )],
            signature: foo_signature.clone(),
        };

        use std::ops::Sub;

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
                        UExpression::sub(
                            UExpression::identifier("n".into()).annotate(UBitwidth::B32),
                            1u32.into(),
                        ),
                    )
                    .into(),
                    ArrayExpression::value(vec![
                        FieldElementExpression::identifier("a".into()).into()
                    ])
                    .annotate(ArrayType::new(Type::FieldElement, 1u32))
                    .into(),
                ),
                TypedStatement::definition(
                    Variable::array("b", Type::FieldElement, 1u32).into(),
                    ArrayExpression::function_call(
                        DeclarationFunctionKey::with_location("main", "foo")
                            .signature(foo_signature.clone()),
                        vec![None],
                        vec![ArrayExpression::identifier("b".into())
                            .annotate(ArrayType::new(Type::FieldElement, 1u32))
                            .into()],
                    )
                    .annotate(ArrayType::new(Type::FieldElement, 1u32))
                    .into(),
                ),
                TypedStatement::definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    UExpression::identifier("n".into())
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::ret(
                    (FieldElementExpression::identifier("a".into())
                        + FieldElementExpression::select(
                            ArrayExpression::identifier("b".into())
                                .annotate(ArrayType::new(Type::FieldElement, 1u32)),
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
            module_map: Default::default(),
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
                    ArrayExpression::value(vec![
                        FieldElementExpression::identifier("a".into()).into()
                    ])
                    .annotate(ArrayType::new(Type::FieldElement, 1u32))
                    .into(),
                ),
                TypedStatement::definition(
                    Variable::array(Identifier::from("a").in_frame(1), Type::FieldElement, 1u32)
                        .into(),
                    ArrayExpression::identifier("b".into())
                        .annotate(ArrayType::new(Type::FieldElement, 1u32))
                        .into(),
                ),
                TypedStatement::definition(
                    Variable::array(Identifier::from("b").version(1), Type::FieldElement, 1u32)
                        .into(),
                    ArrayExpression::identifier(Identifier::from("a").in_frame(1))
                        .annotate(ArrayType::new(Type::FieldElement, 1u32))
                        .into(),
                ),
                TypedStatement::ret(
                    (FieldElementExpression::identifier("a".into())
                        + FieldElementExpression::select(
                            ArrayExpression::identifier(Identifier::from("b").version(1))
                                .annotate(ArrayType::new(Type::FieldElement, 1u32)),
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
            module_map: Default::default(),
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
                    ArrayExpression::slice(
                        ArrayExpression::function_call(
                            DeclarationFunctionKey::with_location("main", "bar")
                                .signature(foo_signature.clone()),
                            vec![None],
                            vec![ArrayExpression::value(vec![
                                TypedExpressionOrSpread::Spread(
                                    ArrayExpression::identifier("a".into())
                                        .annotate(ArrayType::new(Type::FieldElement, 1u32))
                                        .into(),
                                ),
                                FieldElementExpression::value(Bn128Field::from(0)).into(),
                            ])
                            .annotate(ArrayType::new(
                                Type::FieldElement,
                                UExpression::identifier("K".into()).annotate(UBitwidth::B32)
                                    + 1u32.into(),
                            ))
                            .into()],
                        )
                        .annotate(ArrayType::new(
                            Type::FieldElement,
                            UExpression::identifier("K".into()).annotate(UBitwidth::B32)
                                + 1u32.into(),
                        )),
                        0u32.into(),
                        UExpression::identifier("K".into()).annotate(UBitwidth::B32),
                    )
                    .into(),
                ),
                TypedStatement::ret(
                    ArrayExpression::identifier("ret".into())
                        .annotate(ArrayType::new(
                            Type::FieldElement,
                            UExpression::identifier("K".into()).annotate(UBitwidth::B32),
                        ))
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
            statements: vec![TypedStatement::ret(
                ArrayExpression::identifier("a".into())
                    .annotate(ArrayType::new(
                        Type::FieldElement,
                        UExpression::identifier("K".into()).annotate(UBitwidth::B32),
                    ))
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
                        vec![ArrayExpression::value(vec![FieldElementExpression::value(
                            Bn128Field::from(1),
                        )
                        .into()])
                        .annotate(ArrayType::new(Type::FieldElement, 1u32))
                        .into()],
                    )
                    .annotate(ArrayType::new(Type::FieldElement, 1u32))
                    .into(),
                ),
                TypedStatement::ret(
                    TupleExpression::value(vec![])
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
            module_map: Default::default(),
        };

        let reduced = reduce_program(p);

        let expected_main = TypedFunction {
            arguments: vec![],
            statements: vec![TypedStatement::ret(
                TupleExpression::value(vec![])
                    .annotate(TupleType::new(vec![]))
                    .into(),
            )],
            signature: DeclarationSignature::new(),
        };

        let expected = TypedProgram {
            module_map: Default::default(),
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
            statements: vec![TypedStatement::ret(
                ArrayExpression::identifier("a".into())
                    .annotate(ArrayType::new(Type::FieldElement, 1u32))
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
                        vec![ArrayExpression::value(vec![])
                            .annotate(ArrayType::new(Type::FieldElement, 0u32))
                            .into()],
                    )
                    .annotate(ArrayType::new(Type::FieldElement, 1u32))
                    .into(),
                ),
                TypedStatement::ret(
                    TupleExpression::value(vec![])
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
            module_map: Default::default(),
        };

        let reduced = reduce_program(p);

        assert_eq!(
            reduced,
            Err(Error::Incompatible("Call site `main/foo<_>(field[0]) -> field[1]` incompatible with declaration `main/foo<K>(field[K]) -> field[K]`".into()))
        );
    }
}
