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
use crate::typed_absy::result_folder::*;
use crate::typed_absy::CanonicalConstantIdentifier;
use crate::typed_absy::Folder;
use std::collections::HashMap;
use std::collections::VecDeque;

use crate::typed_absy::{
    ArrayExpressionInner, ArrayType, BlockExpression, CoreIdentifier, Expr, FunctionCall,
    FunctionCallExpression, FunctionCallOrExpression, Id, Identifier, OwnedTypedModuleId,
    TypedExpression, TypedExpressionList, TypedExpressionListInner, TypedFunction,
    TypedFunctionIterator, TypedFunctionSymbol, TypedProgram, TypedStatement, UExpression,
    UExpressionInner, Variable,
};

use zokrates_field::Field;

use self::constants_writer::ConstantsWriter;
use self::shallow_ssa::ShallowTransformer;

use crate::static_analysis::propagation::{Constants, Propagator};
use fallible_iterator::FallibleIterator;

use std::fmt;

const MAX_FOR_LOOP_SIZE: u128 = 2u128.pow(20);

// A map to register the canonical value of all constants. The values must be literals.
pub type ConstantDefinitions<'ast, T> =
    HashMap<CanonicalConstantIdentifier<'ast>, TypedExpression<'ast, T>>;

// An SSA version map, giving access to the latest version number for each identifier
pub type Versions<'ast> = HashMap<CoreIdentifier<'ast>, usize>;

// A container to represent whether more treatment must be applied to the function
#[derive(Debug, PartialEq)]
pub enum Output<U, V> {
    Complete(U),
    Incomplete(U, V),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Error {
    Incompatible(String),
    GenericsInMain,
    // TODO: give more details about what's blocking the progress
    NoProgress,
    LoopTooLarge(u128),
    ConstantReduction(String, OwnedTypedModuleId),
    Type(String),
}

impl std::error::Error for Error {}

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

#[derive(Debug, Default, Clone, PartialEq)]
struct Substitutions<'ast>(pub HashMap<CoreIdentifier<'ast>, HashMap<usize, usize>>);

impl<'ast> Substitutions<'ast> {
    // create an equivalent substitution map where all paths
    // are of length 1
    fn canonicalize(self) -> Self {
        Substitutions(
            self.0
                .into_iter()
                .map(|(id, sub)| (id, Self::canonicalize_sub(sub)))
                .collect(),
        )
    }

    // canonicalize substitutions for a given id
    fn canonicalize_sub(sub: HashMap<usize, usize>) -> HashMap<usize, usize> {
        fn add_to_cache(
            sub: &HashMap<usize, usize>,
            cache: HashMap<usize, usize>,
            k: usize,
        ) -> HashMap<usize, usize> {
            match cache.contains_key(&k) {
                // `k` is already in the cache, no changes to the cache
                true => cache,
                _ => match sub.get(&k) {
                    // `k` does not point to anything, no changes to the cache
                    None => cache,
                    // `k` points to some `v
                    Some(v) => {
                        // add `v` to the cache
                        let cache = add_to_cache(sub, cache, *v);
                        // `k` points to what `v` points to, or to `v`
                        let v = cache.get(v).cloned().unwrap_or(*v);
                        let mut cache = cache;
                        cache.insert(k, v);
                        cache
                    }
                },
            }
        }

        sub.keys()
            .fold(HashMap::new(), |cache, k| add_to_cache(&sub, cache, *k))
    }
}

struct Sub<'a, 'ast> {
    substitutions: &'a Substitutions<'ast>,
}

impl<'a, 'ast> Sub<'a, 'ast> {
    fn new(substitutions: &'a Substitutions<'ast>) -> Self {
        Self { substitutions }
    }
}

impl<'a, 'ast, T: Field> Folder<'ast, T> for Sub<'a, 'ast> {
    fn fold_name(&mut self, id: Identifier<'ast>) -> Identifier<'ast> {
        let version = self
            .substitutions
            .0
            .get(&id.id)
            .map(|sub| sub.get(&id.version).cloned().unwrap_or(id.version))
            .unwrap_or(id.version);
        id.version(version)
    }
}

fn register<'ast>(
    substitutions: &mut Substitutions<'ast>,
    substitute: &Versions<'ast>,
    with: &Versions<'ast>,
) {
    for (id, key, value) in substitute
        .iter()
        .filter_map(|(id, version)| with.get(id).map(|to| (id, version, to)))
        .filter(|(_, key, value)| key != value)
    {
        let sub = substitutions.0.entry(id.clone()).or_default();

        // redirect `k` to `v`, unless `v` is already redirected to `v0`, in which case we redirect to `v0`

        sub.insert(*key, *sub.get(value).unwrap_or(value));
    }
}

#[derive(Debug)]
struct Reducer<'ast, 'a, T> {
    complete_statement_buffer: Vec<TypedStatement<'ast, T>>,
    statement_buffer: Vec<TypedStatement<'ast, T>>,
    for_loop_versions: Vec<(Versions<'ast>, Versions<'ast>)>,
    for_loop_versions_after: Vec<(Versions<'ast>, Versions<'ast>)>,
    program: &'a TypedProgram<'ast, T>,
    versions: &'a mut Versions<'ast>,
    substitutions: &'a mut Substitutions<'ast>,
    // while this flag is true, we fill `complete_statement_buffer`
    // as soon as it's false, we fill `statement_buffer`
    send_to_complete_buffer: bool,
}

impl<'ast, 'a, T: Field> Reducer<'ast, 'a, T> {
    fn new(
        program: &'a TypedProgram<'ast, T>,
        versions: &'a mut Versions<'ast>,
        substitutions: &'a mut Substitutions<'ast>,
        for_loop_versions: Vec<(Versions<'ast>, Versions<'ast>)>,
    ) -> Self {
        // we reverse the vector as it's cheaper to `pop` than to take from
        // the head
        let mut for_loop_versions = for_loop_versions;

        for_loop_versions.reverse();

        Reducer {
            complete_statement_buffer: vec![],
            statement_buffer: vec![],
            for_loop_versions_after: vec![],
            for_loop_versions,
            substitutions,
            program,
            versions,
            send_to_complete_buffer: true,
        }
    }
}

impl<'ast, 'a, T: Field> ResultFolder<'ast, T> for Reducer<'ast, 'a, T> {
    type Error = Error;

    fn fold_function_call_expression<
        E: Id<'ast, T> + From<TypedExpression<'ast, T>> + Expr<'ast, T> + FunctionCall<'ast, T>,
    >(
        &mut self,
        ty: &E::Ty,
        e: FunctionCallExpression<'ast, T, E>,
    ) -> Result<FunctionCallOrExpression<'ast, T, E>, Self::Error> {
        // if we reach a function call, we stop yielding statements
        self.send_to_complete_buffer = false;

        let generics = e
            .generics
            .into_iter()
            .map(|g| g.map(|g| self.fold_uint_expression(g)).transpose())
            .collect::<Result<_, _>>()?;

        let arguments = e
            .arguments
            .into_iter()
            .map(|e| self.fold_expression(e))
            .collect::<Result<_, _>>()?;

        let res = inline_call::<_, E>(
            e.function_key.clone(),
            generics,
            arguments,
            ty,
            self.program,
            self.versions,
        );

        match res {
            Ok(Output::Complete((statements, mut expressions))) => {
                self.statement_buffer.extend(statements);
                Ok(FunctionCallOrExpression::Expression(
                    E::from(expressions.pop().unwrap()).into_inner(),
                ))
            }
            Ok(Output::Incomplete((statements, expressions), delta_for_loop_versions)) => {
                self.statement_buffer.extend(statements);
                self.for_loop_versions_after.extend(delta_for_loop_versions);
                Ok(FunctionCallOrExpression::Expression(
                    E::from(expressions[0].clone()).into_inner(),
                ))
            }
            Err(InlineError::Generic(decl, conc)) => Err(Error::Incompatible(format!(
                "Call site `{}` incompatible with declaration `{}`",
                conc.to_string(),
                decl.to_string()
            ))),
            Err(InlineError::NonConstant(key, generics, arguments, _)) => Ok(
                FunctionCallOrExpression::Expression(E::function_call(key, generics, arguments)),
            ),
            Err(InlineError::Flat(embed, generics, arguments, output_types)) => {
                let identifier = Identifier::from(CoreIdentifier::Call(0)).version(
                    *self
                        .versions
                        .entry(CoreIdentifier::Call(0).clone())
                        .and_modify(|e| *e += 1) // if it was already declared, we increment
                        .or_insert(0),
                );
                let var = Variable::with_id_and_type(
                    identifier.clone(),
                    output_types.clone().inner.pop().unwrap(),
                );

                let v = vec![var.clone().into()];

                self.statement_buffer
                    .push(TypedStatement::MultipleDefinition(
                        v,
                        TypedExpressionListInner::EmbedCall(embed, generics, arguments)
                            .annotate(output_types),
                    ));
                Ok(FunctionCallOrExpression::Expression(E::identifier(
                    identifier,
                )))
            }
        }
    }

    fn fold_block_expression<E: ResultFold<'ast, T>>(
        &mut self,
        b: BlockExpression<'ast, T, E>,
    ) -> Result<BlockExpression<'ast, T, E>, Self::Error> {
        // backup the statements and continue with a fresh state
        let statement_buffer = std::mem::take(&mut self.statement_buffer);
        let complete_statement_buffer = std::mem::take(&mut self.complete_statement_buffer);

        let block = fold_block_expression(self, b)?;

        // put the original statements back and extract the statements created by visiting the block
        let extra_statements = std::mem::replace(&mut self.statement_buffer, statement_buffer);
        let extra_complete_statements = std::mem::replace(
            &mut self.complete_statement_buffer,
            complete_statement_buffer,
        );

        // return the visited block, augmented with the statements created while visiting it
        Ok(BlockExpression {
            statements: block
                .statements
                .into_iter()
                .chain(extra_complete_statements)
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

    fn fold_statement(
        &mut self,
        s: TypedStatement<'ast, T>,
    ) -> Result<Vec<TypedStatement<'ast, T>>, Self::Error> {
        let res = match s {
            m @ TypedStatement::MultipleDefinition(..) if !self.send_to_complete_buffer => {
                Ok(vec![m])
            }
            TypedStatement::MultipleDefinition(
                v,
                TypedExpressionList {
                    inner: TypedExpressionListInner::FunctionCall(function_call),
                    types,
                },
            ) => {
                let generics = function_call
                    .generics
                    .into_iter()
                    .map(|g| g.map(|g| self.fold_uint_expression(g)).transpose())
                    .collect::<Result<_, _>>()?;

                let arguments = function_call
                    .arguments
                    .into_iter()
                    .map(|a| self.fold_expression(a))
                    .collect::<Result<_, _>>()?;

                match inline_call::<_, TypedExpressionList<'ast, T>>(
                    function_call.function_key,
                    generics,
                    arguments,
                    &types,
                    self.program,
                    self.versions,
                ) {
                    Ok(Output::Complete((statements, expressions))) => {
                        assert_eq!(v.len(), expressions.len());

                        self.send_to_complete_buffer = false;

                        Ok(statements
                            .into_iter()
                            .chain(
                                v.into_iter()
                                    .zip(expressions)
                                    .map(|(v, e)| TypedStatement::Definition(v, e)),
                            )
                            .collect())
                    }
                    Ok(Output::Incomplete((statements, expressions), delta_for_loop_versions)) => {
                        assert_eq!(v.len(), expressions.len());

                        self.send_to_complete_buffer = false;
                        self.for_loop_versions_after.extend(delta_for_loop_versions);

                        Ok(statements
                            .into_iter()
                            .chain(
                                v.into_iter()
                                    .zip(expressions)
                                    .map(|(v, e)| TypedStatement::Definition(v, e)),
                            )
                            .collect())
                    }
                    Err(InlineError::Generic(decl, conc)) => Err(Error::Incompatible(format!(
                        "Call site `{}` incompatible with declaration `{}`",
                        conc.to_string(),
                        decl.to_string()
                    ))),
                    Err(InlineError::NonConstant(key, generics, arguments, output_types)) => {
                        self.send_to_complete_buffer = false;

                        Ok(vec![TypedStatement::MultipleDefinition(
                            v,
                            TypedExpressionList::function_call(key, generics, arguments)
                                .annotate(output_types),
                        )])
                    }
                    Err(InlineError::Flat(embed, generics, arguments, output_types)) => {
                        self.complete_statement_buffer
                            .push(TypedStatement::MultipleDefinition(
                                v,
                                TypedExpressionListInner::EmbedCall(embed, generics, arguments)
                                    .annotate(output_types),
                            ));

                        Ok(vec![])
                    }
                }
            }
            f @ TypedStatement::For(..) if !self.send_to_complete_buffer => {
                let v = self.for_loop_versions.pop().unwrap();
                self.for_loop_versions_after.push(v);
                Ok(vec![f])
            }
            TypedStatement::For(v, from, to, statements) => {
                let (versions_before, versions_after) = self.for_loop_versions.pop().unwrap();

                match (from.as_inner(), to.as_inner()) {
                    (UExpressionInner::Value(from), UExpressionInner::Value(to))
                        if *from == *to =>
                    {
                        // we know the final versions of the variables after full unrolling of the loop
                        // the versions after the loop need to point to these, so we add to the substitutions
                        register(self.substitutions, &versions_after, &versions_before);
                        Ok(vec![])
                    }
                    (UExpressionInner::Value(from), UExpressionInner::Value(to)) => {
                        // get a fresh set of versions for all variables to use as a starting point inside the loop
                        self.versions.values_mut().for_each(|v| *v += 1);

                        // add this set of versions to the substitution, pointing to the versions before the loop
                        register(self.substitutions, self.versions, &versions_before);

                        let mut transformer = ShallowTransformer::with_versions(self.versions);

                        if to - from > MAX_FOR_LOOP_SIZE {
                            return Err(Error::LoopTooLarge(to.saturating_sub(*from)));
                        }

                        #[allow(clippy::needless_collect)]
                        let extracted_statements: Vec<_> =
                            std::iter::once(TypedStatement::Definition(
                                v.clone().into(),
                                UExpression::from(*from as u32).into(),
                            ))
                            .chain(statements.clone().into_iter())
                            .map(|s| transformer.fold_statement(s))
                            .flatten()
                            .collect();

                        let backups: Vec<_> = transformer
                            .for_loop_backups
                            .into_iter()
                            .map(|v| (v.clone(), v.into_iter().map(|(k, v)| (k, v + 1)).collect()))
                            .collect();

                        // we may have found new for loops when unrolling this one, which means new backed up versions
                        // we insert these in our backup list and update our cursor

                        self.for_loop_versions_after.extend(backups);
                        self.for_loop_versions_after
                            .push((self.versions.clone(), versions_after));

                        // if the ssa transform got blocked, the reduction is not complete
                        self.send_to_complete_buffer = false;

                        Ok(extracted_statements
                            .into_iter()
                            .chain(vec![TypedStatement::For(
                                v,
                                (*from as u32 + 1).into(),
                                (*to as u32).into(),
                                statements,
                            )])
                            .collect())
                    }
                    _ => {
                        let from = self.fold_uint_expression(from)?;
                        let to = self.fold_uint_expression(to)?;
                        self.send_to_complete_buffer = false;
                        self.for_loop_versions_after
                            .push((versions_before, versions_after));
                        Ok(vec![TypedStatement::For(v, from, to, statements)])
                    }
                }
            }
            s => {
                let statements = fold_statement(self, s)?;
                if self.send_to_complete_buffer {
                    self.complete_statement_buffer.extend(statements);
                    Ok(vec![])
                } else {
                    Ok(statements)
                }
            }
        };

        res.map(|res| self.statement_buffer.drain(..).chain(res).collect())
    }

    fn fold_array_expression_inner(
        &mut self,
        array_ty: &ArrayType<'ast, T>,
        e: ArrayExpressionInner<'ast, T>,
    ) -> Result<ArrayExpressionInner<'ast, T>, Self::Error> {
        match e {
            ArrayExpressionInner::Slice(box array, box from, box to) => {
                let array = self.fold_array_expression(array)?;
                let from = self.fold_uint_expression(from)?;
                let to = self.fold_uint_expression(to)?;

                match (from.as_inner(), to.as_inner()) {
                    (UExpressionInner::Value(..), UExpressionInner::Value(..)) => {
                        Ok(ArrayExpressionInner::Slice(box array, box from, box to))
                    }
                    _ => {
                        // if slice bounds are not constant, we need to propagate so we stop yielding
                        self.send_to_complete_buffer = false;
                        Ok(ArrayExpressionInner::Slice(box array, box from, box to))
                    }
                }
            }
            _ => fold_array_expression_inner(self, array_ty, e),
        }
    }
}

pub fn reduce_program<T: Field>(
    p: TypedProgram<T>,
) -> Result<TypedFunctionIterator<ReducerIterator<T>>, Error> {
    // inline all constants and replace them in the  program
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
        0 => Ok(TypedFunctionIterator {
            arguments: main_function.arguments.clone(),
            signature: main_function.signature.clone(),
            statements: ReducerIterator::new(main_function, p),
        }),
        _ => Err(Error::GenericsInMain),
    }
}

/// A state machine which yields statements while minimizing the statements in memory
/// We take the main function and add its statements to an output buffer, making sure to always apply a single expansion
/// per pass. An expansion is one function call inlining, or one single loop unrolling. As soon as we have reached an expansion
/// site, we go through the rest of the program without doing any more expansions.
/// After each pass, we yield all statements in the output buffer before applying another pass. This way, the size of the
/// program in memory here only ever increases by one function body or loop body
#[derive(Debug, PartialEq)]
pub struct ReducerIterator<'ast, T> {
    /// the original program, required in order to resolve function calls
    program: TypedProgram<'ast, T>,
    /// the current function, which gets updated as its statements are yielded
    function: TypedFunction<'ast, T>,
    /// a buffer of statements which are ready to be yielded
    output: VecDeque<TypedStatement<'ast, T>>,
    /// the current SSA version state
    versions: Versions<'ast>,
    /// the current constant expression state for propagation
    constants: Constants<'ast, T>,
    /// the hash of the program, in order to detect a fixed point
    hash: Option<u64>,
    /// a flag to keep track of whether the initial SSA reduction was applied
    first_ssa_done: bool,
    /// the state of the SSA versions before and after each for-loop
    new_for_loop_versions: Vec<(Versions<'ast>, Versions<'ast>)>,
    /// the state of the equivalence between SSA versions, to avoid creating many redefinition statements
    substitutions: Substitutions<'ast>,
}

impl<'ast, T> ReducerIterator<'ast, T> {
    pub fn new(function: TypedFunction<'ast, T>, program: TypedProgram<'ast, T>) -> Self {
        Self {
            program,
            function,
            output: Default::default(),
            versions: Default::default(),
            constants: Default::default(),
            hash: Default::default(),
            first_ssa_done: Default::default(),
            new_for_loop_versions: Default::default(),
            substitutions: Default::default(),
        }
    }
}

impl<'ast, T: Field> FallibleIterator for ReducerIterator<'ast, T> {
    type Item = TypedStatement<'ast, T>;
    type Error = Box<dyn std::error::Error>;

    fn next(&mut self) -> Result<Option<Self::Item>, Self::Error> {
        while self.output.is_empty() && !self.function.statements.is_empty() {
            if !self.first_ssa_done {
                match ShallowTransformer::transform(
                    self.function.clone(),
                    &Default::default(),
                    &mut self.versions,
                ) {
                    Output::Complete(mut f) => {
                        self.first_ssa_done = true;
                        self.output.extend(std::mem::take(&mut f.statements));
                        self.function = f;
                        break;
                    }
                    Output::Incomplete(new_f, new_for_loop_versions) => {
                        self.first_ssa_done = true;
                        self.function = new_f;
                        self.new_for_loop_versions = new_for_loop_versions;
                    }
                };
            }

            // run one round of the iteration process
            {
                self.substitutions = std::mem::take(&mut self.substitutions).canonicalize();

                let mut reducer = Reducer::new(
                    &self.program,
                    &mut self.versions,
                    &mut self.substitutions,
                    std::mem::take(&mut self.new_for_loop_versions),
                );

                let statements = std::mem::take(&mut self.function.statements);

                let new_f = TypedFunction {
                    statements: statements
                        .into_iter()
                        .map(|s| reducer.fold_statement(s))
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .flatten()
                        .collect(),
                    ..self.function.clone()
                };

                assert!(reducer.for_loop_versions.is_empty());
                self.output.extend(reducer.complete_statement_buffer);

                self.new_for_loop_versions = reducer.for_loop_versions_after;

                let mut sub = Sub::new(&self.substitutions);
                let mut prop = Propagator::with_constants(std::mem::take(&mut self.constants));

                self.output = std::mem::take(&mut self.output)
                    .into_iter()
                    .flat_map(|s| sub.fold_statement(s))
                    .map(|s| prop.fold_statement(s))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .flatten()
                    .collect();

                let new_f = sub.fold_function(new_f);

                self.function = prop
                    .fold_function(new_f)
                    .map_err(|e| Error::Incompatible(format!("{}", e)))?;

                self.constants = prop.constants;

                if self.output.is_empty() {
                    let new_hash = Some(compute_hash(&self.function));
                    if new_hash == self.hash {
                        return Err(Error::NoProgress.into());
                    } else {
                        self.hash = new_hash
                    }
                }
            }
        }
        Ok(self.output.pop_front())
    }
}

fn reduce_function_no_generics<'ast, T: Field>(
    f: TypedFunction<'ast, T>,
    program: &TypedProgram<'ast, T>,
) -> Result<TypedFunction<'ast, T>, ()> {
    let arguments = f.arguments.clone();
    let signature = f.signature.clone();

    let reducer_iterator = ReducerIterator::new(f, program.clone());

    let r = TypedFunctionIterator {
        arguments,
        signature,
        statements: reducer_iterator,
    };

    let f = r.collect().map_err(|_| ())?;

    Propagator::with_constants(Constants::default())
        .fold_function(f)
        .map_err(|_| ())
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
    use crate::typed_absy::types::{
        DeclarationConstant, DeclarationSignature, GGenericsAssignment,
    };
    use crate::typed_absy::{
        ArrayExpression, ArrayExpressionInner, DeclarationFunctionKey, DeclarationType,
        DeclarationVariable, FieldElementExpression, GenericIdentifier, Identifier,
        OwnedTypedModuleId, Select, Type, TypedExpression, TypedExpressionList,
        TypedExpressionOrSpread, TypedFunctionSymbolDeclaration, TypedModule, Types, UBitwidth,
        UExpressionInner, Variable,
    };
    use zokrates_field::Bn128Field;

    use lazy_static::lazy_static;

    lazy_static! {
        static ref MAIN_MODULE_ID: OwnedTypedModuleId = OwnedTypedModuleId::from("main");
    }

    #[test]
    fn no_generics() {
        // def foo(field a) -> field:
        //      return a
        // def main(field a) -> field:
        //      u32 n = 42
        //      n = n
        //      a = a
        //      a = foo(a)
        //      n = n
        //      return a

        // expected:
        // def main(field a_0) -> field:
        //      a_1 = a_0
        //      # PUSH CALL to foo
        //          a_3 := a_1 // input binding
        //          #RETURN_AT_INDEX_0_0 := a_3
        //      # POP CALL
        //      a_2 = #RETURN_AT_INDEX_0_0
        //      return a_2

        let foo: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![DeclarationVariable::field_element("a").into()],
            statements: vec![TypedStatement::Return(vec![
                FieldElementExpression::Identifier("a".into()).into(),
            ])]
            .into(),
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![DeclarationVariable::field_element("a").into()],
            statements: vec![
                TypedStatement::Definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    TypedExpression::Uint(42u32.into()),
                ),
                TypedStatement::Definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    UExpressionInner::Identifier("n".into())
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::Definition(
                    Variable::field_element("a").into(),
                    FieldElementExpression::Identifier("a".into()).into(),
                ),
                TypedStatement::MultipleDefinition(
                    vec![Variable::field_element("a").into()],
                    TypedExpressionList::function_call(
                        DeclarationFunctionKey::with_location("main", "foo").signature(
                            DeclarationSignature::new()
                                .inputs(vec![DeclarationType::FieldElement])
                                .outputs(vec![DeclarationType::FieldElement]),
                        ),
                        vec![],
                        vec![FieldElementExpression::Identifier("a".into()).into()],
                    )
                    .annotate(Types::new(vec![Type::FieldElement])),
                ),
                TypedStatement::Definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    UExpressionInner::Identifier("n".into())
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::Return(vec![FieldElementExpression::Identifier("a".into()).into()]),
            ]
            .into(),
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .outputs(vec![DeclarationType::FieldElement]),
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
                                    .outputs(vec![DeclarationType::FieldElement]),
                            ),
                            TypedFunctionSymbol::Here(foo),
                        )
                        .into(),
                        TypedFunctionSymbolDeclaration::new(
                            DeclarationFunctionKey::with_location("main", "main").signature(
                                DeclarationSignature::new()
                                    .inputs(vec![DeclarationType::FieldElement])
                                    .outputs(vec![DeclarationType::FieldElement]),
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

        let expected = TypedFunction {
            arguments: vec![DeclarationVariable::field_element("a").into()],
            statements: vec![
                TypedStatement::Definition(
                    Variable::field_element(Identifier::from("a").version(1)).into(),
                    FieldElementExpression::Identifier("a".into()).into(),
                ),
                TypedStatement::PushCallLog(
                    DeclarationFunctionKey::with_location("main", "foo").signature(
                        DeclarationSignature::new()
                            .inputs(vec![DeclarationType::FieldElement])
                            .outputs(vec![DeclarationType::FieldElement]),
                    ),
                    GGenericsAssignment::default(),
                ),
                TypedStatement::Definition(
                    Variable::field_element(Identifier::from("a").version(3)).into(),
                    FieldElementExpression::Identifier(Identifier::from("a").version(1)).into(),
                ),
                TypedStatement::Definition(
                    Variable::field_element(Identifier::from(CoreIdentifier::Call(0)).version(0))
                        .into(),
                    FieldElementExpression::Identifier(Identifier::from("a").version(3)).into(),
                ),
                TypedStatement::PopCallLog,
                TypedStatement::Definition(
                    Variable::field_element(Identifier::from("a").version(2)).into(),
                    FieldElementExpression::Identifier(
                        Identifier::from(CoreIdentifier::Call(0)).version(0),
                    )
                    .into(),
                ),
                TypedStatement::Return(vec![FieldElementExpression::Identifier(
                    Identifier::from("a").version(2),
                )
                .into()]),
            ]
            .into(),
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        assert_eq!(reduced.unwrap().collect().unwrap(), expected);
    }

    #[test]
    fn with_generics() {
        // def foo<K>(field[K] a) -> field[K]:
        //      return a
        // def main(field a) -> field:
        //      u32 n = 42
        //      n = n
        //      field[1] b = [a]
        //      b = foo(b)
        //      n = n
        //      return a + b[0]

        // expected:
        // def main(field a_0) -> field:
        //      field[1] b_0 = [42]
        //      # PUSH CALL to foo::<1>
        //          a_0 = b_0
        //          #RETURN_AT_INDEX_0_0 := a_0
        //      # POP CALL
        //      b_1 = #RETURN_AT_INDEX_0_0
        //      return a_2 + b_1[0]

        let foo_signature = DeclarationSignature::new()
            .generics(vec![Some(
                GenericIdentifier::with_name("K").with_index(0).into(),
            )])
            .inputs(vec![DeclarationType::array((
                DeclarationType::FieldElement,
                DeclarationConstant::Generic(GenericIdentifier::with_name("K").with_index(0)),
            ))])
            .outputs(vec![DeclarationType::array((
                DeclarationType::FieldElement,
                DeclarationConstant::Generic(GenericIdentifier::with_name("K").with_index(0)),
            ))]);

        let foo: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![DeclarationVariable::array(
                "a",
                DeclarationType::FieldElement,
                GenericIdentifier::with_name("K").with_index(0),
            )
            .into()],
            statements: vec![TypedStatement::Return(vec![
                ArrayExpressionInner::Identifier("a".into())
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
            ])]
            .into(),
            signature: foo_signature.clone(),
        };

        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![DeclarationVariable::field_element("a").into()],
            statements: vec![
                TypedStatement::Definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    TypedExpression::Uint(42u32.into()),
                ),
                TypedStatement::Definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    UExpressionInner::Identifier("n".into())
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::Definition(
                    Variable::array("b", Type::FieldElement, 1u32).into(),
                    ArrayExpressionInner::Value(
                        vec![FieldElementExpression::Identifier("a".into()).into()].into(),
                    )
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
                ),
                TypedStatement::MultipleDefinition(
                    vec![Variable::array("b", Type::FieldElement, 1u32).into()],
                    TypedExpressionList::function_call(
                        DeclarationFunctionKey::with_location("main", "foo")
                            .signature(foo_signature.clone()),
                        vec![None],
                        vec![ArrayExpressionInner::Identifier("b".into())
                            .annotate(Type::FieldElement, 1u32)
                            .into()],
                    )
                    .annotate(Types::new(vec![Type::array((Type::FieldElement, 1u32))])),
                ),
                TypedStatement::Definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    UExpressionInner::Identifier("n".into())
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::Return(vec![(FieldElementExpression::Identifier("a".into())
                    + FieldElementExpression::select(
                        ArrayExpressionInner::Identifier("b".into())
                            .annotate(Type::FieldElement, 1u32),
                        0u32,
                    ))
                .into()]),
            ]
            .into(),
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .outputs(vec![DeclarationType::FieldElement]),
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
                                    .outputs(vec![DeclarationType::FieldElement]),
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

        let expected = TypedFunction {
            arguments: vec![DeclarationVariable::field_element("a").into()],
            statements: vec![
                TypedStatement::Definition(
                    Variable::array("b", Type::FieldElement, 1u32).into(),
                    ArrayExpressionInner::Value(
                        vec![FieldElementExpression::Identifier("a".into()).into()].into(),
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
                TypedStatement::Definition(
                    Variable::array(Identifier::from("a").version(1), Type::FieldElement, 1u32)
                        .into(),
                    ArrayExpressionInner::Identifier("b".into())
                        .annotate(Type::FieldElement, 1u32)
                        .into(),
                ),
                TypedStatement::Definition(
                    Variable::array(
                        Identifier::from(CoreIdentifier::Call(0)).version(0),
                        Type::FieldElement,
                        1u32,
                    )
                    .into(),
                    ArrayExpressionInner::Identifier(Identifier::from("a").version(1))
                        .annotate(Type::FieldElement, 1u32)
                        .into(),
                ),
                TypedStatement::PopCallLog,
                TypedStatement::Definition(
                    Variable::array(Identifier::from("b").version(1), Type::FieldElement, 1u32)
                        .into(),
                    ArrayExpressionInner::Identifier(
                        Identifier::from(CoreIdentifier::Call(0)).version(0),
                    )
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
                ),
                TypedStatement::Return(vec![(FieldElementExpression::Identifier("a".into())
                    + FieldElementExpression::select(
                        ArrayExpressionInner::Identifier(Identifier::from("b").version(1))
                            .annotate(Type::FieldElement, 1u32),
                        0u32,
                    ))
                .into()]),
            ]
            .into(),
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        assert_eq!(reduced.unwrap().collect().unwrap(), expected);
    }

    #[test]
    fn with_generics_and_propagation() {
        // def foo<K>(field[K] a) -> field[K]:
        //      return a
        // def main(field a) -> field:
        //      u32 n = 2
        //      n = n
        //      field[n - 1] b = [a]
        //      b = foo(b)
        //      n = n
        //      return a + b[0]

        // expected:
        // def main(field a_0) -> field:
        //      field[1] b_0 = [42]
        //      # PUSH CALL to foo::<1>
        //          a_0 = b_0
        //          #RETURN_AT_INDEX_0_0 := a_0
        //      # POP CALL
        //      b_1 = #RETURN_AT_INDEX_0_0
        //      return a_2 + b_1[0]

        let foo_signature = DeclarationSignature::new()
            .generics(vec![Some(
                GenericIdentifier::with_name("K").with_index(0).into(),
            )])
            .inputs(vec![DeclarationType::array((
                DeclarationType::FieldElement,
                DeclarationConstant::Generic(GenericIdentifier::with_name("K").with_index(0)),
            ))])
            .outputs(vec![DeclarationType::array((
                DeclarationType::FieldElement,
                DeclarationConstant::Generic(GenericIdentifier::with_name("K").with_index(0)),
            ))]);

        let foo: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![DeclarationVariable::array(
                "a",
                DeclarationType::FieldElement,
                GenericIdentifier::with_name("K").with_index(0),
            )
            .into()],
            statements: vec![TypedStatement::Return(vec![
                ArrayExpressionInner::Identifier("a".into())
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
            ])]
            .into(),
            signature: foo_signature.clone(),
        };

        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![DeclarationVariable::field_element("a").into()],
            statements: vec![
                TypedStatement::Definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    TypedExpression::Uint(2u32.into()),
                ),
                TypedStatement::Definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    UExpressionInner::Identifier("n".into())
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::Definition(
                    Variable::array(
                        "b",
                        Type::FieldElement,
                        UExpressionInner::Sub(
                            box UExpressionInner::Identifier("n".into()).annotate(UBitwidth::B32),
                            box 1u32.into(),
                        )
                        .annotate(UBitwidth::B32),
                    )
                    .into(),
                    ArrayExpressionInner::Value(
                        vec![FieldElementExpression::Identifier("a".into()).into()].into(),
                    )
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
                ),
                TypedStatement::MultipleDefinition(
                    vec![Variable::array("b", Type::FieldElement, 1u32).into()],
                    TypedExpressionList::function_call(
                        DeclarationFunctionKey::with_location("main", "foo")
                            .signature(foo_signature.clone()),
                        vec![None],
                        vec![ArrayExpressionInner::Identifier("b".into())
                            .annotate(Type::FieldElement, 1u32)
                            .into()],
                    )
                    .annotate(Types::new(vec![Type::array((Type::FieldElement, 1u32))])),
                ),
                TypedStatement::Definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    UExpressionInner::Identifier("n".into())
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::Return(vec![(FieldElementExpression::Identifier("a".into())
                    + FieldElementExpression::select(
                        ArrayExpressionInner::Identifier("b".into())
                            .annotate(Type::FieldElement, 1u32),
                        0u32,
                    ))
                .into()]),
            ]
            .into(),
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .outputs(vec![DeclarationType::FieldElement]),
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
                                    .outputs(vec![DeclarationType::FieldElement]),
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

        let expected = TypedFunction {
            arguments: vec![DeclarationVariable::field_element("a").into()],
            statements: vec![
                TypedStatement::Definition(
                    Variable::array("b", Type::FieldElement, 1u32).into(),
                    ArrayExpressionInner::Value(
                        vec![FieldElementExpression::Identifier("a".into()).into()].into(),
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
                TypedStatement::Definition(
                    Variable::array(Identifier::from("a").version(1), Type::FieldElement, 1u32)
                        .into(),
                    ArrayExpressionInner::Identifier("b".into())
                        .annotate(Type::FieldElement, 1u32)
                        .into(),
                ),
                TypedStatement::Definition(
                    Variable::array(
                        Identifier::from(CoreIdentifier::Call(0)).version(0),
                        Type::FieldElement,
                        1u32,
                    )
                    .into(),
                    ArrayExpressionInner::Identifier(Identifier::from("a").version(1))
                        .annotate(Type::FieldElement, 1u32)
                        .into(),
                ),
                TypedStatement::PopCallLog,
                TypedStatement::Definition(
                    Variable::array(Identifier::from("b").version(1), Type::FieldElement, 1u32)
                        .into(),
                    ArrayExpressionInner::Identifier(
                        Identifier::from(CoreIdentifier::Call(0)).version(0),
                    )
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
                ),
                TypedStatement::Return(vec![(FieldElementExpression::Identifier("a".into())
                    + FieldElementExpression::select(
                        ArrayExpressionInner::Identifier(Identifier::from("b").version(1))
                            .annotate(Type::FieldElement, 1u32),
                        0u32,
                    ))
                .into()]),
            ]
            .into(),
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        assert_eq!(reduced.unwrap().collect().unwrap(), expected);
    }

    #[test]
    fn call_in_call() {
        // we use a global ssa counter, hence reusing variable names in called functions
        // leads to counter increase

        // def bar<K>(field[K] a) -> field[K]:
        //      return a

        // def foo<K>(field[K] a) -> field[K]:
        //      field[K] ret = bar([...a, 0])[0..K]
        //      return ret

        // def main():
        //      field[1] b = foo([1])
        //      return

        // expected:
        // def main():
        //      # PUSH CALL to foo::<1>
        //          # PUSH CALL to bar::<2>
        //          # POP CALL
        //      # POP CALL
        //      return

        let foo_signature = DeclarationSignature::new()
            .inputs(vec![DeclarationType::array((
                DeclarationType::FieldElement,
                DeclarationConstant::Generic(GenericIdentifier::with_name("K").with_index(0)),
            ))])
            .outputs(vec![DeclarationType::array((
                DeclarationType::FieldElement,
                DeclarationConstant::Generic(GenericIdentifier::with_name("K").with_index(0)),
            ))])
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
                TypedStatement::Definition(
                    Variable::array(
                        "ret",
                        Type::FieldElement,
                        UExpressionInner::Identifier("K".into()).annotate(UBitwidth::B32),
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
                                        ArrayExpressionInner::Identifier("a".into())
                                            .annotate(Type::FieldElement, 1u32)
                                            .into(),
                                    ),
                                    FieldElementExpression::Number(Bn128Field::from(0)).into(),
                                ]
                                .into(),
                            )
                            .annotate(
                                Type::FieldElement,
                                UExpressionInner::Identifier("K".into()).annotate(UBitwidth::B32)
                                    + 1u32.into(),
                            )
                            .into()],
                        )
                        .annotate(
                            Type::FieldElement,
                            UExpressionInner::Identifier("K".into()).annotate(UBitwidth::B32)
                                + 1u32.into(),
                        ),
                        box 0u32.into(),
                        box UExpressionInner::Identifier("K".into()).annotate(UBitwidth::B32),
                    )
                    .annotate(
                        Type::FieldElement,
                        UExpressionInner::Identifier("K".into()).annotate(UBitwidth::B32),
                    )
                    .into(),
                ),
                TypedStatement::Return(vec![ArrayExpressionInner::Identifier("ret".into())
                    .annotate(
                        Type::FieldElement,
                        UExpressionInner::Identifier("K".into()).annotate(UBitwidth::B32),
                    )
                    .into()]),
            ]
            .into(),
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
            statements: vec![TypedStatement::Return(vec![
                ArrayExpressionInner::Identifier("a".into())
                    .annotate(
                        Type::FieldElement,
                        UExpressionInner::Identifier("K".into()).annotate(UBitwidth::B32),
                    )
                    .into(),
            ])]
            .into(),
            signature: bar_signature.clone(),
        };

        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![],
            statements: vec![
                TypedStatement::MultipleDefinition(
                    vec![Variable::array("b", Type::FieldElement, 1u32).into()],
                    TypedExpressionList::function_call(
                        DeclarationFunctionKey::with_location("main", "foo")
                            .signature(foo_signature.clone()),
                        vec![None],
                        vec![ArrayExpressionInner::Value(
                            vec![FieldElementExpression::Number(Bn128Field::from(1)).into()].into(),
                        )
                        .annotate(Type::FieldElement, 1u32)
                        .into()],
                    )
                    .annotate(Types::new(vec![Type::array((Type::FieldElement, 1u32))])),
                ),
                TypedStatement::Return(vec![]),
            ]
            .into(),
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

        let expected = TypedFunction {
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
                TypedStatement::Return(vec![]),
            ]
            .into(),
            signature: DeclarationSignature::new(),
        };

        assert_eq!(reduced.unwrap().collect().unwrap(), expected);
    }

    #[test]
    fn incompatible() {
        // def foo<K>(field[K] a) -> field[K]:
        //      return a
        // def main():
        //      field[1] b = foo([])
        //      return

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
            .outputs(vec![DeclarationType::array((
                DeclarationType::FieldElement,
                GenericIdentifier::with_name("K").with_index(0),
            ))]);

        let foo: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![DeclarationVariable::array(
                "a",
                DeclarationType::FieldElement,
                GenericIdentifier::with_name("K").with_index(0),
            )
            .into()],
            statements: vec![TypedStatement::Return(vec![
                ArrayExpressionInner::Identifier("a".into())
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
            ])]
            .into(),
            signature: foo_signature.clone(),
        };

        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![],
            statements: vec![
                TypedStatement::MultipleDefinition(
                    vec![Variable::array("b", Type::FieldElement, 1u32).into()],
                    TypedExpressionList::function_call(
                        DeclarationFunctionKey::with_location("main", "foo")
                            .signature(foo_signature.clone()),
                        vec![None],
                        vec![ArrayExpressionInner::Value(vec![].into())
                            .annotate(Type::FieldElement, 0u32)
                            .into()],
                    )
                    .annotate(Types::new(vec![Type::array((Type::FieldElement, 1u32))])),
                ),
                TypedStatement::Return(vec![]),
            ]
            .into(),
            signature: DeclarationSignature::new().inputs(vec![]).outputs(vec![]),
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
                                DeclarationSignature::new().inputs(vec![]).outputs(vec![]),
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

        let reduced = reduce_program(p)
            .unwrap()
            .collect()
            .unwrap_err()
            .to_string();

        assert_eq!(
            reduced,
            "Call site `main/foo<_>(field[0]) -> field[1]` incompatible with declaration `main/foo<K>(field[K]) -> field[K]`"
        );
    }
}
