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

mod inline;
mod shallow_ssa;

use self::inline::{inline_call, InlineError};
use crate::typed_absy::result_folder::*;
use crate::typed_absy::types::ConcreteGenericsAssignment;
use crate::typed_absy::types::GGenericsAssignment;
use crate::typed_absy::Folder;
use std::collections::HashMap;

use crate::typed_absy::{
    ArrayExpression, ArrayExpressionInner, ArrayType, BooleanExpression, CoreIdentifier,
    DeclarationFunctionKey, FieldElementExpression, FunctionCall, Identifier, StructExpression,
    StructExpressionInner, Type, Typed, TypedExpression, TypedExpressionList, TypedFunction,
    TypedFunctionSymbol, TypedModule, TypedProgram, TypedStatement, UExpression, UExpressionInner,
    Variable,
};

use std::convert::{TryFrom, TryInto};

use zokrates_field::Field;

use self::shallow_ssa::ShallowTransformer;

use crate::static_analysis::Propagator;

use std::fmt;

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
            Error::NoProgress => write!(f, "Failed to unroll or inline program. Check that main function arguments aren't used as array size or for-loop bounds")
        }
    }
}

#[derive(Debug, Default)]
struct Substitutions<'ast>(HashMap<CoreIdentifier<'ast>, HashMap<usize, usize>>);

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
        .filter_map(|(id, version)| with.get(&id).clone().map(|to| (id, version, to)))
        .filter(|(_, key, value)| key != value)
    {
        let sub = substitutions.0.entry(id.clone()).or_default();

        // redirect `k` to `v`, unless `v` is already redirected to `v0`, in which case we redirect to `v0`

        sub.insert(*key, *sub.get(value).unwrap_or(value));
    }
}

struct Reducer<'ast, 'a, T> {
    statement_buffer: Vec<TypedStatement<'ast, T>>,
    for_loop_versions: Vec<Versions<'ast>>,
    for_loop_versions_after: Vec<Versions<'ast>>,
    program: &'a TypedProgram<'ast, T>,
    versions: &'a mut Versions<'ast>,
    substitutions: &'a mut Substitutions<'ast>,
    complete: bool,
}

impl<'ast, 'a, T: Field> Reducer<'ast, 'a, T> {
    fn new(
        program: &'a TypedProgram<'ast, T>,
        versions: &'a mut Versions<'ast>,
        substitutions: &'a mut Substitutions<'ast>,
        for_loop_versions: Vec<Versions<'ast>>,
    ) -> Self {
        // we reverse the vector as it's cheaper to `pop` than to take from
        // the head
        let mut for_loop_versions = for_loop_versions;

        for_loop_versions.reverse();

        Reducer {
            statement_buffer: vec![],
            for_loop_versions_after: vec![],
            for_loop_versions,
            substitutions,
            program,
            versions,
            complete: true,
        }
    }

    fn fold_function_call<E>(
        &mut self,
        key: DeclarationFunctionKey<'ast>,
        generics: Vec<Option<UExpression<'ast, T>>>,
        arguments: Vec<TypedExpression<'ast, T>>,
        output_types: Vec<Type<'ast, T>>,
    ) -> Result<E, Error>
    where
        E: FunctionCall<'ast, T> + TryFrom<TypedExpression<'ast, T>, Error = ()> + std::fmt::Debug,
    {
        let generics = generics
            .into_iter()
            .map(|g| g.map(|g| self.fold_uint_expression(g)).transpose())
            .collect::<Result<_, _>>()?;

        let arguments = arguments
            .into_iter()
            .map(|e| self.fold_expression(e))
            .collect::<Result<_, _>>()?;

        let res = inline_call(
            key.clone(),
            generics,
            arguments,
            output_types,
            &self.program,
            &mut self.versions,
        );

        match res {
            Ok(Output::Complete((statements, expressions))) => {
                self.complete &= true;
                self.statement_buffer.extend(statements);
                Ok(expressions[0].clone().try_into().unwrap())
            }
            Ok(Output::Incomplete((statements, expressions), delta_for_loop_versions)) => {
                self.complete = false;
                self.statement_buffer.extend(statements);
                self.for_loop_versions_after.extend(delta_for_loop_versions);
                Ok(expressions[0].clone().try_into().unwrap())
            }
            Err(InlineError::Generic(decl, conc)) => Err(Error::Incompatible(format!(
                "Call site `{}` incompatible with declaration `{}`",
                conc.to_string(),
                decl.to_string()
            ))),
            Err(InlineError::NonConstant(key, generics, arguments, mut output_types)) => {
                self.complete = false;

                Ok(E::function_call(
                    key,
                    generics,
                    arguments,
                    output_types.pop().unwrap(),
                ))
            }
            Err(InlineError::Flat(embed, generics, arguments, output_types)) => {
                let identifier = Identifier::from(CoreIdentifier::Call(0)).version(
                    *self
                        .versions
                        .entry(CoreIdentifier::Call(0).clone())
                        .and_modify(|e| *e += 1) // if it was already declared, we increment
                        .or_insert(0),
                );
                let var = Variable::with_id_and_type(identifier, output_types[0].clone());

                let v = vec![var.clone().into()];

                self.statement_buffer
                    .push(TypedStatement::MultipleDefinition(
                        v,
                        TypedExpressionList::EmbedCall(embed, generics, arguments, output_types),
                    ));
                Ok(TypedExpression::from(var).try_into().unwrap())
            }
        }
    }
}

impl<'ast, 'a, T: Field> ResultFolder<'ast, T> for Reducer<'ast, 'a, T> {
    type Error = Error;

    fn fold_statement(
        &mut self,
        s: TypedStatement<'ast, T>,
    ) -> Result<Vec<TypedStatement<'ast, T>>, Self::Error> {
        let res = match s {
            TypedStatement::MultipleDefinition(
                v,
                TypedExpressionList::FunctionCall(key, generics, arguments, output_types),
            ) => {
                let generics = generics
                    .into_iter()
                    .map(|g| g.map(|g| self.fold_uint_expression(g)).transpose())
                    .collect::<Result<_, _>>()?;

                let arguments = arguments
                    .into_iter()
                    .map(|a| self.fold_expression(a))
                    .collect::<Result<_, _>>()?;

                match inline_call(
                    key,
                    generics,
                    arguments,
                    output_types,
                    &self.program,
                    &mut self.versions,
                ) {
                    Ok(Output::Complete((statements, expressions))) => {
                        assert_eq!(v.len(), expressions.len());

                        self.complete &= true;

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

                        self.complete = false;
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
                        self.complete = false;

                        Ok(vec![TypedStatement::MultipleDefinition(
                            v,
                            TypedExpressionList::FunctionCall(
                                key,
                                generics,
                                arguments,
                                output_types,
                            ),
                        )])
                    }
                    Err(InlineError::Flat(embed, generics, arguments, output_types)) => {
                        Ok(vec![TypedStatement::MultipleDefinition(
                            v,
                            TypedExpressionList::EmbedCall(
                                embed,
                                generics,
                                arguments,
                                output_types,
                            ),
                        )])
                    }
                }
            }
            TypedStatement::For(v, from, to, statements) => {
                let versions_before = self.for_loop_versions.pop().unwrap();

                match (from.as_inner(), to.as_inner()) {
                    (UExpressionInner::Value(from), UExpressionInner::Value(to)) => {
                        let mut out_statements = vec![];

                        // get a fresh set of versions for all variables to use as a starting point inside the loop
                        self.versions.values_mut().for_each(|v| *v += 1);

                        // add this set of versions to the substitution, pointing to the versions before the loop
                        register(&mut self.substitutions, &self.versions, &versions_before);

                        // the versions after the loop are found by applying an offset of 2 to the versions before the loop
                        let versions_after = versions_before
                            .clone()
                            .into_iter()
                            .map(|(k, v)| (k, v + 2))
                            .collect();

                        let mut transformer = ShallowTransformer::with_versions(&mut self.versions);

                        for index in *from..*to {
                            let statements: Vec<TypedStatement<_>> =
                                std::iter::once(TypedStatement::Definition(
                                    v.clone().into(),
                                    UExpression::from(index as u32).into(),
                                ))
                                .chain(statements.clone().into_iter())
                                .map(|s| transformer.fold_statement(s))
                                .flatten()
                                .collect();

                            out_statements.extend(statements);
                        }

                        let backups = transformer.for_loop_backups;
                        let blocked = transformer.blocked;

                        // we know the final versions of the variables after full unrolling of the loop
                        // the versions after the loop need to point to these, so we add to the substitutions
                        register(&mut self.substitutions, &versions_after, &self.versions);

                        // we may have found new for loops when unrolling this one, which means new backed up versions
                        // we insert these in our backup list and update our cursor

                        self.for_loop_versions_after.extend(backups);

                        // if the ssa transform got blocked, the reduction is not complete
                        self.complete &= !blocked;

                        Ok(out_statements)
                    }
                    _ => {
                        let from = self.fold_uint_expression(from)?;
                        let to = self.fold_uint_expression(to)?;
                        self.complete = false;
                        self.for_loop_versions_after.push(versions_before);
                        Ok(vec![TypedStatement::For(v, from, to, statements)])
                    }
                }
            }
            s => fold_statement(self, s),
        };

        res.map(|res| self.statement_buffer.drain(..).chain(res).collect())
    }

    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> Result<BooleanExpression<'ast, T>, Self::Error> {
        match e {
            BooleanExpression::FunctionCall(key, generics, arguments) => {
                self.fold_function_call(key, generics, arguments, vec![Type::Boolean])
            }
            e => fold_boolean_expression(self, e),
        }
    }

    fn fold_uint_expression(
        &mut self,
        e: UExpression<'ast, T>,
    ) -> Result<UExpression<'ast, T>, Self::Error> {
        match e.as_inner() {
            UExpressionInner::FunctionCall(key, generics, arguments) => self.fold_function_call(
                key.clone(),
                generics.clone(),
                arguments.clone(),
                vec![e.get_type()],
            ),
            _ => fold_uint_expression(self, e),
        }
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> Result<FieldElementExpression<'ast, T>, Self::Error> {
        match e {
            FieldElementExpression::FunctionCall(key, generic, arguments) => {
                self.fold_function_call(key, generic, arguments, vec![Type::FieldElement])
            }
            e => fold_field_expression(self, e),
        }
    }

    fn fold_array_expression_inner(
        &mut self,
        ty: &ArrayType<'ast, T>,
        e: ArrayExpressionInner<'ast, T>,
    ) -> Result<ArrayExpressionInner<'ast, T>, Self::Error> {
        match e {
            ArrayExpressionInner::FunctionCall(key, generics, arguments) => self
                .fold_function_call::<ArrayExpression<_>>(
                    key.clone(),
                    generics,
                    arguments.clone(),
                    vec![Type::array(ty.clone())],
                )
                .map(|e| e.into_inner()),
            ArrayExpressionInner::Slice(box array, box from, box to) => {
                let array = self.fold_array_expression(array)?;
                let from = self.fold_uint_expression(from)?;
                let to = self.fold_uint_expression(to)?;

                match (from.as_inner(), to.as_inner()) {
                    (UExpressionInner::Value(..), UExpressionInner::Value(..)) => {
                        Ok(ArrayExpressionInner::Slice(box array, box from, box to))
                    }
                    _ => {
                        self.complete = false;
                        Ok(ArrayExpressionInner::Slice(box array, box from, box to))
                    }
                }
            }
            _ => fold_array_expression_inner(self, &ty, e),
        }
    }

    fn fold_struct_expression(
        &mut self,
        e: StructExpression<'ast, T>,
    ) -> Result<StructExpression<'ast, T>, Self::Error> {
        match e.as_inner() {
            StructExpressionInner::FunctionCall(key, generics, arguments) => self
                .fold_function_call(
                    key.clone(),
                    generics.clone(),
                    arguments.clone(),
                    vec![e.get_type()],
                ),
            _ => fold_struct_expression(self, e),
        }
    }
}

pub fn reduce_program<T: Field>(p: TypedProgram<T>) -> Result<TypedProgram<T>, Error> {
    let main_module = p.modules.get(&p.main).unwrap().clone();

    let (main_key, main_function) = main_module
        .functions
        .iter()
        .find(|(k, _)| k.id == "main")
        .unwrap();

    let main_function = match main_function {
        TypedFunctionSymbol::Here(f) => f.clone(),
        _ => unreachable!(),
    };

    match main_function.signature.generics.len() {
        0 => {
            let main_function = reduce_function(main_function, GGenericsAssignment::default(), &p)?;

            Ok(TypedProgram {
                main: p.main.clone(),
                modules: vec![(
                    p.main.clone(),
                    TypedModule {
                        functions: vec![(
                            main_key.clone(),
                            TypedFunctionSymbol::Here(main_function),
                        )]
                        .into_iter()
                        .collect(),
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
    generics: ConcreteGenericsAssignment<'ast>,
    program: &TypedProgram<'ast, T>,
) -> Result<TypedFunction<'ast, T>, Error> {
    let mut versions = Versions::default();

    match ShallowTransformer::transform(f, &generics, &mut versions) {
        Output::Complete(f) => Ok(f),
        Output::Incomplete(new_f, new_for_loop_versions) => {
            let mut for_loop_versions = new_for_loop_versions;

            let mut f = new_f;

            let mut substitutions = Substitutions::default();

            let mut constants: HashMap<Identifier<'ast>, TypedExpression<'ast, T>> = HashMap::new();

            let mut hash = None;

            loop {
                let mut reducer = Reducer::new(
                    &program,
                    &mut versions,
                    &mut substitutions,
                    for_loop_versions,
                );

                let new_f = TypedFunction {
                    statements: f
                        .statements
                        .into_iter()
                        .map(|s| reducer.fold_statement(s))
                        .collect::<Result<Vec<_>, _>>()?
                        .into_iter()
                        .flatten()
                        .collect(),
                    ..f
                };

                assert!(reducer.for_loop_versions.is_empty());

                match reducer.complete {
                    true => {
                        substitutions = substitutions.canonicalize();

                        let new_f = Sub::new(&substitutions).fold_function(new_f);

                        let new_f = Propagator::with_constants(&mut constants)
                            .fold_function(new_f)
                            .map_err(|e| match e {
                                crate::static_analysis::propagation::Error::Type(e) => {
                                    Error::Incompatible(e)
                                }
                            })?;

                        break Ok(new_f);
                    }
                    false => {
                        for_loop_versions = reducer.for_loop_versions_after;

                        let new_f = Sub::new(&substitutions).fold_function(new_f);

                        f = Propagator::with_constants(&mut constants)
                            .fold_function(new_f)
                            .map_err(|e| match e {
                                crate::static_analysis::propagation::Error::Type(e) => {
                                    Error::Incompatible(e)
                                }
                            })?;

                        let new_hash = Some(compute_hash(&f));

                        if new_hash == hash {
                            break Err(Error::NoProgress);
                        } else {
                            hash = new_hash
                        }
                    }
                }
            }
        }
    }
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
    use crate::typed_absy::types::Constant;
    use crate::typed_absy::types::DeclarationSignature;
    use crate::typed_absy::{
        ArrayExpressionInner, DeclarationFunctionKey, DeclarationType, DeclarationVariable,
        FieldElementExpression, Identifier, OwnedTypedModuleId, Select, Type, TypedExpression,
        TypedExpressionList, TypedExpressionOrSpread, UBitwidth, UExpressionInner, Variable,
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
            ])],
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
                    TypedExpressionList::FunctionCall(
                        DeclarationFunctionKey::with_location("main", "foo").signature(
                            DeclarationSignature::new()
                                .inputs(vec![DeclarationType::FieldElement])
                                .outputs(vec![DeclarationType::FieldElement]),
                        ),
                        vec![],
                        vec![FieldElementExpression::Identifier("a".into()).into()],
                        vec![Type::FieldElement],
                    ),
                ),
                TypedStatement::Definition(
                    Variable::uint("n", UBitwidth::B32).into(),
                    UExpressionInner::Identifier("n".into())
                        .annotate(UBitwidth::B32)
                        .into(),
                ),
                TypedStatement::Return(vec![FieldElementExpression::Identifier("a".into()).into()]),
            ],
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        let p = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![
                        (
                            DeclarationFunctionKey::with_location("main", "foo").signature(
                                DeclarationSignature::new()
                                    .inputs(vec![DeclarationType::FieldElement])
                                    .outputs(vec![DeclarationType::FieldElement]),
                            ),
                            TypedFunctionSymbol::Here(foo),
                        ),
                        (
                            DeclarationFunctionKey::with_location("main", "main").signature(
                                DeclarationSignature::new()
                                    .inputs(vec![DeclarationType::FieldElement])
                                    .outputs(vec![DeclarationType::FieldElement]),
                            ),
                            TypedFunctionSymbol::Here(main),
                        ),
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
        };

        let reduced = reduce_program(p);

        let expected_main = TypedFunction {
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
            ],
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        let expected: TypedProgram<Bn128Field> = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![(
                        DeclarationFunctionKey::with_location("main", "main").signature(
                            DeclarationSignature::new()
                                .inputs(vec![DeclarationType::FieldElement])
                                .outputs(vec![DeclarationType::FieldElement]),
                        ),
                        TypedFunctionSymbol::Here(expected_main),
                    )]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
        };

        assert_eq!(reduced.unwrap(), expected);
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
            .generics(vec![Some("K".into())])
            .inputs(vec![DeclarationType::array((
                DeclarationType::FieldElement,
                Constant::Generic("K"),
            ))])
            .outputs(vec![DeclarationType::array((
                DeclarationType::FieldElement,
                Constant::Generic("K"),
            ))]);

        let foo: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![
                DeclarationVariable::array("a", DeclarationType::FieldElement, "K").into(),
            ],
            statements: vec![TypedStatement::Return(vec![
                ArrayExpressionInner::Identifier("a".into())
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
            ])],
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
                    TypedExpressionList::FunctionCall(
                        DeclarationFunctionKey::with_location("main", "foo")
                            .signature(foo_signature.clone()),
                        vec![None],
                        vec![ArrayExpressionInner::Identifier("b".into())
                            .annotate(Type::FieldElement, 1u32)
                            .into()],
                        vec![Type::array((Type::FieldElement, 1u32))],
                    ),
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
            ],
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        let p = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![
                        (
                            DeclarationFunctionKey::with_location("main", "foo")
                                .signature(foo_signature.clone()),
                            TypedFunctionSymbol::Here(foo),
                        ),
                        (
                            DeclarationFunctionKey::with_location("main", "main").signature(
                                DeclarationSignature::new()
                                    .inputs(vec![DeclarationType::FieldElement])
                                    .outputs(vec![DeclarationType::FieldElement]),
                            ),
                            TypedFunctionSymbol::Here(main),
                        ),
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
        };

        let reduced = reduce_program(p);

        let expected_main = TypedFunction {
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
                    GGenericsAssignment(vec![("K", 1)].into_iter().collect()),
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
            ],
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        let expected = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![(
                        DeclarationFunctionKey::with_location("main", "main").signature(
                            DeclarationSignature::new()
                                .inputs(vec![DeclarationType::FieldElement])
                                .outputs(vec![DeclarationType::FieldElement]),
                        ),
                        TypedFunctionSymbol::Here(expected_main),
                    )]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
        };

        assert_eq!(reduced.unwrap(), expected);
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
            .generics(vec![Some("K".into())])
            .inputs(vec![DeclarationType::array((
                DeclarationType::FieldElement,
                Constant::Generic("K"),
            ))])
            .outputs(vec![DeclarationType::array((
                DeclarationType::FieldElement,
                Constant::Generic("K"),
            ))]);

        let foo: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![
                DeclarationVariable::array("a", DeclarationType::FieldElement, "K").into(),
            ],
            statements: vec![TypedStatement::Return(vec![
                ArrayExpressionInner::Identifier("a".into())
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
            ])],
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
                    TypedExpressionList::FunctionCall(
                        DeclarationFunctionKey::with_location("main", "foo")
                            .signature(foo_signature.clone()),
                        vec![None],
                        vec![ArrayExpressionInner::Identifier("b".into())
                            .annotate(Type::FieldElement, 1u32)
                            .into()],
                        vec![Type::array((Type::FieldElement, 1u32))],
                    ),
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
            ],
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        let p = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![
                        (
                            DeclarationFunctionKey::with_location("main", "foo")
                                .signature(foo_signature.clone()),
                            TypedFunctionSymbol::Here(foo),
                        ),
                        (
                            DeclarationFunctionKey::with_location("main", "main").signature(
                                DeclarationSignature::new()
                                    .inputs(vec![DeclarationType::FieldElement])
                                    .outputs(vec![DeclarationType::FieldElement]),
                            ),
                            TypedFunctionSymbol::Here(main),
                        ),
                    ]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
        };

        let reduced = reduce_program(p);

        let expected_main = TypedFunction {
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
                    GGenericsAssignment(vec![("K", 1)].into_iter().collect()),
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
            ],
            signature: DeclarationSignature::new()
                .inputs(vec![DeclarationType::FieldElement])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        let expected = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![(
                        DeclarationFunctionKey::with_location("main", "main").signature(
                            DeclarationSignature::new()
                                .inputs(vec![DeclarationType::FieldElement])
                                .outputs(vec![DeclarationType::FieldElement]),
                        ),
                        TypedFunctionSymbol::Here(expected_main),
                    )]
                    .into_iter()
                    .collect(),
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
        //              field[2] a_1 = [...[1]], 0]
        //              field[2] #RET_0_1 = a_1
        //          # POP CALL
        //          field[1] ret := #RET_0_1[0..1]
        //          field[1] #RET_0 = ret
        //      # POP CALL
        //      field[1] b_0 := #RET_0
        //      return

        let foo_signature = DeclarationSignature::new()
            .inputs(vec![DeclarationType::array((
                DeclarationType::FieldElement,
                Constant::Generic("K"),
            ))])
            .outputs(vec![DeclarationType::array((
                DeclarationType::FieldElement,
                Constant::Generic("K"),
            ))])
            .generics(vec![Some("K".into())]);

        let foo: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![DeclarationVariable::array(
                "a",
                DeclarationType::FieldElement,
                Constant::Generic("K"),
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
                        box ArrayExpressionInner::FunctionCall(
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
            ],
            signature: foo_signature.clone(),
        };

        let bar_signature = foo_signature.clone();

        let bar: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![DeclarationVariable::array(
                "a",
                DeclarationType::FieldElement,
                Constant::Generic("K"),
            )
            .into()],
            statements: vec![TypedStatement::Return(vec![
                ArrayExpressionInner::Identifier("a".into())
                    .annotate(
                        Type::FieldElement,
                        UExpressionInner::Identifier("K".into()).annotate(UBitwidth::B32),
                    )
                    .into(),
            ])],
            signature: bar_signature.clone(),
        };

        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![],
            statements: vec![
                TypedStatement::MultipleDefinition(
                    vec![Variable::array("b", Type::FieldElement, 1u32).into()],
                    TypedExpressionList::FunctionCall(
                        DeclarationFunctionKey::with_location("main", "foo")
                            .signature(foo_signature.clone()),
                        vec![None],
                        vec![ArrayExpressionInner::Value(
                            vec![FieldElementExpression::Number(Bn128Field::from(1)).into()].into(),
                        )
                        .annotate(Type::FieldElement, 1u32)
                        .into()],
                        vec![Type::array((Type::FieldElement, 1u32))],
                    ),
                ),
                TypedStatement::Return(vec![]),
            ],
            signature: DeclarationSignature::new(),
        };

        let p = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![
                        (
                            DeclarationFunctionKey::with_location("main", "bar")
                                .signature(bar_signature.clone()),
                            TypedFunctionSymbol::Here(bar),
                        ),
                        (
                            DeclarationFunctionKey::with_location("main", "foo")
                                .signature(foo_signature.clone()),
                            TypedFunctionSymbol::Here(foo),
                        ),
                        (
                            DeclarationFunctionKey::with_location("main", "main"),
                            TypedFunctionSymbol::Here(main),
                        ),
                    ]
                    .into_iter()
                    .collect(),
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
                    GGenericsAssignment(vec![("K", 1)].into_iter().collect()),
                ),
                TypedStatement::PushCallLog(
                    DeclarationFunctionKey::with_location("main", "bar")
                        .signature(foo_signature.clone()),
                    GGenericsAssignment(vec![("K", 2)].into_iter().collect()),
                ),
                TypedStatement::Definition(
                    Variable::array(Identifier::from("a").version(1), Type::FieldElement, 2u32)
                        .into(),
                    ArrayExpressionInner::Value(
                        vec![
                            TypedExpressionOrSpread::Spread(
                                ArrayExpressionInner::Value(
                                    vec![TypedExpressionOrSpread::Expression(
                                        FieldElementExpression::Number(Bn128Field::from(1)).into(),
                                    )]
                                    .into(),
                                )
                                .annotate(Type::FieldElement, 1u32)
                                .into(),
                            ),
                            FieldElementExpression::Number(Bn128Field::from(0)).into(),
                        ]
                        .into(),
                    )
                    .annotate(Type::FieldElement, 2u32)
                    .into(),
                ),
                TypedStatement::Definition(
                    Variable::array(
                        Identifier::from(CoreIdentifier::Call(0)).version(1),
                        Type::FieldElement,
                        2u32,
                    )
                    .into(),
                    ArrayExpressionInner::Identifier(Identifier::from("a").version(1))
                        .annotate(Type::FieldElement, 2u32)
                        .into(),
                ),
                TypedStatement::PopCallLog,
                TypedStatement::Definition(
                    Variable::array("ret", Type::FieldElement, 1u32).into(),
                    ArrayExpressionInner::Slice(
                        box ArrayExpressionInner::Identifier(
                            Identifier::from(CoreIdentifier::Call(0)).version(1),
                        )
                        .annotate(Type::FieldElement, 2u32),
                        box 0u32.into(),
                        box 1u32.into(),
                    )
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
                ),
                TypedStatement::Definition(
                    Variable::array(
                        Identifier::from(CoreIdentifier::Call(0)),
                        Type::FieldElement,
                        1u32,
                    )
                    .into(),
                    ArrayExpressionInner::Identifier("ret".into())
                        .annotate(Type::FieldElement, 1u32)
                        .into(),
                ),
                TypedStatement::PopCallLog,
                TypedStatement::Definition(
                    Variable::array("b", Type::FieldElement, 1u32).into(),
                    ArrayExpressionInner::Identifier(Identifier::from(CoreIdentifier::Call(0)))
                        .annotate(Type::FieldElement, 1u32)
                        .into(),
                ),
                TypedStatement::Return(vec![]),
            ],
            signature: DeclarationSignature::new(),
        };

        let expected = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![(
                        DeclarationFunctionKey::with_location("main", "main")
                            .signature(DeclarationSignature::new()),
                        TypedFunctionSymbol::Here(expected_main),
                    )]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
        };

        assert_eq!(reduced.unwrap(), expected);
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
            .generics(vec![Some("K".into())])
            .inputs(vec![DeclarationType::array((
                DeclarationType::FieldElement,
                Constant::Generic("K"),
            ))])
            .outputs(vec![DeclarationType::array((
                DeclarationType::FieldElement,
                Constant::Generic("K"),
            ))]);

        let foo: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![
                DeclarationVariable::array("a", DeclarationType::FieldElement, "K").into(),
            ],
            statements: vec![TypedStatement::Return(vec![
                ArrayExpressionInner::Identifier("a".into())
                    .annotate(Type::FieldElement, 1u32)
                    .into(),
            ])],
            signature: foo_signature.clone(),
        };

        let main: TypedFunction<Bn128Field> = TypedFunction {
            arguments: vec![],
            statements: vec![
                TypedStatement::MultipleDefinition(
                    vec![Variable::array("b", Type::FieldElement, 1u32).into()],
                    TypedExpressionList::FunctionCall(
                        DeclarationFunctionKey::with_location("main", "foo")
                            .signature(foo_signature.clone()),
                        vec![None],
                        vec![ArrayExpressionInner::Value(vec![].into())
                            .annotate(Type::FieldElement, 0u32)
                            .into()],
                        vec![Type::array((Type::FieldElement, 1u32))],
                    ),
                ),
                TypedStatement::Return(vec![]),
            ],
            signature: DeclarationSignature::new().inputs(vec![]).outputs(vec![]),
        };

        let p = TypedProgram {
            main: "main".into(),
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![
                        (
                            DeclarationFunctionKey::with_location("main", "foo")
                                .signature(foo_signature.clone()),
                            TypedFunctionSymbol::Here(foo),
                        ),
                        (
                            DeclarationFunctionKey::with_location("main", "main").signature(
                                DeclarationSignature::new().inputs(vec![]).outputs(vec![]),
                            ),
                            TypedFunctionSymbol::Here(main),
                        ),
                    ]
                    .into_iter()
                    .collect(),
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
