//! Module containing semantic analysis tools to run at compile time
//!
//! @file semantics.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2017

use num_bigint::BigUint;
use std::collections::{btree_map::Entry, BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;
use std::path::PathBuf;
use zokrates_ast::common::FormatString;
use zokrates_ast::typed::types::{GGenericsAssignment, GTupleType, GenericsAssignment};
use zokrates_ast::typed::SourceIdentifier;
use zokrates_ast::typed::*;
use zokrates_ast::typed::{DeclarationParameter, DeclarationVariable, Variable};
use zokrates_ast::untyped::Identifier;
use zokrates_ast::untyped::*;
use zokrates_field::Field;

use zokrates_ast::untyped::types::{UnresolvedSignature, UnresolvedType, UserTypeId};

use std::hash::Hash;
use zokrates_ast::typed::types::{
    check_type, specialize_declaration_type, ArrayType, DeclarationArrayType, DeclarationConstant,
    DeclarationFunctionKey, DeclarationSignature, DeclarationStructMember, DeclarationStructType,
    DeclarationTupleType, DeclarationType, GenericIdentifier, StructLocation, StructMember,
    TupleType,
};

#[derive(PartialEq, Eq, Debug)]
pub struct ErrorInner {
    pos: Option<(Position, Position)>,
    message: String,
}

#[derive(PartialEq, Eq, Debug)]
pub struct Error {
    pub inner: ErrorInner,
    pub module_id: PathBuf,
}

impl ErrorInner {
    pub fn pos(&self) -> &Option<(Position, Position)> {
        &self.pos
    }

    pub fn message(&self) -> &str {
        &self.message
    }

    fn in_file(self, id: &ModuleId) -> Error {
        Error {
            inner: self,
            module_id: id.to_path_buf(),
        }
    }
}

// a single struct to cover all cases of user-defined types
#[derive(Debug, Clone)]
struct UserDeclarationType<'ast, T> {
    generics: Vec<DeclarationConstant<'ast, T>>,
    ty: DeclarationType<'ast, T>,
}

impl<'ast, T> UserDeclarationType<'ast, T> {
    // returns the declared generics for this user type
    // for alias of basic types this is empty
    // for structs this is the same as the used generics
    // for aliases of structs this is the names of the generics declared on the left side of the type declaration
    fn declaration_generics(&self) -> Vec<&'ast str> {
        self.generics
            .iter()
            .filter_map(|g| match g {
                DeclarationConstant::Generic(g) => Some(g),
                _ => None,
            })
            .collect::<BTreeSet<_>>() // we collect into a BTreeSet because draining it after yields the element in the right order defined by Ord
            .into_iter()
            .map(|g| g.name())
            .collect()
    }
}

type TypeMap<'ast, T> = BTreeMap<OwnedModuleId, BTreeMap<UserTypeId, UserDeclarationType<'ast, T>>>;
type ConstantMap<'ast, T> =
    BTreeMap<OwnedModuleId, BTreeMap<ConstantIdentifier<'ast>, DeclarationType<'ast, T>>>;

/// The global state of the program during semantic checks
#[derive(Debug)]
struct State<'ast, T> {
    /// The modules yet to be checked, which we consume as we explore the dependency tree
    modules: Modules<'ast>,
    /// The already checked modules, which we're returning at the end
    typed_modules: TypedModules<'ast, T>,
    /// The user-defined types, which we keep track at this phase only. In later phases, we rely only on basic types and combinations thereof
    types: TypeMap<'ast, T>,
    // The user-defined constants
    constants: ConstantMap<'ast, T>,
}

/// A symbol for a given name: either a type or a group of functions. Not both!
#[derive(PartialEq, Hash, Eq, Debug)]
enum SymbolType<'ast, T> {
    Type,
    Constant,
    Functions(BTreeSet<DeclarationSignature<'ast, T>>),
}

/// A data structure to keep track of all symbols in a module
#[derive(Default)]
struct SymbolUnifier<'ast, T> {
    symbols: BTreeMap<String, SymbolType<'ast, T>>,
}

impl<'ast, T: std::cmp::Ord> SymbolUnifier<'ast, T> {
    fn insert_type<S: Into<String>>(&mut self, id: S) -> bool {
        let e = self.symbols.entry(id.into());
        match e {
            // if anything is already called `id`, we cannot introduce the symbol
            Entry::Occupied(..) => false,
            // otherwise, we can!
            Entry::Vacant(v) => {
                v.insert(SymbolType::Type);
                true
            }
        }
    }

    fn insert_constant<S: Into<String>>(&mut self, id: S) -> bool {
        let e = self.symbols.entry(id.into());
        match e {
            // if anything is already called `id`, we cannot introduce this constant
            Entry::Occupied(..) => false,
            // otherwise, we can!
            Entry::Vacant(v) => {
                v.insert(SymbolType::Constant);
                true
            }
        }
    }

    fn insert_function<S: Into<String>>(
        &mut self,
        id: S,
        signature: DeclarationSignature<'ast, T>,
    ) -> bool {
        let s_type = self.symbols.entry(id.into());
        match s_type {
            // if anything is already called `id`, it depends what it is
            Entry::Occupied(mut o) => {
                match o.get_mut() {
                    // if it's a Type or a Constant, then we can't introduce a function
                    SymbolType::Type | SymbolType::Constant => false,
                    // if it's a Function, we can introduce it only if it has a different signature
                    SymbolType::Functions(signatures) => signatures.insert(signature),
                }
            }
            // otherwise, we can!
            Entry::Vacant(v) => {
                v.insert(SymbolType::Functions(vec![signature].into_iter().collect()));
                true
            }
        }
    }
}

impl<'ast, T: Field> State<'ast, T> {
    fn new(modules: Modules<'ast>) -> Self {
        State {
            modules,
            typed_modules: BTreeMap::new(),
            types: BTreeMap::new(),
            constants: BTreeMap::new(),
        }
    }
}

/// A function query in the current module.
#[derive(Debug)]
struct FunctionQuery<'ast, T> {
    id: Identifier<'ast>,
    generics_count: Option<usize>,
    inputs: Vec<Type<'ast, T>>,
    /// Output type is optional as we try to infer it
    output: Option<Type<'ast, T>>,
}

impl<'ast, T: fmt::Display> fmt::Display for FunctionQuery<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(count) = self.generics_count {
            write!(
                f,
                "<{}>",
                (0..count)
                    .map(|_| String::from("_"))
                    .collect::<Vec<_>>()
                    .join(", ")
            )?
        }

        write!(f, "(")?;
        for (i, t) in self.inputs.iter().enumerate() {
            write!(f, "{}", t)?;
            if i < self.inputs.len() - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, ")")?;

        write!(
            f,
            " -> {}",
            self.output
                .as_ref()
                .map(|o| o.to_string())
                .unwrap_or_else(|| "_".to_string())
        )
    }
}

impl<'ast, T: Field> FunctionQuery<'ast, T> {
    /// Create a new query.
    fn new(
        id: Identifier<'ast>,
        generics: &Option<Vec<Option<UExpression<'ast, T>>>>,
        inputs: &[Type<'ast, T>],
        output: Option<Type<'ast, T>>,
    ) -> Self {
        FunctionQuery {
            id,
            generics_count: generics.as_ref().map(|g| g.len()),
            inputs: inputs.to_owned(),
            output,
        }
    }

    /// match a `FunctionKey` against this `FunctionQuery`
    fn match_func(&self, func: &DeclarationFunctionKey<'ast, T>) -> bool {
        self.id == func.id
            && self.generics_count.map(|count| count == func.signature.generics.len()).unwrap_or(true) // we do not look at the values here, this will be checked when inlining anyway
            && self.inputs.len() == func.signature.inputs.len()
            && self
                .inputs
                .iter()
                .zip(func.signature.inputs.iter())
                .all(|(input_ty, sig_ty)| input_ty.can_be_specialized_to(sig_ty))
            && self.output
            .as_ref()
                    .map(|o| o.can_be_specialized_to(&func.signature.output))
                    .unwrap_or(true)
    }

    fn match_funcs(
        &self,
        funcs: &HashSet<DeclarationFunctionKey<'ast, T>>,
    ) -> Vec<DeclarationFunctionKey<'ast, T>> {
        funcs
            .iter()
            .filter(|func| self.match_func(func))
            .cloned()
            .collect()
    }
}

#[derive(Debug, Clone)]
pub struct IdentifierInfo<'ast, T, U> {
    id: U,
    ty: Type<'ast, T>,
    is_mutable: bool,
}

#[derive(Default, Debug)]
struct Scope<'ast, T> {
    level: usize,
    map: HashMap<
        SourceIdentifier<'ast>,
        BTreeMap<usize, IdentifierInfo<'ast, T, CoreIdentifier<'ast>>>,
    >,
}

impl<'ast, T: Field> Scope<'ast, T> {
    // insert into the scope and return whether we are shadowing an existing variable
    fn insert(
        &mut self,
        id: SourceIdentifier<'ast>,
        info: IdentifierInfo<'ast, T, CoreIdentifier<'ast>>,
    ) -> bool {
        let existed = self
            .map
            .get(&id)
            .map(|versions| !versions.is_empty())
            .unwrap_or(false);
        self.map.entry(id).or_default().insert(self.level, info);

        existed
    }

    /// get the current version of this variable
    fn get(
        &self,
        id: &SourceIdentifier<'ast>,
    ) -> Option<IdentifierInfo<'ast, T, CoreIdentifier<'ast>>> {
        self.map
            .get(id)
            .and_then(|versions| versions.values().next_back().cloned())
    }

    fn enter(&mut self) {
        self.level += 1;
    }

    fn exit(&mut self) {
        for versions in self.map.values_mut() {
            versions.remove(&self.level);
        }
        self.level -= 1;
    }
}

/// Checker checks the semantics of a program, keeping track of functions and variables in scope
#[derive(Default)]
pub struct Checker<'ast, T> {
    return_type: Option<DeclarationType<'ast, T>>,
    scope: Scope<'ast, T>,
    functions: HashSet<DeclarationFunctionKey<'ast, T>>,
}

impl<'ast, T: Field> Checker<'ast, T> {
    /// Check a `Program`
    ///
    /// # Arguments
    ///
    /// * `prog` - The `Program` to be checked
    pub fn check(prog: Program<'ast>) -> Result<TypedProgram<'ast, T>, Vec<Error>> {
        Checker::default().check_program(prog)
    }

    fn check_program(
        &mut self,
        program: Program<'ast>,
    ) -> Result<TypedProgram<'ast, T>, Vec<Error>> {
        let mut state = State::new(program.modules);

        let mut errors = vec![];

        // recursively type-check modules starting with `main`
        match self.check_module(&program.main, &mut state) {
            Ok(()) => {}
            Err(e) => errors.extend(e),
        };

        if !errors.is_empty() {
            return Err(errors);
        }

        let main_id = program.main.clone();

        Checker::check_single_main(state.typed_modules.get(&program.main).unwrap()).map_err(
            |inner| {
                vec![Error {
                    inner,
                    module_id: main_id,
                }]
            },
        )?;

        Ok(TypedProgram {
            main: program.main,
            modules: state.typed_modules,
        })
    }

    fn check_type_definition(
        &mut self,
        ty: TypeDefinitionNode<'ast>,
        module_id: &ModuleId,
        state: &State<'ast, T>,
    ) -> Result<UserDeclarationType<'ast, T>, Vec<ErrorInner>> {
        let pos = ty.pos();
        let ty = ty.value;

        let mut errors = vec![];

        let mut generics = vec![];
        let mut generics_map = BTreeMap::new();

        for (index, g) in ty.generics.iter().enumerate() {
            if state
                .constants
                .get(module_id)
                .and_then(|m| m.get(g.value))
                .is_some()
            {
                errors.push(ErrorInner {
                    pos: Some(g.pos()),
                    message: format!(
                        "Generic parameter {p} conflicts with constant symbol {p}",
                        p = g.value
                    ),
                });
            } else {
                match generics_map.insert(g.value, index).is_none() {
                    true => {
                        generics.push(DeclarationConstant::Generic(
                            GenericIdentifier::with_name(g.value).with_index(index),
                        ));
                    }
                    false => {
                        errors.push(ErrorInner {
                            pos: Some(g.pos()),
                            message: format!("Generic parameter {} is already declared", g.value),
                        });
                    }
                }
            }
        }

        let mut used_generics = HashSet::new();

        match self.check_declaration_type(
            ty.ty,
            module_id,
            state,
            &generics_map,
            &mut used_generics,
        ) {
            Ok(ty) => {
                // check that all declared generics were used
                for declared_generic in generics_map.keys() {
                    if !used_generics.contains(declared_generic) {
                        errors.push(ErrorInner {
                            pos: Some(pos),
                            message: format!("Generic parameter {} must be used", declared_generic),
                        });
                    }
                }

                if !errors.is_empty() {
                    return Err(errors);
                }

                Ok(UserDeclarationType { generics, ty })
            }
            Err(e) => {
                errors.push(e);
                Err(errors)
            }
        }
    }

    fn check_constant_definition(
        &mut self,
        id: ConstantIdentifier<'ast>,
        c: ConstantDefinitionNode<'ast>,
        module_id: &ModuleId,
        state: &State<'ast, T>,
    ) -> Result<TypedConstant<'ast, T>, ErrorInner> {
        let pos = c.pos();

        let ty = self.check_declaration_type(
            c.value.ty.clone(),
            module_id,
            state,
            &BTreeMap::default(),
            &mut HashSet::default(),
        )?;
        let checked_expr =
            self.check_expression(c.value.expression.clone(), module_id, &state.types)?;

        match ty {
            DeclarationType::FieldElement => {
                FieldElementExpression::try_from_typed(checked_expr).map(TypedExpression::from)
            }
            DeclarationType::Boolean => {
                BooleanExpression::try_from_typed(checked_expr).map(TypedExpression::from)
            }
            DeclarationType::Uint(bitwidth) => {
                UExpression::try_from_typed(checked_expr, &bitwidth).map(TypedExpression::from)
            }
            DeclarationType::Array(ref array_ty) => {
                ArrayExpression::try_from_typed(checked_expr, array_ty).map(TypedExpression::from)
            }
            DeclarationType::Struct(ref struct_ty) => {
                StructExpression::try_from_typed(checked_expr, struct_ty).map(TypedExpression::from)
            }
            DeclarationType::Tuple(ref tuple_ty) => {
                TupleExpression::try_from_typed(checked_expr, tuple_ty).map(TypedExpression::from)
            }
            DeclarationType::Int => Err(checked_expr), // Integers cannot be assigned
        }
        .map_err(|e| ErrorInner {
            pos: Some(pos),
            message: format!(
                "Expression `{}` of type `{}` cannot be assigned to constant `{}` of type `{}`",
                e,
                e.get_type(),
                id,
                ty
            ),
        })
        .map(|e| TypedConstant::new(e, ty))
    }

    fn check_struct_type_declaration(
        &mut self,
        id: String,
        s: StructDefinitionNode<'ast>,
        module_id: &ModuleId,
        state: &State<'ast, T>,
    ) -> Result<DeclarationStructType<'ast, T>, Vec<ErrorInner>> {
        let pos = s.pos();
        let s = s.value;

        let mut errors = vec![];
        let mut fields: Vec<(_, _)> = vec![];
        let mut fields_set = HashSet::new();

        let mut generics = vec![];
        let mut generics_map = BTreeMap::new();

        for (index, g) in s.generics.iter().enumerate() {
            if state
                .constants
                .get(module_id)
                .and_then(|m| m.get(g.value))
                .is_some()
            {
                errors.push(ErrorInner {
                    pos: Some(g.pos()),
                    message: format!(
                        "Generic parameter {p} conflicts with constant symbol {p}",
                        p = g.value
                    ),
                });
            } else {
                match generics_map.insert(g.value, index).is_none() {
                    true => {
                        generics.push(Some(DeclarationConstant::Generic(
                            GenericIdentifier::with_name(g.value).with_index(index),
                        )));
                    }
                    false => {
                        errors.push(ErrorInner {
                            pos: Some(g.pos()),
                            message: format!("Generic parameter {} is already declared", g.value),
                        });
                    }
                }
            }
        }

        let mut used_generics = HashSet::new();

        for field in s.fields {
            let member_id = field.value.id.to_string();
            match self
                .check_declaration_type(
                    field.value.ty,
                    module_id,
                    state,
                    &generics_map,
                    &mut used_generics,
                )
                .map(|t| (member_id, t))
            {
                Ok(f) => match fields_set.insert(f.0.clone()) {
                    true => fields.push(f),
                    false => errors.push(ErrorInner {
                        pos: Some(pos),
                        message: format!("Duplicate key {} in struct definition", f.0,),
                    }),
                },
                Err(e) => {
                    errors.push(e);
                }
            }
        }

        // check that all declared generics were used
        for declared_generic in generics_map.keys() {
            if !used_generics.contains(declared_generic) {
                errors.push(ErrorInner {
                    pos: Some(pos),
                    message: format!("Generic parameter {} must be used", declared_generic),
                });
            }
        }

        if !errors.is_empty() {
            return Err(errors);
        }

        Ok(DeclarationStructType::new(
            module_id.to_path_buf(),
            id,
            generics,
            fields
                .iter()
                .map(|f| DeclarationStructMember::new(f.0.clone(), f.1.clone()))
                .collect(),
        ))
    }

    fn check_symbol_declaration(
        &mut self,
        declaration: SymbolDeclarationNode<'ast>,
        module_id: &ModuleId,
        state: &mut State<'ast, T>,
        symbols: &mut TypedSymbolDeclarations<'ast, T>,
        symbol_unifier: &mut SymbolUnifier<'ast, T>,
    ) -> Result<(), Vec<Error>> {
        let mut errors: Vec<Error> = vec![];

        let pos = declaration.pos();
        let declaration = declaration.value;

        match declaration.symbol.clone() {
            Symbol::Here(SymbolDefinition::Struct(t)) => {
                match self.check_struct_type_declaration(
                    declaration.id.to_string(),
                    t.clone(),
                    module_id,
                    state,
                ) {
                    Ok(ty) => {
                        match symbol_unifier.insert_type(declaration.id) {
                            false => errors.push(
                                ErrorInner {
                                    pos: Some(pos),
                                    message: format!(
                                        "{} conflicts with another symbol",
                                        declaration.id
                                    ),
                                }
                                .in_file(module_id),
                            ),
                            true => {
                                // there should be no entry in the map for this type yet
                                assert!(state
                                    .types
                                    .entry(module_id.to_path_buf())
                                    .or_default()
                                    .insert(
                                        declaration.id.to_string(),
                                        UserDeclarationType {
                                            generics: ty
                                                .generics
                                                .clone()
                                                .into_iter()
                                                .map(|g| g.unwrap())
                                                .collect(),
                                            ty: DeclarationType::Struct(ty)
                                        }
                                    )
                                    .is_none());
                            }
                        };
                    }
                    Err(e) => errors.extend(e.into_iter().map(|inner| Error {
                        inner,
                        module_id: module_id.to_path_buf(),
                    })),
                }
            }
            Symbol::Here(SymbolDefinition::Constant(c)) => {
                match self.check_constant_definition(declaration.id, c, module_id, state) {
                    Ok(c) => {
                        match symbol_unifier.insert_constant(declaration.id) {
                            false => errors.push(
                                ErrorInner {
                                    pos: Some(pos),
                                    message: format!(
                                        "{} conflicts with another symbol",
                                        declaration.id
                                    ),
                                }
                                .in_file(module_id),
                            ),
                            true => {
                                symbols.push(
                                    TypedConstantSymbolDeclaration::new(
                                        CanonicalConstantIdentifier::new(
                                            declaration.id,
                                            module_id.into(),
                                        ),
                                        TypedConstantSymbol::Here(c.clone()),
                                    )
                                    .into(),
                                );
                                let id = declaration.id;

                                let info = IdentifierInfo {
                                    id: CoreIdentifier::Constant(CanonicalConstantIdentifier::new(
                                        declaration.id,
                                        module_id.into(),
                                    )),
                                    ty: c.get_type(),
                                    is_mutable: false,
                                };
                                assert_eq!(self.scope.level, 0);
                                assert!(!self.scope.insert(id, info));
                                assert!(state
                                    .constants
                                    .entry(module_id.to_path_buf())
                                    .or_default()
                                    .insert(declaration.id, c.ty)
                                    .is_none());
                            }
                        };
                    }
                    Err(e) => {
                        errors.push(e.in_file(module_id));
                    }
                }
            }
            Symbol::Here(SymbolDefinition::Type(t)) => {
                match self.check_type_definition(t, module_id, state) {
                    Ok(ty) => {
                        match symbol_unifier.insert_type(declaration.id) {
                            false => errors.push(
                                ErrorInner {
                                    pos: Some(pos),
                                    message: format!(
                                        "{} conflicts with another symbol",
                                        declaration.id,
                                    ),
                                }
                                .in_file(module_id),
                            ),
                            true => {
                                assert!(state
                                    .types
                                    .entry(module_id.to_path_buf())
                                    .or_default()
                                    .insert(declaration.id.to_string(), ty)
                                    .is_none());
                            }
                        };
                    }
                    Err(e) => {
                        errors.extend(e.into_iter().map(|inner| inner.in_file(module_id)));
                    }
                }
            }
            Symbol::Here(SymbolDefinition::Function(f)) => {
                match self.check_function(f, module_id, state) {
                    Ok(funct) => {
                        match symbol_unifier
                            .insert_function(declaration.id, funct.signature.clone())
                        {
                            false => errors.push(
                                ErrorInner {
                                    pos: Some(pos),
                                    message: format!(
                                        "{} conflicts with another symbol",
                                        declaration.id
                                    ),
                                }
                                .in_file(module_id),
                            ),
                            true => {}
                        };

                        self.functions.insert(
                            DeclarationFunctionKey::with_location(
                                module_id.to_path_buf(),
                                declaration.id,
                            )
                            .signature(funct.signature.clone()),
                        );
                        symbols.push(
                            TypedFunctionSymbolDeclaration::new(
                                DeclarationFunctionKey::with_location(
                                    module_id.to_path_buf(),
                                    declaration.id,
                                )
                                .signature(funct.signature.clone()),
                                TypedFunctionSymbol::Here(funct),
                            )
                            .into(),
                        );
                    }
                    Err(e) => {
                        errors.extend(e.into_iter().map(|inner| inner.in_file(module_id)));
                    }
                }
            }
            Symbol::There(import) => {
                let pos = import.pos();
                let import = import.value;

                match Checker::default().check_module(&import.module_id, state) {
                    Ok(()) => {
                        // find candidates in the checked module
                        let function_candidates: Vec<_> = state
                            .typed_modules
                            .get(&import.module_id)
                            .unwrap()
                            .functions_iter()
                            .into_iter()
                            .filter(|d| d.key.id == import.symbol_id)
                            .map(|d| DeclarationFunctionKey {
                                module: import.module_id.to_path_buf(),
                                id: import.symbol_id,
                                signature: d.symbol.signature(&state.typed_modules).clone(),
                            })
                            .collect();

                        // find candidates in the types
                        let type_candidate = state
                            .types
                            .entry(import.module_id.to_path_buf())
                            .or_default()
                            .get(import.symbol_id)
                            .cloned();

                        // find constant definition candidate
                        let const_candidate = state
                            .constants
                            .entry(import.module_id.to_path_buf())
                            .or_default()
                            .iter()
                            .find(|(i, _)| *i == &import.symbol_id)
                            .map(|(_, c)| c)
                            .cloned();

                        match (function_candidates.len(), type_candidate, const_candidate) {
                            (0, Some(t), None) => {
                                // rename the type to the declared symbol
                                let t = UserDeclarationType {
                                    ty: match t.ty {
                                        DeclarationType::Struct(t) => DeclarationType::Struct(DeclarationStructType {
                                            location: Some(StructLocation {
                                                name: declaration.id.into(),
                                                module: module_id.to_path_buf()
                                            }),
                                            ..t
                                        }),
                                        _ => t.ty // all other cases
                                    },
                                    ..t
                                };

                                // we imported a type, so the symbol it gets bound to should not already exist
                                match symbol_unifier.insert_type(declaration.id) {
                                    false => {
                                        errors.push(Error {
                                            module_id: module_id.to_path_buf(),
                                            inner: ErrorInner {
                                                pos: Some(pos),
                                                message: format!(
                                                    "{} conflicts with another symbol",
                                                    declaration.id,
                                                ),
                                            }});
                                    }
                                    true => {}
                                };
                                state
                                    .types
                                    .entry(module_id.to_path_buf())
                                    .or_default()
                                    .insert(declaration.id.to_string(), t);
                            }
                            (0, None, Some(ty)) => {
                                match symbol_unifier.insert_constant(declaration.id) {
                                    false => {
                                        errors.push(Error {
                                            module_id: module_id.to_path_buf(),
                                            inner: ErrorInner {
                                                pos: Some(pos),
                                                message: format!(
                                                    "{} conflicts with another symbol",
                                                    declaration.id,
                                                ),
                                            }});
                                    }
                                    true => {
                                        let imported_id = CanonicalConstantIdentifier::new(import.symbol_id, import.module_id);
                                        let id = CanonicalConstantIdentifier::new(declaration.id, module_id.into());

                                        symbols.push(TypedConstantSymbolDeclaration::new(
                                            id.clone(),
                                            TypedConstantSymbol::There(imported_id)
                                        ).into());

                                        let id = declaration.id;
                                        let info = IdentifierInfo {
                                            id: CoreIdentifier::Constant(CanonicalConstantIdentifier::new(
                                                declaration.id,
                                                module_id.into(),
                                            )),
                                            ty: zokrates_ast::typed::types::try_from_g_type(ty.clone()).unwrap(),
                                            is_mutable: false,
                                        };
                                        assert_eq!(self.scope.level, 0);
                                        assert!(!self.scope.insert(id, info));

                                        state
                                            .constants
                                            .entry(module_id.to_path_buf())
                                            .or_default()
                                            .insert(declaration.id, ty);
                                    }
                                };
                            }
                            (0, None, None) => {
                                errors.push(ErrorInner {
                                    pos: Some(pos),
                                    message: format!(
                                        "Could not find symbol {} in module {}",
                                        import.symbol_id, import.module_id.display(),
                                    ),
                                }.in_file(module_id));
                            }
                            (_, Some(_), Some(_)) => unreachable!("collision in module we're importing from should have been caught when checking it"),
                            _ => {
                                for candidate in function_candidates {

                                    match symbol_unifier.insert_function(declaration.id, candidate.signature.clone()) {
                                        false => {
                                            errors.push(ErrorInner {
                                                pos: Some(pos),
                                                message: format!(
                                                    "{} conflicts with another symbol",
                                                    declaration.id,
                                                ),
                                            }.in_file(module_id));
                                        },
                                        true => {}
                                    };

                                    let local_key = candidate.clone().id(declaration.id).module(module_id.to_path_buf());

                                    self.functions.insert(local_key.clone());
                                    symbols.push(
                                        TypedFunctionSymbolDeclaration::new(
                                            local_key,
                                            TypedFunctionSymbol::There(candidate,
                                            ),
                                        ).into()
                                    );
                                }
                            }
                        };
                    }
                    Err(e) => {
                        errors.extend(e);
                    }
                };
            }
            Symbol::Flat(funct) => {
                match symbol_unifier.insert_function(declaration.id, funct.typed_signature()) {
                    false => {
                        errors.push(
                            ErrorInner {
                                pos: Some(pos),
                                message: format!(
                                    "{} conflicts with another symbol",
                                    declaration.id
                                ),
                            }
                            .in_file(module_id),
                        );
                    }
                    true => {}
                };

                self.functions.insert(
                    DeclarationFunctionKey::with_location(module_id.to_path_buf(), declaration.id)
                        .signature(funct.typed_signature()),
                );
                symbols.push(
                    TypedFunctionSymbolDeclaration::new(
                        DeclarationFunctionKey::with_location(
                            module_id.to_path_buf(),
                            declaration.id,
                        )
                        .signature(funct.typed_signature()),
                        TypedFunctionSymbol::Flat(funct),
                    )
                    .into(),
                );
            }
            _ => unreachable!(),
        };

        // return if any errors occured
        if !errors.is_empty() {
            return Err(errors);
        }

        Ok(())
    }

    fn check_module(
        &mut self,
        module_id: &ModuleId,
        state: &mut State<'ast, T>,
    ) -> Result<(), Vec<Error>> {
        let mut checked_symbols = TypedSymbolDeclarations::new();

        // check if the module was already removed from the untyped ones
        let to_insert = match state.modules.remove(module_id) {
            // if it was, do nothing
            None => None,
            // if it was not, check it
            Some(module) => {
                // create default entries for this module
                state.types.entry(module_id.to_path_buf()).or_default();
                state.constants.entry(module_id.to_path_buf()).or_default();

                // we keep track of the introduced symbols to avoid collisions between types and functions
                let mut symbol_unifier = SymbolUnifier::default();

                // we go through symbol declarations and check them
                for declaration in module.symbols {
                    self.check_symbol_declaration(
                        declaration,
                        module_id,
                        state,
                        &mut checked_symbols,
                        &mut symbol_unifier,
                    )?
                }

                Some(TypedModule {
                    symbols: checked_symbols,
                })
            }
        };

        // insert into typed_modules if we checked anything
        if let Some(typed_module) = to_insert {
            // there should be no checked module at that key just yet, if there is we have a colision or we checked something twice
            assert!(state
                .typed_modules
                .insert(module_id.to_path_buf(), typed_module)
                .is_none());
        };

        Ok(())
    }

    fn check_single_main(module: &TypedModule<T>) -> Result<(), ErrorInner> {
        match module
            .functions_iter()
            .into_iter()
            .filter(|d| d.key.id == "main")
            .count()
        {
            1 => Ok(()),
            0 => Err(ErrorInner {
                pos: None,
                message: "No main function found".into(),
            }),
            n => Err(ErrorInner {
                pos: None,
                message: format!("Only one main function allowed, found {}", n),
            }),
        }
    }

    fn check_for_variable(
        &mut self,
        var: VariableNode<'ast>,
        module_id: &ModuleId,
        types: &TypeMap<'ast, T>,
    ) -> Result<Variable<'ast, T>, Vec<ErrorInner>> {
        let pos = var.pos();

        let var = self.check_variable(var, module_id, types)?;

        match var.get_type() {
            Type::Uint(UBitwidth::B32) => Ok(()),
            t => Err(vec![ErrorInner {
                pos: Some(pos),
                message: format!("Variable in for loop cannot have type {}", t),
            }]),
        }?;

        Ok(var)
    }

    fn id_in_this_scope(&self, id: SourceIdentifier<'ast>) -> CoreIdentifier<'ast> {
        // in the semantic checker, 0 is top level, 1 is function level. For shadowing, we start with 0 at function level
        // hence the offset of 1
        assert!(
            self.scope.level > 0,
            "CoreIdentifier cannot be declared in the global scope"
        );
        CoreIdentifier::from(ShadowedIdentifier::shadow(id, self.scope.level - 1))
    }

    fn check_function(
        &mut self,
        funct_node: FunctionNode<'ast>,
        module_id: &ModuleId,
        state: &State<'ast, T>,
    ) -> Result<TypedFunction<'ast, T>, Vec<ErrorInner>> {
        assert!(self.return_type.is_none());

        self.enter_scope();

        let pos = funct_node.pos();

        let mut errors = vec![];
        let funct = funct_node.value;
        let mut signature = None;

        assert_eq!(funct.arguments.len(), funct.signature.inputs.len());

        let mut arguments_checked = vec![];

        let mut statements_checked = vec![];

        match self.check_signature(funct.signature, module_id, state) {
            Ok(s) => {
                // initialise generics map
                let mut generics: GenericsAssignment<'ast, T> = GGenericsAssignment::default();

                // define variables for the constants
                for generic in &s.generics {
                    let generic = match generic.clone().unwrap() {
                        DeclarationConstant::Generic(g) => g,
                        _ => unreachable!(),
                    };

                    // for declaration signatures, generics cannot be ignored
                    generics.0.insert(
                        generic.clone(),
                        UExpressionInner::Identifier(self.id_in_this_scope(generic.name()).into())
                            .annotate(UBitwidth::B32),
                    );

                    //we don't have to check for conflicts here, because this was done when checking the signature
                    self.insert_into_scope(generic.name(), Type::Uint(UBitwidth::B32), false);
                }

                for (arg, decl_ty) in funct.arguments.into_iter().zip(s.inputs.iter()) {
                    let pos = arg.pos();

                    let arg = arg.value;

                    let decl_v = DeclarationVariable::new(
                        self.id_in_this_scope(arg.id.value.id),
                        decl_ty.clone(),
                        arg.id.value.is_mutable,
                    );

                    let is_mutable = arg.id.value.is_mutable;

                    let ty = specialize_declaration_type(decl_v.clone()._type, &generics).unwrap();

                    assert_eq!(self.scope.level, 1);

                    let id = arg.id.value.id;
                    let info = IdentifierInfo {
                        id: decl_v.id.id.clone(),
                        ty,
                        is_mutable,
                    };
                    match self.scope.insert(id, info) {
                        false => {}
                        true => {
                            errors.push(ErrorInner {
                                pos: Some(pos),
                                message: format!("Duplicate name in function definition: `{}` was previously declared as an argument, a generic parameter or a constant", arg.id.value.id)
                            });
                        }
                    };

                    arguments_checked.push(DeclarationParameter {
                        id: decl_v,
                        private: arg.is_private,
                    });
                }

                let mut found_return = false;

                for stat in funct.statements.into_iter() {
                    let pos = Some(stat.pos());

                    if let Statement::Return(..) = stat.value {
                        if found_return {
                            errors.push(ErrorInner {
                                pos,
                                message: "Expected a single return statement".to_string(),
                            });
                        }

                        found_return = true;
                    }

                    match self.check_statement(stat, module_id, &state.types) {
                        Ok(statement) => {
                            statements_checked.push(statement);
                        }
                        Err(e) => {
                            errors.extend(e);
                        }
                    }
                }

                if !found_return {
                    match (&*s.output).is_empty_tuple() {
                        true => statements_checked
                            .push(TypedStatement::Return(TypedExpression::empty_tuple())),
                        false => {
                            errors.push(ErrorInner {
                                pos: Some(pos),
                                message: "Expected a return statement".to_string(),
                            });
                        }
                    }
                }

                signature = Some(s);
            }
            Err(e) => {
                errors.extend(e);
            }
        };

        self.exit_scope();

        if !errors.is_empty() {
            return Err(errors);
        }

        self.return_type = None;

        Ok(TypedFunction {
            arguments: arguments_checked,
            statements: statements_checked,
            signature: signature.unwrap(),
        })
    }

    fn check_signature(
        &mut self,
        signature: UnresolvedSignature<'ast>,
        module_id: &ModuleId,
        state: &State<'ast, T>,
    ) -> Result<DeclarationSignature<'ast, T>, Vec<ErrorInner>> {
        let mut errors = vec![];
        let mut inputs = vec![];
        let mut generics = vec![];

        let mut generics_map = BTreeMap::new();

        for (index, g) in signature.generics.iter().enumerate() {
            if state
                .constants
                .get(module_id)
                .and_then(|m| m.get(g.value))
                .is_some()
            {
                errors.push(ErrorInner {
                    pos: Some(g.pos()),
                    message: format!(
                        "Generic parameter {p} conflicts with constant symbol {p}",
                        p = g.value
                    ),
                });
            } else {
                match generics_map.insert(g.value, index).is_none() {
                    true => {
                        generics.push(Some(DeclarationConstant::Generic(
                            GenericIdentifier::with_name(g.value).with_index(index),
                        )));
                    }
                    false => {
                        errors.push(ErrorInner {
                            pos: Some(g.pos()),
                            message: format!("Generic parameter {} is already declared", g.value),
                        });
                    }
                }
            }
        }

        for t in signature.inputs {
            match self.check_declaration_type(
                t,
                module_id,
                state,
                &generics_map,
                &mut HashSet::default(),
            ) {
                Ok(t) => {
                    inputs.push(t);
                }
                Err(e) => {
                    errors.push(e);
                }
            }
        }

        match signature
            .output
            .map(|o| {
                self.check_declaration_type(
                    o,
                    module_id,
                    state,
                    &generics_map,
                    &mut HashSet::default(),
                )
            })
            .unwrap_or_else(|| Ok(DeclarationType::Tuple(GTupleType::new(vec![]))))
        {
            Ok(output) => {
                if !errors.is_empty() {
                    return Err(errors);
                }

                self.return_type = Some(output.clone());
                Ok(DeclarationSignature::new()
                    .generics(generics)
                    .inputs(inputs)
                    .output(output))
            }
            Err(e) => {
                errors.push(e);
                Err(errors)
            }
        }
    }

    fn check_type(
        &mut self,
        ty: UnresolvedTypeNode<'ast>,
        module_id: &ModuleId,
        types: &TypeMap<'ast, T>,
    ) -> Result<Type<'ast, T>, ErrorInner> {
        let pos = ty.pos();
        let ty = ty.value;

        match ty {
            UnresolvedType::FieldElement => Ok(Type::FieldElement),
            UnresolvedType::Boolean => Ok(Type::Boolean),
            UnresolvedType::Uint(bitwidth) => Ok(Type::uint(bitwidth)),
            UnresolvedType::Array(t, size) => {
                let size = self.check_expression(size, module_id, types)?;

                let ty = size.get_type();

                let size = match size {
                    TypedExpression::Uint(e) => match e.bitwidth() {
                        UBitwidth::B32 => Ok(e),
                        _ => Err(ErrorInner {
                            pos: Some(pos),
                            message: format!(
                            "Expected array dimension to be a u32 constant, found {} of type {}",
                            e, ty
                        ),
                        }),
                    },
                    TypedExpression::Int(v) => {
                        UExpression::try_from_int(v.clone(), &UBitwidth::B32).map_err(|_| {
                            ErrorInner {
                                pos: Some(pos),
                                message: format!(
                            "Expected array dimension to be a u32 constant, found {} of type {}",
                            v, ty
                        ),
                            }
                        })
                    }
                    _ => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "Expected array dimension to be a u32 constant, found {} of type {}",
                            size, ty
                        ),
                    }),
                }?;

                Ok(Type::Array(ArrayType::new(
                    self.check_type(*t, module_id, types)?,
                    size,
                )))
            }
            UnresolvedType::Tuple(elements) => {
                let checked_elements: Vec<_> = elements
                    .into_iter()
                    .map(|e| self.check_type(e, module_id, types))
                    .collect::<Result<_, _>>()?;
                Ok(Type::Tuple(TupleType::new(checked_elements)))
            }
            UnresolvedType::User(id, generics) => {
                let declared_ty =
                    types
                        .get(module_id)
                        .unwrap()
                        .get(&id)
                        .cloned()
                        .ok_or_else(|| ErrorInner {
                            pos: Some(pos),
                            message: format!("Undefined type {}", id),
                        })?;

                let generic_identifiers = declared_ty.declaration_generics();

                let declaration_type = declared_ty.ty;

                // absence of generics is treated as 0 generics, as we do not provide inference for now
                let generics = generics.unwrap_or_default();

                // check generics
                match generic_identifiers.len() == generics.len() {
                    true => {
                        // build the generic assignment for this type
                        let assignment = GGenericsAssignment(generics
                            .into_iter()
                            .zip(generic_identifiers)
                            .enumerate()
                            .map(|(i, (e, g))| match e {
                                Some(e) => {
                                    self
                                        .check_expression(e, module_id, types)
                                        .and_then(|e| {
                                            UExpression::try_from_typed(e, &UBitwidth::B32)
                                                .map(|e| (GenericIdentifier::with_name(g).with_index(i), e))
                                                .map_err(|e| ErrorInner {
                                                    pos: Some(pos),
                                                    message: format!("Expected u32 expression, but got expression of type {}", e.get_type()),
                                                })
                                        })
                                },
                                None => Err(ErrorInner {
                                    pos: Some(pos),
                                    message:
                                    "Expected u32 constant or identifier, but found `_`. Generic inference is not supported yet."
                                        .into(),
                                })
                            })
                            .collect::<Result<_, _>>()?);

                        // specialize the declared type using the generic assignment
                        Ok(specialize_declaration_type(declaration_type, &assignment).unwrap())
                    }
                    false => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "Expected {} generic argument{} on type {}, but got {}",
                            generic_identifiers.len(),
                            if generic_identifiers.len() == 1 {
                                ""
                            } else {
                                "s"
                            },
                            id,
                            generics.len()
                        ),
                    }),
                }
            }
        }
    }
    fn check_generic_expression(
        &mut self,
        expr: ExpressionNode<'ast>,
        module_id: &ModuleId,
        constants_map: &BTreeMap<ConstantIdentifier<'ast>, DeclarationType<'ast, T>>,
        generics_map: &BTreeMap<Identifier<'ast>, usize>,
        used_generics: &mut HashSet<Identifier<'ast>>,
    ) -> Result<DeclarationConstant<'ast, T>, ErrorInner> {
        let pos = expr.pos();

        match expr.value {
            Expression::U32Constant(c) => Ok(DeclarationConstant::from(c)),
            Expression::IntConstant(c) => {
                if c <= BigUint::from(2u128.pow(32) - 1) {
                    Ok(DeclarationConstant::from(
                        u32::from_str_radix(&c.to_str_radix(16), 16).unwrap(),
                    ))
                } else {
                    Err(ErrorInner {
                        pos: Some(pos),
                        message: format!(
                    "Expected array dimension to be a u32 constant or an identifier, found {}",
                    Expression::IntConstant(c)
                ),
                    })
                }
            }
            Expression::Identifier(name) => {
                used_generics.insert(name);

                match (constants_map.get(name), generics_map.get(&name)) {
                    (Some(ty), None) => {
                        match ty {
                            DeclarationType::Uint(UBitwidth::B32) => Ok(DeclarationConstant::Constant(CanonicalConstantIdentifier::new(name, module_id.into()))),
                            _ => Err(ErrorInner {
                                pos: Some(pos),
                                message: format!(
                                    "Expected array dimension to be a u32 constant or an identifier, found {} of type {}",
                                    name, ty
                                ),
                            })
                        }
                    }
                    (None, Some(index)) => Ok(DeclarationConstant::Generic(GenericIdentifier::with_name(name).with_index(*index))),
                    _ => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!("Undeclared symbol `{}`", name)
                    })
                }
            }
            e => Err(ErrorInner {
                pos: Some(pos),
                message: format!(
                    "Expected array dimension to be a u32 constant or an identifier, found {}",
                    e
                ),
            }),
        }
    }

    fn check_declaration_type(
        &mut self,
        ty: UnresolvedTypeNode<'ast>,
        module_id: &ModuleId,
        state: &State<'ast, T>,
        generics_map: &BTreeMap<Identifier<'ast>, usize>,
        used_generics: &mut HashSet<Identifier<'ast>>,
    ) -> Result<DeclarationType<'ast, T>, ErrorInner> {
        let pos = ty.pos();
        let ty = ty.value;

        match ty {
            UnresolvedType::FieldElement => Ok(DeclarationType::FieldElement),
            UnresolvedType::Boolean => Ok(DeclarationType::Boolean),
            UnresolvedType::Uint(bitwidth) => Ok(DeclarationType::uint(bitwidth)),
            UnresolvedType::Array(t, size) => {
                let checked_size = self.check_generic_expression(
                    size.clone(),
                    module_id,
                    state.constants.get(module_id).unwrap_or(&BTreeMap::new()),
                    generics_map,
                    used_generics,
                )?;

                Ok(DeclarationType::Array(DeclarationArrayType::new(
                    self.check_declaration_type(*t, module_id, state, generics_map, used_generics)?,
                    checked_size,
                )))
            }
            UnresolvedType::Tuple(elements) => {
                let checked_elements: Vec<_> = elements
                    .into_iter()
                    .map(|e| {
                        self.check_declaration_type(
                            e,
                            module_id,
                            state,
                            generics_map,
                            used_generics,
                        )
                    })
                    .collect::<Result<_, _>>()?;
                Ok(DeclarationType::Tuple(DeclarationTupleType::new(
                    checked_elements,
                )))
            }
            UnresolvedType::User(id, generics) => {
                let ty = state
                    .types
                    .get(module_id)
                    .unwrap()
                    .get(&id)
                    .cloned()
                    .ok_or_else(|| ErrorInner {
                        pos: Some(pos),
                        message: format!("Undefined type {}", id),
                    })?;

                let generics = generics.unwrap_or_default();
                let checked_generics: Vec<_> = generics
                    .into_iter()
                    .map(|e| match e {
                        Some(e) => self
                            .check_generic_expression(
                                e,
                                module_id,
                                state.constants.get(module_id).unwrap_or(&BTreeMap::new()),
                                generics_map,
                                used_generics,
                            )
                            .map(Some),
                        None => Err(ErrorInner {
                            pos: Some(pos),
                            message: "Expected u32 constant or identifier, but found `_`".into(),
                        }),
                    })
                    .collect::<Result<_, _>>()?;

                match ty.generics.len() == checked_generics.len() {
                    true => {
                        let mut assignment = GGenericsAssignment::default();

                        assignment.0.extend(ty.generics.iter().zip(checked_generics.iter()).map(|(decl_g, g_val)| match decl_g.clone() {
                            DeclarationConstant::Generic(g) => (g, g_val.clone().unwrap()),
                            _ => unreachable!("generic on declaration struct types must be generic identifiers")
                        }));

                        let res = match ty.ty {
                            // if the type is a struct, we do not specialize in the members.
                            // we only remap the generics
                            DeclarationType::Struct(declared_struct_ty) => {
                                DeclarationType::Struct(DeclarationStructType {
                                    generics: declared_struct_ty
                                        .generics
                                        .into_iter()
                                        .map(|g| g.map(|g| g.map(&assignment).unwrap()))
                                        .collect(),
                                    ..declared_struct_ty
                                })
                            }
                            ty => specialize_declaration_type(ty, &assignment).unwrap(),
                        };

                        Ok(res)
                    }
                    false => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "Expected {} generic argument{} on type {}, but got {}",
                            ty.generics.len(),
                            if ty.generics.len() == 1 { "" } else { "s" },
                            id,
                            checked_generics.len()
                        ),
                    }),
                }
            }
        }
    }

    fn check_variable(
        &mut self,
        v: zokrates_ast::untyped::VariableNode<'ast>,
        module_id: &ModuleId,
        types: &TypeMap<'ast, T>,
    ) -> Result<Variable<'ast, T>, Vec<ErrorInner>> {
        let ty = self
            .check_type(v.value._type, module_id, types)
            .map_err(|e| vec![e])?;

        // insert into the scope and ignore whether shadowing happened
        self.insert_into_scope(v.value.id, ty.clone(), v.value.is_mutable);

        Ok(Variable::new(
            self.id_in_this_scope(v.value.id),
            ty,
            v.value.is_mutable,
        ))
    }

    fn check_for_loop(
        &mut self,
        var: zokrates_ast::untyped::VariableNode<'ast>,
        range: (ExpressionNode<'ast>, ExpressionNode<'ast>),
        statements: Vec<StatementNode<'ast>>,
        pos: (Position, Position),
        module_id: &ModuleId,
        types: &TypeMap<'ast, T>,
    ) -> Result<TypedStatement<'ast, T>, Vec<ErrorInner>> {
        let from = self
            .check_expression(range.0, module_id, types)
            .map_err(|e| vec![e])?;
        let to = self
            .check_expression(range.1, module_id, types)
            .map_err(|e| vec![e])?;

        let from = match from {
            TypedExpression::Uint(from) => match from.bitwidth() {
                UBitwidth::B32 => Ok(from),
                bitwidth => Err(ErrorInner {
                    pos: Some(pos),
                    message: format!(
                        "Expected lower loop bound to be of type u32, found {}",
                        Type::<T>::Uint(bitwidth)
                    ),
                }),
            },
            TypedExpression::Int(v) => {
                UExpression::try_from_int(v, &UBitwidth::B32).map_err(|_| ErrorInner {
                    pos: Some(pos),
                    message: format!(
                        "Expected lower loop bound to be of type u32, found {}",
                        Type::<T>::Int
                    ),
                })
            }
            from => Err(ErrorInner {
                pos: Some(pos),
                message: format!(
                    "Expected lower loop bound to be of type u32, found {}",
                    from.get_type()
                ),
            }),
        }
        .map_err(|e| vec![e])?;

        let to = match to {
            TypedExpression::Uint(to) => match to.bitwidth() {
                UBitwidth::B32 => Ok(to),
                bitwidth => Err(ErrorInner {
                    pos: Some(pos),
                    message: format!(
                        "Expected upper loop bound to be of type u32, found {}",
                        Type::<T>::Uint(bitwidth)
                    ),
                }),
            },
            TypedExpression::Int(v) => {
                UExpression::try_from_int(v, &UBitwidth::B32).map_err(|_| ErrorInner {
                    pos: Some(pos),
                    message: format!(
                        "Expected upper loop bound to be of type u32, found {}",
                        Type::<T>::Int
                    ),
                })
            }
            to => Err(ErrorInner {
                pos: Some(pos),
                message: format!(
                    "Expected upper loop bound to be of type u32, found {}",
                    to.get_type()
                ),
            }),
        }
        .map_err(|e| vec![e])?;

        let var = self.check_for_variable(var, module_id, types)?;

        let checked_statements = statements
            .into_iter()
            .map(|s| self.check_statement(s, module_id, types))
            .collect::<Result<Vec<_>, _>>()?;

        Ok(TypedStatement::For(var, from, to, checked_statements))
    }

    // the assignee is already checked to be defined and mutable
    fn check_rhs(
        &mut self,
        return_type: Type<'ast, T>,
        expr: ExpressionNode<'ast>,
        module_id: &ModuleId,
        types: &TypeMap<'ast, T>,
    ) -> Result<TypedExpression<'ast, T>, ErrorInner> {
        match expr.value {
            // for function calls, check the rhs with the expected type
            Expression::FunctionCall(box fun_id_expression, generics, arguments) => self
                .check_function_call_expression(
                    fun_id_expression,
                    generics,
                    arguments,
                    Some(return_type),
                    module_id,
                    types,
                ),
            // otherwise, just check the rhs normally
            _ => self.check_expression(expr, module_id, types),
        }
    }

    fn check_statement(
        &mut self,
        stat: StatementNode<'ast>,
        module_id: &ModuleId,
        types: &TypeMap<'ast, T>,
    ) -> Result<TypedStatement<'ast, T>, Vec<ErrorInner>> {
        let pos = stat.pos();

        match stat.value {
            Statement::Log(l, expressions) => {
                let l = FormatString::from(l);

                let expressions = expressions
                    .into_iter()
                    .map(|e| self.check_expression(e, module_id, types))
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|e| vec![e])?;

                let mut errors = vec![];

                for e in &expressions {
                    if let TypedExpression::Int(e) = e {
                        errors.push(ErrorInner {
                            pos: Some(pos),
                            message: format!("Cannot determine type for expression `{}`", e),
                        });
                    }
                }

                if expressions.len() != l.len() {
                    errors.push(ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "Wrong argument count in log call: expected {}, got {}",
                            l.len(),
                            expressions.len()
                        ),
                    });
                }

                if !errors.is_empty() {
                    return Err(errors);
                }

                Ok(TypedStatement::Log(l, expressions))
            }
            Statement::Return(e) => {
                let mut errors = vec![];

                // we clone the return type because there might be other return statements
                let return_type = self.return_type.clone().unwrap();

                let e_checked = e
                    .map(|e| {
                        match e.value {
                            Expression::FunctionCall(
                                box fun_id_expression,
                                generics,
                                arguments,
                            ) => {
                                let ty = zokrates_ast::typed::types::try_from_g_type(
                                    return_type.clone(),
                                )
                                .map(Some)
                                .unwrap();

                                self.check_function_call_expression(
                                    fun_id_expression,
                                    generics,
                                    arguments,
                                    ty,
                                    module_id,
                                    types,
                                )
                            }
                            _ => self.check_expression(e, module_id, types),
                        }
                        .map_err(|e| vec![e])
                    })
                    .unwrap_or_else(|| Ok(TypedExpression::empty_tuple()))?;

                let res = match TypedExpression::align_to_type(e_checked.clone(), &return_type)
                    .map_err(|e| {
                        vec![ErrorInner {
                            pos: Some(pos),
                            message: format!(
                                "Expected return value to be of type `{}`, found `{}` of type `{}`",
                                e.1,
                                e.0,
                                e.0.get_type()
                            ),
                        }]
                    }) {
                    Ok(e) => {
                        match e.get_type() == return_type {
                            true => {}
                            false => errors.push(ErrorInner {
                                pos: Some(pos),
                                message: format!(
                                    "Expected `{}` in return statement, found `{}`",
                                    return_type,
                                    e.get_type()
                                ),
                            }),
                        }
                        TypedStatement::Return(e)
                    }
                    Err(err) => {
                        errors.extend(err);
                        TypedStatement::Return(e_checked)
                    }
                };

                if !errors.is_empty() {
                    return Err(errors);
                }

                Ok(res)
            }
            Statement::Definition(var, expr) => {
                // get the lhs type
                let var_ty = self
                    .check_type(var.value._type, module_id, types)
                    .map_err(|e| vec![e])?;

                // check the rhs based on the lhs type
                let checked_expr = self
                    .check_rhs(var_ty.clone(), expr, module_id, types)
                    .map_err(|e| vec![e])?;

                // insert the lhs into the scope and ignore whether shadowing happened
                self.insert_into_scope(var.value.id, var_ty.clone(), var.value.is_mutable);

                let var = Variable::new(
                    self.id_in_this_scope(var.value.id),
                    var_ty.clone(),
                    var.value.is_mutable,
                );

                match var_ty {
                    Type::FieldElement => FieldElementExpression::try_from_typed(checked_expr)
                        .map(TypedExpression::from),
                    Type::Boolean => {
                        BooleanExpression::try_from_typed(checked_expr).map(TypedExpression::from)
                    }
                    Type::Uint(bitwidth) => UExpression::try_from_typed(checked_expr, &bitwidth)
                        .map(TypedExpression::from),
                    Type::Array(ref array_ty) => {
                        ArrayExpression::try_from_typed(checked_expr, array_ty)
                            .map(TypedExpression::from)
                    }
                    Type::Struct(ref struct_ty) => {
                        StructExpression::try_from_typed(checked_expr, struct_ty)
                            .map(TypedExpression::from)
                    }
                    Type::Tuple(ref tuple_ty) => {
                        TupleExpression::try_from_typed(checked_expr, tuple_ty)
                            .map(TypedExpression::from)
                    }
                    Type::Int => Err(checked_expr), // Integers cannot be assigned
                }
                .map_err(|e| ErrorInner {
                    pos: Some(pos),
                    message: format!(
                        "Expression `{}` of type `{}` cannot be assigned to `{}` of type `{}`",
                        e,
                        e.get_type(),
                        var.clone(),
                        var_ty
                    ),
                })
                .map(|e| TypedStatement::Definition(var.into(), e.into()))
                .map_err(|e| vec![e])
            }
            Statement::Assignment(assignee, expr) => {
                // check that the assignee is declared, well formed and mutable
                let assignee = self
                    .check_assignee(assignee, module_id, types)
                    .map_err(|e| vec![e])?;

                let assignee_ty = assignee.get_type();

                let checked_expr = self
                    .check_rhs(assignee_ty.clone(), expr, module_id, types)
                    .map_err(|e| vec![e])?;

                match assignee_ty {
                    Type::FieldElement => FieldElementExpression::try_from_typed(checked_expr)
                        .map(TypedExpression::from),
                    Type::Boolean => {
                        BooleanExpression::try_from_typed(checked_expr).map(TypedExpression::from)
                    }
                    Type::Uint(bitwidth) => UExpression::try_from_typed(checked_expr, &bitwidth)
                        .map(TypedExpression::from),
                    Type::Array(ref array_ty) => {
                        ArrayExpression::try_from_typed(checked_expr, array_ty)
                            .map(TypedExpression::from)
                    }
                    Type::Struct(ref struct_ty) => {
                        StructExpression::try_from_typed(checked_expr, struct_ty)
                            .map(TypedExpression::from)
                    }
                    Type::Tuple(ref tuple_ty) => {
                        TupleExpression::try_from_typed(checked_expr, tuple_ty)
                            .map(TypedExpression::from)
                    }
                    Type::Int => Err(checked_expr), // Integers cannot be assigned
                }
                .map_err(|e| ErrorInner {
                    pos: Some(pos),
                    message: format!(
                        "Expression `{}` of type `{}` cannot be assigned to `{}` of type `{}`",
                        e,
                        e.get_type(),
                        assignee.clone(),
                        assignee_ty
                    ),
                })
                .map(|e| TypedStatement::Definition(assignee, e.into()))
                .map_err(|e| vec![e])
            }
            Statement::Assertion(e, message) => {
                let e = self
                    .check_expression(e, module_id, types)
                    .map_err(|e| vec![e])?;

                match e {
                    TypedExpression::Boolean(e) => Ok(TypedStatement::Assertion(
                        e,
                        RuntimeError::SourceAssertion(AssertionMetadata {
                            file: module_id.display().to_string(),
                            position: pos.0,
                            message,
                        }),
                    )),
                    e => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "Expected {} to be of type bool, found {}",
                            e,
                            e.get_type(),
                        ),
                    }),
                }
                .map_err(|e| vec![e])
            }
            Statement::For(var, from, to, statements) => {
                self.enter_scope();

                let res = self.check_for_loop(var, (from, to), statements, pos, module_id, types);

                self.exit_scope();

                res
            }
        }
    }

    fn check_assignee(
        &mut self,
        assignee: AssigneeNode<'ast>,
        module_id: &ModuleId,
        types: &TypeMap<'ast, T>,
    ) -> Result<TypedAssignee<'ast, T>, ErrorInner> {
        let pos = assignee.pos();
        // check that the assignee is declared
        match assignee.value {
            Assignee::Identifier(variable_name) => match self.scope.get(&variable_name) {
                Some(info) => match info.is_mutable {
                    false => Err(ErrorInner {
                        pos: Some(assignee.pos()),
                        message: format!("Assignment to an immutable variable `{}`", variable_name),
                    }),
                    _ => Ok(TypedAssignee::Identifier(Variable::new(
                        info.id,
                        info.ty.clone(),
                        info.is_mutable,
                    ))),
                },
                None => Err(ErrorInner {
                    pos: Some(assignee.pos()),
                    message: format!("Variable `{}` is undeclared", variable_name),
                }),
            },
            Assignee::Select(box assignee, box index) => {
                let checked_assignee = self.check_assignee(assignee, module_id, types)?;

                let ty = checked_assignee.get_type();
                match ty {
                    Type::Array(..) => {
                        let checked_index = match index {
                            RangeOrExpression::Expression(e) => {
                                self.check_expression(e, module_id, types)?
                            }
                            r => unimplemented!(
                                "Using slices in assignments is not supported yet, found {}",
                                r
                            ),
                        };

                        let checked_typed_index =
                            UExpression::try_from_typed(checked_index, &UBitwidth::B32).map_err(
                                |e| ErrorInner {
                                    pos: Some(pos),
                                    message: format!(
                                        "Expected array {} index to have type u32, found {}",
                                        checked_assignee,
                                        e.get_type()
                                    ),
                                },
                            )?;

                        Ok(TypedAssignee::Select(
                            box checked_assignee,
                            box checked_typed_index,
                        ))
                    }
                    ty => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "Cannot access element at index {} on {} of type {}",
                            index, checked_assignee, ty,
                        ),
                    }),
                }
            }
            Assignee::Member(box assignee, box member) => {
                let checked_assignee = self.check_assignee(assignee, module_id, types)?;

                let ty = checked_assignee.get_type();
                match &ty {
                    Type::Struct(members) => match members.iter().find(|m| m.id == member) {
                        Some(_) => Ok(TypedAssignee::Member(box checked_assignee, member.into())),
                        None => Err(ErrorInner {
                            pos: Some(pos),
                            message: format!(
                                "{} {{{}}} doesn't have member {}",
                                ty,
                                members
                                    .iter()
                                    .map(|m| format!("{}: {}", m.id, m.ty))
                                    .collect::<Vec<_>>()
                                    .join(", "),
                                member
                            ),
                        }),
                    },
                    ty => Err(ErrorInner {
                        pos: Some(pos),

                        message: format!(
                            "Cannot access field {} on {} of type {}",
                            member, checked_assignee, ty,
                        ),
                    }),
                }
            }
            Assignee::Element(box assignee, index) => {
                let checked_assignee = self.check_assignee(assignee, module_id, types)?;

                let ty = checked_assignee.get_type();
                match &ty {
                    Type::Tuple(tuple_ty) => match tuple_ty.elements.get(index as usize) {
                        Some(_) => Ok(TypedAssignee::Element(box checked_assignee, index)),
                        None => Err(ErrorInner {
                            pos: Some(pos),
                            message: format!(
                                "Tuple of size {} cannot be accessed at index {}",
                                tuple_ty.elements.len(),
                                index
                            ),
                        }),
                    },
                    ty => Err(ErrorInner {
                        pos: Some(pos),

                        message: format!(
                            "Cannot access element {} on {} of type {}",
                            index, checked_assignee, ty,
                        ),
                    }),
                }
            }
        }
    }

    fn check_spread_or_expression(
        &mut self,
        spread_or_expression: SpreadOrExpression<'ast>,
        module_id: &ModuleId,
        types: &TypeMap<'ast, T>,
    ) -> Result<TypedExpressionOrSpread<'ast, T>, ErrorInner> {
        match spread_or_expression {
            SpreadOrExpression::Spread(s) => {
                let pos = s.pos();

                let checked_expression =
                    self.check_expression(s.value.expression, module_id, types)?;

                match checked_expression {
                    TypedExpression::Array(a) => Ok(TypedExpressionOrSpread::Spread(a.into())),
                    e => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "Expected spread operator to apply on array, found {}",
                            e.get_type()
                        ),
                    }),
                }
            }
            SpreadOrExpression::Expression(e) => {
                self.check_expression(e, module_id, types).map(|r| r.into())
            }
        }
    }

    fn check_function_call_expression(
        &mut self,
        function_id: ExpressionNode<'ast>,
        generics: Option<Vec<Option<ExpressionNode<'ast>>>>,
        arguments: Vec<ExpressionNode<'ast>>,
        expected_return_type: Option<Type<'ast, T>>,
        module_id: &ModuleId,
        types: &TypeMap<'ast, T>,
    ) -> Result<TypedExpression<'ast, T>, ErrorInner> {
        let pos = function_id.pos();
        let fun_id = match function_id.value {
            Expression::Identifier(id) => Ok(id),
            e => Err(ErrorInner {
                pos: Some(pos),
                message: format!(
                    "Expected function in function call to be an identifier, found `{}`",
                    e
                ),
            }),
        }?;

        // check the generic arguments, if any
        let generics_checked: Option<Vec<Option<UExpression<'ast, T>>>> = generics
            .map(|generics| {
                generics
                    .into_iter()
                    .map(|g| {
                        g.map(|g| {
                            let pos = g.pos();
                            self.check_expression(g, module_id, types).and_then(|g| {
                                UExpression::try_from_typed(g, &UBitwidth::B32).map_err(|e| {
                                    ErrorInner {
                                        pos: Some(pos),
                                        message: format!(
                                            "Expected {} to be of type u32, found {}",
                                            e,
                                            e.get_type(),
                                        ),
                                    }
                                })
                            })
                        })
                        .transpose()
                    })
                    .collect::<Result<_, _>>()
            })
            .transpose()?;

        // check the arguments
        let mut arguments_checked = vec![];
        for arg in arguments {
            let arg_checked = self.check_expression(arg, module_id, types)?;
            arguments_checked.push(arg_checked);
        }

        let arguments_types: Vec<_> = arguments_checked.iter().map(|a| a.get_type()).collect();

        let query = FunctionQuery::new(
            fun_id,
            &generics_checked,
            &arguments_types,
            expected_return_type.clone(),
        );

        let functions = self.find_functions(&query);

        match functions.len() {
            // the function has to be defined
            1 => {
                let mut functions = functions;

                let f = functions.pop().unwrap();

                let signature = f.signature;

                let arguments_checked = arguments_checked.into_iter().zip(signature.inputs.iter()).map(|(a, t)| TypedExpression::align_to_type(a, t)).collect::<Result<Vec<_>, _>>().map_err(|e| ErrorInner {
                    pos: Some(pos),
                    message: format!("Expected function call argument to be of type `{}`, found `{}` of type `{}`", e.1, e.0, e.0.get_type())
                })?;

                let generics_checked = generics_checked.unwrap_or_else(|| vec![None; signature.generics.len()]);

                let output_type = expected_return_type.map(Ok).unwrap_or_else(|| signature.get_output_type(
                    generics_checked.clone(),
                    arguments_checked.iter().map(|a| a.get_type()).collect()
                ).map_err(|e| ErrorInner {
                    pos: Some(pos),
                    message: format!(
                        "Failed to infer value for generic parameter `{}`, try providing an explicit value",
                        e,
                    ),
                }))?;

                let function_key = DeclarationFunctionKey {
                    module: module_id.to_path_buf(),
                    id: f.id,
                    signature: signature.clone(),
                };

                match output_type {
                    Type::Int => unreachable!(),
                    Type::FieldElement => Ok(FieldElementExpression::function_call(
                        function_key,
                        generics_checked,
                        arguments_checked,
                    ).into()),
                    Type::Boolean => Ok(BooleanExpression::function_call(
                        function_key,
                        generics_checked,
                        arguments_checked,
                    ).into()),
                    Type::Uint(bitwidth) => Ok(UExpression::function_call(
                        function_key,
                        generics_checked,
                        arguments_checked,
                    ).annotate(bitwidth).into()),
                    Type::Struct(struct_ty) => Ok(StructExpression::function_call(
                        function_key,
                        generics_checked,
                        arguments_checked,
                    ).annotate(struct_ty).into()),
                    Type::Array(array_ty) => Ok(ArrayExpression::function_call(
                        function_key,
                        generics_checked,
                        arguments_checked,
                    ).annotate(*array_ty.ty, *array_ty.size).into()),
                    Type::Tuple(tuple_ty) => Ok(TupleExpression::function_call(
                        function_key,
                        generics_checked,
                        arguments_checked,
                    ).annotate(tuple_ty).into()),
                }
            }
            0 => Err(ErrorInner {
                pos: Some(pos),
                message: format!(
                    "Function definition for function {} with signature {} not found.",
                    fun_id, query
                ),
            }),
            n => Err(ErrorInner {
                pos: Some(pos),
                message: format!("Ambiguous call to function {}, {} candidates were found. Please be more explicit.", fun_id, n)
            }),
        }
    }

    fn check_expression(
        &mut self,
        expr: ExpressionNode<'ast>,
        module_id: &ModuleId,
        types: &TypeMap<'ast, T>,
    ) -> Result<TypedExpression<'ast, T>, ErrorInner> {
        let pos = expr.pos();

        match expr.value {
            Expression::IntConstant(v) => Ok(IntExpression::Value(v).into()),
            Expression::BooleanConstant(b) => Ok(BooleanExpression::Value(b).into()),
            Expression::Identifier(name) => {
                // check that `id` is defined in the scope
                match self.scope.get(&name) {
                    Some(info) => {
                        let id = info.id;
                        match info.ty.clone() {
                            Type::Boolean => Ok(BooleanExpression::Identifier(id.into()).into()),
                            Type::Uint(bitwidth) => Ok(UExpressionInner::Identifier(id.into())
                                .annotate(bitwidth)
                                .into()),
                            Type::FieldElement => {
                                Ok(FieldElementExpression::Identifier(id.into()).into())
                            }
                            Type::Array(array_type) => {
                                Ok(ArrayExpressionInner::Identifier(id.into())
                                    .annotate(*array_type.ty, *array_type.size)
                                    .into())
                            }
                            Type::Struct(members) => {
                                Ok(StructExpressionInner::Identifier(id.into())
                                    .annotate(members)
                                    .into())
                            }
                            Type::Tuple(tuple_ty) => {
                                Ok(TupleExpressionInner::Identifier(id.into())
                                    .annotate(tuple_ty)
                                    .into())
                            }
                            Type::Int => unreachable!(),
                        }
                    }
                    None => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!("Identifier \"{}\" is undefined", name),
                    }),
                }
            }
            Expression::Add(box e1, box e2) => {
                let e1_checked = self.check_expression(e1, module_id, types)?;
                let e2_checked = self.check_expression(e2, module_id, types)?;

                use self::TypedExpression::*;

                let (e1_checked, e2_checked) = TypedExpression::align_without_integers(
                    e1_checked, e2_checked,
                )
                .map_err(|(e1, e2)| ErrorInner {
                    pos: Some(pos),
                    message: format!("Cannot apply `+` to {}, {}", e1.get_type(), e2.get_type()),
                })?;

                match (e1_checked, e2_checked) {
                    (Int(e1), Int(e2)) => Ok(IntExpression::Add(box e1, box e2).into()),
                    (TypedExpression::FieldElement(e1), TypedExpression::FieldElement(e2)) => {
                        Ok(FieldElementExpression::Add(box e1, box e2).into())
                    }
                    (TypedExpression::Uint(e1), TypedExpression::Uint(e2))
                        if e1.get_type() == e2.get_type() =>
                    {
                        Ok((e1 + e2).into())
                    }
                    (t1, t2) => Err(ErrorInner {
                        pos: Some(pos),

                        message: format!(
                            "Cannot apply `+` to {}, {}",
                            t1.get_type(),
                            t2.get_type()
                        ),
                    }),
                }
            }
            Expression::Sub(box e1, box e2) => {
                let e1_checked = self.check_expression(e1, module_id, types)?;
                let e2_checked = self.check_expression(e2, module_id, types)?;

                use self::TypedExpression::*;

                let (e1_checked, e2_checked) = TypedExpression::align_without_integers(
                    e1_checked, e2_checked,
                )
                .map_err(|(e1, e2)| ErrorInner {
                    pos: Some(pos),
                    message: format!("Cannot apply `-` to {}, {}", e1.get_type(), e2.get_type()),
                })?;

                match (e1_checked, e2_checked) {
                    (Int(e1), Int(e2)) => Ok(IntExpression::Sub(box e1, box e2).into()),
                    (FieldElement(e1), FieldElement(e2)) => {
                        Ok(FieldElementExpression::Sub(box e1, box e2).into())
                    }
                    (Uint(e1), Uint(e2)) if e1.get_type() == e2.get_type() => Ok((e1 - e2).into()),
                    (t1, t2) => Err(ErrorInner {
                        pos: Some(pos),

                        message: format!(
                            "Expected only field elements, found {}, {}",
                            t1.get_type(),
                            t2.get_type()
                        ),
                    }),
                }
            }
            Expression::Mult(box e1, box e2) => {
                let e1_checked = self.check_expression(e1, module_id, types)?;
                let e2_checked = self.check_expression(e2, module_id, types)?;

                use self::TypedExpression::*;

                let (e1_checked, e2_checked) = TypedExpression::align_without_integers(
                    e1_checked, e2_checked,
                )
                .map_err(|(e1, e2)| ErrorInner {
                    pos: Some(pos),
                    message: format!("Cannot apply `*` to {}, {}", e1.get_type(), e2.get_type()),
                })?;

                match (e1_checked, e2_checked) {
                    (Int(e1), Int(e2)) => Ok(IntExpression::Mult(box e1, box e2).into()),
                    (TypedExpression::FieldElement(e1), TypedExpression::FieldElement(e2)) => {
                        Ok(FieldElementExpression::Mult(box e1, box e2).into())
                    }
                    (TypedExpression::Uint(e1), TypedExpression::Uint(e2))
                        if e1.get_type() == e2.get_type() =>
                    {
                        Ok((e1 * e2).into())
                    }
                    (t1, t2) => Err(ErrorInner {
                        pos: Some(pos),

                        message: format!(
                            "Cannot apply `*` to {}, {}",
                            t1.get_type(),
                            t2.get_type()
                        ),
                    }),
                }
            }
            Expression::Div(box e1, box e2) => {
                let e1_checked = self.check_expression(e1, module_id, types)?;
                let e2_checked = self.check_expression(e2, module_id, types)?;

                use self::TypedExpression::*;

                let (e1_checked, e2_checked) = TypedExpression::align_without_integers(
                    e1_checked, e2_checked,
                )
                .map_err(|(e1, e2)| ErrorInner {
                    pos: Some(pos),
                    message: format!("Cannot apply `/` to {}, {}", e1.get_type(), e2.get_type()),
                })?;

                match (e1_checked, e2_checked) {
                    (Int(e1), Int(e2)) => Ok(IntExpression::Div(box e1, box e2).into()),
                    (FieldElement(e1), FieldElement(e2)) => {
                        Ok(FieldElementExpression::Div(box e1, box e2).into())
                    }
                    (TypedExpression::Uint(e1), TypedExpression::Uint(e2))
                        if e1.get_type() == e2.get_type() =>
                    {
                        Ok((e1 / e2).into())
                    }
                    (t1, t2) => Err(ErrorInner {
                        pos: Some(pos),

                        message: format!(
                            "Cannot apply `/` to {}, {}",
                            t1.get_type(),
                            t2.get_type()
                        ),
                    }),
                }
            }
            Expression::Rem(box e1, box e2) => {
                let e1_checked = self.check_expression(e1, module_id, types)?;
                let e2_checked = self.check_expression(e2, module_id, types)?;

                let (e1_checked, e2_checked) = TypedExpression::align_without_integers(
                    e1_checked, e2_checked,
                )
                .map_err(|(e1, e2)| ErrorInner {
                    pos: Some(pos),
                    message: format!("Cannot apply `%` to {}, {}", e1.get_type(), e2.get_type()),
                })?;

                match (e1_checked, e2_checked) {
                    (TypedExpression::Uint(e1), TypedExpression::Uint(e2))
                        if e1.get_type() == e2.get_type() =>
                    {
                        Ok((e1 % e2).into())
                    }
                    (t1, t2) => Err(ErrorInner {
                        pos: Some(pos),

                        message: format!(
                            "Cannot apply `%` to {}, {}",
                            t1.get_type(),
                            t2.get_type()
                        ),
                    }),
                }
            }
            Expression::Pow(box e1, box e2) => {
                let e1_checked = self.check_expression(e1, module_id, types)?;
                let e2_checked = self.check_expression(e2, module_id, types)?;

                let e1_checked = match FieldElementExpression::try_from_typed(e1_checked) {
                    Ok(e) => e.into(),
                    Err(e) => e,
                };
                let e2_checked = match UExpression::try_from_typed(e2_checked, &UBitwidth::B32) {
                    Ok(e) => e.into(),
                    Err(e) => e,
                };

                match (e1_checked, e2_checked) {
                    (TypedExpression::FieldElement(e1), TypedExpression::Uint(e2)) => Ok(
                        TypedExpression::FieldElement(FieldElementExpression::Pow(box e1, box e2)),
                    ),
                    (t1, t2) => Err(ErrorInner {
                        pos: Some(pos),

                        message: format!(
                            "Expected `field` and `u32`, found {}, {}",
                            t1.get_type(),
                            t2.get_type()
                        ),
                    }),
                }
            }
            Expression::Neg(box e) => {
                let e = self.check_expression(e, module_id, types)?;

                match e {
                    TypedExpression::Int(e) => Ok(IntExpression::Neg(box e).into()),
                    TypedExpression::FieldElement(e) => {
                        Ok(FieldElementExpression::Neg(box e).into())
                    }
                    TypedExpression::Uint(e) => Ok((-e).into()),
                    e => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "Unary operator `-` cannot be applied to {} of type {}",
                            e,
                            e.get_type()
                        ),
                    }),
                }
            }
            Expression::Pos(box e) => {
                let e = self.check_expression(e, module_id, types)?;

                match e {
                    TypedExpression::Int(e) => Ok(IntExpression::Pos(box e).into()),
                    TypedExpression::FieldElement(e) => {
                        Ok(FieldElementExpression::Pos(box e).into())
                    }
                    TypedExpression::Uint(e) => Ok(UExpression::pos(e).into()),
                    e => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "Unary operator `+` cannot be applied to {} of type {}",
                            e,
                            e.get_type()
                        ),
                    }),
                }
            }
            Expression::Conditional(box conditional) => {
                let condition_checked =
                    self.check_expression(*conditional.condition, module_id, types)?;

                if !conditional.consequence_statements.is_empty()
                    || !conditional.alternative_statements.is_empty()
                {
                    return Err(ErrorInner {
                        pos: Some(pos),
                        message: "Statements are not supported in conditional branches".to_string(),
                    });
                }

                let consequence_checked =
                    self.check_expression(*conditional.consequence, module_id, types)?;
                let alternative_checked =
                    self.check_expression(*conditional.alternative, module_id, types)?;

                let (consequence_checked, alternative_checked) =
                    TypedExpression::align_without_integers(
                        consequence_checked,
                        alternative_checked,
                    )
                    .map_err(|(e1, e2)| ErrorInner {
                        pos: Some(pos),
                        message: format!("{{consequence}} and {{alternative}} in conditional expression should have the same type, found {}, {}", e1.get_type(), e2.get_type()),
                    })?;

                let kind = match conditional.kind {
                    zokrates_ast::untyped::ConditionalKind::IfElse => {
                        zokrates_ast::typed::ConditionalKind::IfElse
                    }
                    zokrates_ast::untyped::ConditionalKind::Ternary => {
                        zokrates_ast::typed::ConditionalKind::Ternary
                    }
                };

                match condition_checked {
                    TypedExpression::Boolean(condition) => {
                        match (consequence_checked, alternative_checked) {
                            (TypedExpression::FieldElement(consequence), TypedExpression::FieldElement(alternative)) => {
                                Ok(FieldElementExpression::conditional(condition, consequence, alternative, kind).into())
                            },
                            (TypedExpression::Boolean(consequence), TypedExpression::Boolean(alternative)) => {
                                Ok(BooleanExpression::conditional(condition, consequence, alternative, kind).into())
                            },
                            (TypedExpression::Array(consequence), TypedExpression::Array(alternative)) => {
                                Ok(ArrayExpression::conditional(condition, consequence, alternative, kind).into())
                            },
                            (TypedExpression::Struct(consequence), TypedExpression::Struct(alternative)) => {
                                Ok(StructExpression::conditional(condition, consequence, alternative, kind).into())
                            },
                            (TypedExpression::Tuple(consequence), TypedExpression::Tuple(alternative)) => {
                                Ok(TupleExpression::conditional(condition, consequence, alternative, kind).into())
                            },
                            (TypedExpression::Uint(consequence), TypedExpression::Uint(alternative)) => {
                                Ok(UExpression::conditional(condition, consequence, alternative, kind).into())
                            },
                            (TypedExpression::Int(consequence), TypedExpression::Int(alternative)) => {
                                Ok(IntExpression::conditional(condition, consequence, alternative, kind).into())
                            },
                            (c, a) => Err(ErrorInner {
                                pos: Some(pos),
                                message: format!("{{consequence}} and {{alternative}} in conditional expression should have the same type, found {}, {}", c.get_type(), a.get_type())
                            })
                        }
                    }
                    c => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "{{condition}} should be a boolean, found {}",
                            c.get_type()
                        ),
                    }),
                }
            }
            Expression::FieldConstant(n) => Ok(FieldElementExpression::Number(
                T::try_from(n).map_err(|_| ErrorInner {
                    pos: Some(pos),
                    message: format!(
                        "Field constant not in the representable range [{}, {}]",
                        T::min_value(),
                        T::max_value()
                    ),
                })?,
            )
            .into()),
            Expression::U8Constant(n) => Ok(UExpressionInner::Value(n.into()).annotate(8).into()),
            Expression::U16Constant(n) => Ok(UExpressionInner::Value(n.into()).annotate(16).into()),
            Expression::U32Constant(n) => Ok(UExpressionInner::Value(n.into()).annotate(32).into()),
            Expression::U64Constant(n) => Ok(UExpressionInner::Value(n.into()).annotate(64).into()),
            Expression::FunctionCall(box fun_id_expression, generics, arguments) => self
                .check_function_call_expression(
                    fun_id_expression,
                    generics,
                    arguments,
                    None,
                    module_id,
                    types,
                ),
            Expression::Lt(box e1, box e2) => {
                let e1_checked = self.check_expression(e1, module_id, types)?;
                let e2_checked = self.check_expression(e2, module_id, types)?;

                let (e1_checked, e2_checked) = TypedExpression::align_without_integers(
                    e1_checked, e2_checked,
                )
                .map_err(|(e1, e2)| ErrorInner {
                    pos: Some(pos),
                    message: format!(
                        "Cannot compare {} of type {} to {} of type {}",
                        e1,
                        e1.get_type(),
                        e2,
                        e2.get_type()
                    ),
                })?;

                match (e1_checked, e2_checked) {
                    (TypedExpression::FieldElement(e1), TypedExpression::FieldElement(e2)) => {
                        Ok(BooleanExpression::FieldLt(box e1, box e2).into())
                    }
                    (TypedExpression::Uint(e1), TypedExpression::Uint(e2)) => {
                        if e1.get_type() == e2.get_type() {
                            Ok(BooleanExpression::UintLt(box e1, box e2).into())
                        } else {
                            Err(ErrorInner {
                                pos: Some(pos),
                                message: format!(
                                    "Cannot compare {} of type {} to {} of type {}",
                                    e1,
                                    e1.get_type(),
                                    e2,
                                    e2.get_type()
                                ),
                            })
                        }
                    }
                    (e1, e2) => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "Cannot compare {} of type {} to {} of type {}",
                            e1,
                            e1.get_type(),
                            e2,
                            e2.get_type()
                        ),
                    }),
                }
            }
            Expression::Le(box e1, box e2) => {
                let e1_checked = self.check_expression(e1, module_id, types)?;
                let e2_checked = self.check_expression(e2, module_id, types)?;

                let (e1_checked, e2_checked) = TypedExpression::align_without_integers(
                    e1_checked, e2_checked,
                )
                .map_err(|(e1, e2)| ErrorInner {
                    pos: Some(pos),
                    message: format!(
                        "Cannot compare {} of type {} to {} of type {}",
                        e1,
                        e1.get_type(),
                        e2,
                        e2.get_type()
                    ),
                })?;

                match (e1_checked, e2_checked) {
                    (TypedExpression::FieldElement(e1), TypedExpression::FieldElement(e2)) => {
                        Ok(BooleanExpression::FieldLe(box e1, box e2).into())
                    }
                    (TypedExpression::Uint(e1), TypedExpression::Uint(e2)) => {
                        if e1.get_type() == e2.get_type() {
                            Ok(BooleanExpression::UintLe(box e1, box e2).into())
                        } else {
                            Err(ErrorInner {
                                pos: Some(pos),
                                message: format!(
                                    "Cannot compare {} of type {} to {} of type {}",
                                    e1,
                                    e1.get_type(),
                                    e2,
                                    e2.get_type()
                                ),
                            })
                        }
                    }
                    (e1, e2) => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "Cannot compare {} of type {} to {} of type {}",
                            e1,
                            e1.get_type(),
                            e2,
                            e2.get_type()
                        ),
                    }),
                }
            }
            Expression::Eq(box e1, box e2) => {
                let e1_checked = self.check_expression(e1, module_id, types)?;
                let e2_checked = self.check_expression(e2, module_id, types)?;

                let (e1_checked, e2_checked) = TypedExpression::align_without_integers(
                    e1_checked, e2_checked,
                )
                .map_err(|(e1, e2)| ErrorInner {
                    pos: Some(pos),
                    message: format!(
                        "Cannot compare {} of type {} to {} of type {}",
                        e1,
                        e1.get_type(),
                        e2,
                        e2.get_type()
                    ),
                })?;

                match (e1_checked, e2_checked) {
                    (TypedExpression::FieldElement(e1), TypedExpression::FieldElement(e2)) => {
                        Ok(BooleanExpression::FieldEq(EqExpression::new(e1, e2)).into())
                    }
                    (TypedExpression::Boolean(e1), TypedExpression::Boolean(e2)) => {
                        Ok(BooleanExpression::BoolEq(EqExpression::new(e1, e2)).into())
                    }
                    (TypedExpression::Array(e1), TypedExpression::Array(e2)) => {
                        Ok(BooleanExpression::ArrayEq(EqExpression::new(e1, e2)).into())
                    }
                    (TypedExpression::Struct(e1), TypedExpression::Struct(e2)) => {
                        Ok(BooleanExpression::StructEq(EqExpression::new(e1, e2)).into())
                    }
                    (TypedExpression::Tuple(e1), TypedExpression::Tuple(e2)) => {
                        Ok(BooleanExpression::TupleEq(EqExpression::new(e1, e2)).into())
                    }
                    (TypedExpression::Uint(e1), TypedExpression::Uint(e2))
                        if e1.get_type() == e2.get_type() =>
                    {
                        Ok(BooleanExpression::UintEq(EqExpression::new(e1, e2)).into())
                    }
                    (e1, e2) => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "Cannot compare {} of type {} to {} of type {}",
                            e1,
                            e1.get_type(),
                            e2,
                            e2.get_type()
                        ),
                    }),
                }
            }
            Expression::Ge(box e1, box e2) => {
                let e1_checked = self.check_expression(e1, module_id, types)?;
                let e2_checked = self.check_expression(e2, module_id, types)?;

                let (e1_checked, e2_checked) = TypedExpression::align_without_integers(
                    e1_checked, e2_checked,
                )
                .map_err(|(e1, e2)| ErrorInner {
                    pos: Some(pos),
                    message: format!(
                        "Cannot compare {} of type {} to {} of type {}",
                        e1,
                        e1.get_type(),
                        e2,
                        e2.get_type()
                    ),
                })?;

                match (e1_checked, e2_checked) {
                    (TypedExpression::FieldElement(e1), TypedExpression::FieldElement(e2)) => {
                        Ok(BooleanExpression::FieldGe(box e1, box e2).into())
                    }
                    (TypedExpression::Uint(e1), TypedExpression::Uint(e2)) => {
                        if e1.get_type() == e2.get_type() {
                            Ok(BooleanExpression::UintGe(box e1, box e2).into())
                        } else {
                            Err(ErrorInner {
                                pos: Some(pos),
                                message: format!(
                                    "Cannot compare {} of type {} to {} of type {}",
                                    e1,
                                    e1.get_type(),
                                    e2,
                                    e2.get_type()
                                ),
                            })
                        }
                    }
                    (e1, e2) => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "Cannot compare {} of type {} to {} of type {}",
                            e1,
                            e1.get_type(),
                            e2,
                            e2.get_type()
                        ),
                    }),
                }
            }
            Expression::Gt(box e1, box e2) => {
                let e1_checked = self.check_expression(e1, module_id, types)?;
                let e2_checked = self.check_expression(e2, module_id, types)?;

                let (e1_checked, e2_checked) = TypedExpression::align_without_integers(
                    e1_checked, e2_checked,
                )
                .map_err(|(e1, e2)| ErrorInner {
                    pos: Some(pos),
                    message: format!(
                        "Cannot compare {} of type {} to {} of type {}",
                        e1,
                        e1.get_type(),
                        e2,
                        e2.get_type()
                    ),
                })?;

                match (e1_checked, e2_checked) {
                    (TypedExpression::FieldElement(e1), TypedExpression::FieldElement(e2)) => {
                        Ok(BooleanExpression::FieldGt(box e1, box e2).into())
                    }
                    (TypedExpression::Uint(e1), TypedExpression::Uint(e2)) => {
                        if e1.get_type() == e2.get_type() {
                            Ok(BooleanExpression::UintGt(box e1, box e2).into())
                        } else {
                            Err(ErrorInner {
                                pos: Some(pos),
                                message: format!(
                                    "Cannot compare {} of type {} to {} of type {}",
                                    e1,
                                    e1.get_type(),
                                    e2,
                                    e2.get_type()
                                ),
                            })
                        }
                    }
                    (e1, e2) => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "Cannot compare {} of type {} to {} of type {}",
                            e1,
                            e1.get_type(),
                            e2,
                            e2.get_type()
                        ),
                    }),
                }
            }
            Expression::Select(box array, box index) => {
                let array = self.check_expression(array, module_id, types)?;

                match index {
                    RangeOrExpression::Range(r) => {
                        match array {
                            TypedExpression::Array(array) => {
                                let array_size = array.size();

                                let inner_type = array.inner_type().clone();

                                // check that the bounds are valid expressions
                                let from = r
                                    .value
                                    .from
                                    .map(|e| self.check_expression(e, module_id, types))
                                    .unwrap_or_else(|| Ok(UExpression::from(0u32).into()))?;

                                let to = r
                                    .value
                                    .to
                                    .map(|e| self.check_expression(e, module_id, types))
                                    .unwrap_or_else(|| Ok(array_size.clone().into()))?;

                                let from = UExpression::try_from_typed(from, &UBitwidth::B32).map_err(|e| ErrorInner {
                                                    pos: Some(pos),
                                                    message: format!(
                                                        "Expected the lower bound of the range to be a u32, found {} of type {}",
                                                        e,
                                                        e.get_type()
                                                    ),
                                                })?;

                                let to = UExpression::try_from_typed(to, &UBitwidth::B32).map_err(|e| ErrorInner {
                                                    pos: Some(pos),
                                                    message: format!(
                                                        "Expected the upper bound of the range to be a u32, found {} of type {}",
                                                        e,
                                                        e.get_type()
                                                    ),
                                                })?;

                                Ok(ArrayExpressionInner::Slice(
                                    box array,
                                    box from.clone(),
                                    box to.clone(),
                                )
                                .annotate(inner_type, UExpression::floor_sub(to, from))
                                .into())
                            }
                            e => Err(ErrorInner {
                                pos: Some(pos),
                                message: format!(
                                    "Cannot access slice of expression {} of type {}",
                                    e,
                                    e.get_type(),
                                ),
                            }),
                        }
                    }
                    RangeOrExpression::Expression(index) => {
                        let index = self.check_expression(index, module_id, types)?;

                        let index =
                            UExpression::try_from_typed(index, &UBitwidth::B32).map_err(|e| {
                                ErrorInner {
                                    pos: Some(pos),
                                    message: format!(
                                        "Expected index to be of type u32, found {}",
                                        e
                                    ),
                                }
                            })?;

                        match array {
                            TypedExpression::Array(a) => {
                                match a.inner_type().clone() {
                                    Type::FieldElement => {
                                        Ok(FieldElementExpression::select(a, index).into())
                                    }
                                    Type::Uint(..) => Ok(UExpression::select(a, index).into()),
                                    Type::Boolean => Ok(BooleanExpression::select(a, index).into()),
                                    Type::Array(..) => Ok(ArrayExpression::select(a, index).into()),
                                    Type::Struct(..) => Ok(StructExpression::select(a, index).into()),
                                    Type::Tuple(..) => Ok(TupleExpression::select(a, index).into()),
                                    Type::Int => unreachable!(),
                                }
                            }
                            a => Err(ErrorInner {
                                pos: Some(pos),
                                message: format!(
                                    "Cannot access element at index {} of type {} on expression {} of type {}",
                                    index,
                                    index.get_type(),
                                    a,
                                    a.get_type()
                                ),
                            }),
                        }
                    }
                }
            }
            Expression::Element(box e, index) => {
                let e = self.check_expression(e, module_id, types)?;
                match e {
                    TypedExpression::Tuple(t) => {
                        let ty = t.ty().elements.get(index as usize);

                        match ty {
                            Some(ty) => match ty {
                                Type::Int => unreachable!(),
                                Type::FieldElement => {
                                    Ok(FieldElementExpression::element(t, index).into())
                                }
                                Type::Boolean => Ok(BooleanExpression::element(t, index).into()),
                                Type::Uint(..) => Ok(UExpression::element(t, index).into()),
                                Type::Array(..) => Ok(ArrayExpression::element(t, index).into()),
                                Type::Struct(..) => Ok(StructExpression::element(t, index).into()),
                                Type::Tuple(..) => Ok(TupleExpression::element(t, index).into()),
                            },
                            None => Err(ErrorInner {
                                pos: Some(pos),
                                message: format!(
                                    "Tuple of size {} cannot be accessed at index {}",
                                    t.ty().elements.len(),
                                    index
                                ),
                            }),
                        }
                    }
                    e => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "Cannot access tuple element {} on expression of type {}",
                            index,
                            e.get_type()
                        ),
                    }),
                }
            }
            Expression::Member(box e, box id) => {
                let e = self.check_expression(e, module_id, types)?;

                match e {
                    TypedExpression::Struct(s) => {
                        // check that the struct has that field and return the type if it does
                        let ty = s.ty().iter().find(|m| m.id == id).map(|m| *m.ty.clone());

                        match ty {
                            Some(ty) => match ty {
                                Type::Int => unreachable!(),
                                Type::FieldElement => {
                                    Ok(FieldElementExpression::member(s, id.to_string()).into())
                                }
                                Type::Boolean => {
                                    Ok(BooleanExpression::member(s, id.to_string()).into())
                                }
                                Type::Uint(..) => Ok(UExpression::member(s, id.to_string()).into()),
                                Type::Array(..) => {
                                    Ok(ArrayExpression::member(s, id.to_string()).into())
                                }
                                Type::Struct(..) => {
                                    Ok(StructExpression::member(s, id.to_string()).into())
                                }
                                Type::Tuple(..) => {
                                    Ok(TupleExpression::member(s, id.to_string()).into())
                                }
                            },
                            None => Err(ErrorInner {
                                pos: Some(pos),
                                message: format!(
                                    "{} {{{}}} doesn't have member {}",
                                    s.get_type(),
                                    s.ty()
                                        .members
                                        .iter()
                                        .map(|m| format!("{}: {}", m.id, m.ty))
                                        .collect::<Vec<_>>()
                                        .join(", "),
                                    id,
                                ),
                            }),
                        }
                    }
                    e => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "Cannot access member {} on expression of type {}",
                            id,
                            e.get_type()
                        ),
                    }),
                }
            }
            Expression::InlineArray(expressions_or_spreads) => {
                // check each expression, getting its type
                let mut expressions_or_spreads_checked = vec![];
                for e in expressions_or_spreads {
                    let e_checked = self.check_spread_or_expression(e, module_id, types)?;
                    expressions_or_spreads_checked.push(e_checked);
                }

                if expressions_or_spreads_checked.is_empty() {
                    return Err(ErrorInner {
                        pos: Some(pos),
                        message: "Empty arrays are not allowed".to_string(),
                    });
                }

                // we infer the inner type to be the type of the first non-integer element
                // if there was no such element, then the array only has integers and we use that as the inner type
                let inferred_type = expressions_or_spreads_checked
                    .iter()
                    .filter_map(|e| match e.get_type() {
                        (Type::Int, _) => None,
                        (t, _) => Some(t),
                    })
                    .next()
                    .unwrap_or(Type::Int);

                let unwrapped_expressions_or_spreads = match inferred_type.clone() {
                    Type::Int => expressions_or_spreads_checked,
                    t => {
                        let target_array_ty =
                            ArrayType::new(t, UExpressionInner::Value(0).annotate(UBitwidth::B32));

                        expressions_or_spreads_checked
                            .into_iter()
                            .map(|e| {
                                TypedExpressionOrSpread::align_to_type(e, &target_array_ty).map_err(
                                    |(e, ty)| ErrorInner {
                                        pos: Some(pos),
                                        message: format!("Expected {} to have type {}", e, ty,),
                                    },
                                )
                            })
                            .collect::<Result<Vec<_>, _>>()?
                    }
                };

                // the size of the inline array is the sum of the size of its elements. However expressed as a u32 expression,
                // this value can be an tree of height n in the worst case, with n the size of the array (if all elements are
                // simple values and not spreads, 1 + 1 + 1 + ... 1)
                // To avoid that, we compute 2 sizes: the sum of all constant sizes as an u32 expression, and the
                // sum of all non constant sizes as a u32 number. We then return the sum of the two as a u32 expression.
                // `1 + 1 + ... + 1` is reduced to a single expression, which prevents this blowup

                let size: UExpression<'ast, T> = unwrapped_expressions_or_spreads
                    .iter()
                    .map(|e| e.size())
                    .fold(None, |acc, e| match acc {
                        Some((c_acc, e_acc)) => match e.as_inner() {
                            UExpressionInner::Value(e) => Some(((c_acc + *e as u32), e_acc)),
                            _ => Some((c_acc, e_acc + e)),
                        },
                        None => match e.as_inner() {
                            UExpressionInner::Value(e) => Some((*e as u32, 0u32.into())),
                            _ => Some((0u32, e)),
                        },
                    })
                    .map(|(c_size, e_size)| e_size + c_size.into())
                    .unwrap_or_else(|| 0u32.into());

                Ok(
                    ArrayExpressionInner::Value(unwrapped_expressions_or_spreads.into())
                        .annotate(inferred_type, size)
                        .into(),
                )
            }
            Expression::InlineTuple(elements) => {
                let elements: Vec<_> = elements
                    .into_iter()
                    .map(|e| self.check_expression(e, module_id, types))
                    .collect::<Result<_, _>>()?;
                let ty = TupleType::new(elements.iter().map(|e| e.get_type()).collect());
                Ok(TupleExpressionInner::Value(elements).annotate(ty).into())
            }
            Expression::ArrayInitializer(box e, box count) => {
                let e = self.check_expression(e, module_id, types)?;
                let ty = e.get_type();

                let count = self.check_expression(count, module_id, types)?;

                let count = UExpression::try_from_typed(count, &UBitwidth::B32).map_err(|e| {
                    ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "Expected array initializer count to be a u32, found {} of type {}",
                            e,
                            e.get_type(),
                        ),
                    }
                })?;

                Ok(ArrayExpressionInner::Repeat(box e, box count.clone())
                    .annotate(ty, count)
                    .into())
            }
            Expression::InlineStruct(id, inline_members) => {
                let ty = match types.get(module_id).unwrap().get(&id).cloned() {
                    None => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!("Undefined type `{}`", id),
                    }),
                    Some(ty) => Ok(ty),
                }?;

                let mut declared_struct_type = match ty.ty {
                    DeclarationType::Struct(struct_type) => struct_type,
                    _ => unreachable!(),
                };

                declared_struct_type.generics = (0..declared_struct_type.generics.len())
                    .map(|index| {
                        Some(DeclarationConstant::Generic(
                            GenericIdentifier::without_name().with_index(index),
                        ))
                    })
                    .collect();

                // check that we provided the required number of values
                if declared_struct_type.members_count() != inline_members.len() {
                    return Err(ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "Inline struct {} does not match {} {{{}}}",
                            Expression::InlineStruct(id, inline_members),
                            declared_struct_type,
                            declared_struct_type
                                .members
                                .iter()
                                .map(|m| format!("{}: {}", m.id, m.ty))
                                .collect::<Vec<_>>()
                                .join(", ")
                        ),
                    });
                }

                // check that the mapping of values matches the expected type
                // put the value into a map, pick members from this map following declared members, and try to parse them

                let mut inline_members_map = inline_members
                    .clone()
                    .into_iter()
                    .map(|(id, v)| (id.to_string(), v))
                    .collect::<BTreeMap<_, _>>();

                let inferred_values = declared_struct_type
                    .iter()
                    .map(
                        |member| match inline_members_map.remove(member.id.as_str()) {
                            Some(value) => {
                                let expression_checked =
                                    self.check_expression(value, module_id, types)?;

                                let expression_checked =
                                    TypedExpression::align_to_type(expression_checked, &*member.ty)
                                        .map_err(|e| ErrorInner {
                                            pos: Some(pos),
                                            message: format!(
                                        "Member {} of struct {} has type {}, found {} of type {}",
                                        member.id,
                                        id.clone(),
                                        e.1,
                                        e.0,
                                        e.0.get_type(),
                                    ),
                                        })?;

                                Ok(expression_checked)
                            }
                            None => Err(ErrorInner {
                                pos: Some(pos),
                                message: format!(
                                    "Member {} of struct {} {{{}}} not found in value {}",
                                    member.id,
                                    declared_struct_type,
                                    declared_struct_type
                                        .members
                                        .iter()
                                        .map(|m| format!("{}: {}", m.id, m.ty))
                                        .collect::<Vec<_>>()
                                        .join(", "),
                                    Expression::InlineStruct(id.clone(), inline_members.clone()),
                                ),
                            }),
                        },
                    )
                    .collect::<Result<Vec<_>, _>>()?;

                let mut generics_map = GGenericsAssignment::default();

                let members = declared_struct_type
                    .iter()
                    .zip(inferred_values.iter())
                    .map(|(m, v)| {
                        if !check_type(&m.ty, &v.get_type(), &mut generics_map) {
                            Err(ErrorInner {
                                pos: Some(pos),
                                message: format!(
                                    "Value `{}` doesn't match the expected type `{}` because of conflict in generic values",
                                    Expression::InlineStruct(id.clone(), inline_members.clone()),
                                    declared_struct_type
                                ),
                            })
                        } else {
                            Ok(StructMember {
                                id: m.id.clone(),
                                ty: box v.get_type().clone(),
                            })
                        }
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                let generics = generics_map.0.values().cloned().map(Some).collect();

                let inferred_struct_type = StructType {
                    canonical_location: declared_struct_type.canonical_location.clone(),
                    location: declared_struct_type.location,
                    generics,
                    members,
                };

                Ok(StructExpressionInner::Value(inferred_values)
                    .annotate(inferred_struct_type)
                    .into())
            }
            Expression::And(box e1, box e2) => {
                let e1_checked = self.check_expression(e1, module_id, types)?;
                let e2_checked = self.check_expression(e2, module_id, types)?;

                let (e1_checked, e2_checked) = TypedExpression::align_without_integers(
                    e1_checked, e2_checked,
                )
                .map_err(|(e1, e2)| ErrorInner {
                    pos: Some(pos),
                    message: format!(
                        "Cannot apply boolean operators to {} and {}",
                        e1.get_type(),
                        e2.get_type()
                    ),
                })?;

                match (e1_checked, e2_checked) {
                    (TypedExpression::Int(e1), TypedExpression::Int(e2)) => {
                        Ok(IntExpression::And(box e1, box e2).into())
                    }
                    (TypedExpression::Boolean(e1), TypedExpression::Boolean(e2)) => {
                        Ok(BooleanExpression::And(box e1, box e2).into())
                    }
                    (e1, e2) => Err(ErrorInner {
                        pos: Some(pos),

                        message: format!(
                            "Cannot apply boolean operators to {} and {}",
                            e1.get_type(),
                            e2.get_type()
                        ),
                    }),
                }
            }
            Expression::Or(box e1, box e2) => {
                let e1_checked = self.check_expression(e1, module_id, types)?;
                let e2_checked = self.check_expression(e2, module_id, types)?;
                match (e1_checked, e2_checked) {
                    (TypedExpression::Boolean(e1), TypedExpression::Boolean(e2)) => {
                        Ok(BooleanExpression::Or(box e1, box e2).into())
                    }
                    (e1, e2) => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "Cannot apply `||` to {}, {}",
                            e1.get_type(),
                            e2.get_type()
                        ),
                    }),
                }
            }
            Expression::LeftShift(box e1, box e2) => {
                let e1 = self.check_expression(e1, module_id, types)?;
                let e2 = self.check_expression(e2, module_id, types)?;

                let e2 =
                    UExpression::try_from_typed(e2, &UBitwidth::B32).map_err(|e| ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "Expected the left shift right operand to have type `u32`, found {}",
                            e
                        ),
                    })?;

                match e1 {
                    TypedExpression::Int(e1) => Ok(IntExpression::LeftShift(box e1, box e2).into()),
                    TypedExpression::Uint(e1) => Ok(UExpression::left_shift(e1, e2).into()),
                    e1 => Err(ErrorInner {
                        pos: Some(pos),

                        message: format!(
                            "Cannot left-shift {} by {}",
                            e1.get_type(),
                            e2.get_type()
                        ),
                    }),
                }
            }
            Expression::RightShift(box e1, box e2) => {
                let e1 = self.check_expression(e1, module_id, types)?;
                let e2 = self.check_expression(e2, module_id, types)?;

                let e2 =
                    UExpression::try_from_typed(e2, &UBitwidth::B32).map_err(|e| ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "Expected the right shift right operand to be of type `u32`, found {}",
                            e
                        ),
                    })?;

                match e1 {
                    TypedExpression::Int(e1) => {
                        Ok(IntExpression::RightShift(box e1, box e2).into())
                    }
                    TypedExpression::Uint(e1) => Ok(UExpression::right_shift(e1, e2).into()),
                    e1 => Err(ErrorInner {
                        pos: Some(pos),

                        message: format!(
                            "Cannot right-shift {} by {}",
                            e1.get_type(),
                            e2.get_type()
                        ),
                    }),
                }
            }
            Expression::BitOr(box e1, box e2) => {
                let e1_checked = self.check_expression(e1, module_id, types)?;
                let e2_checked = self.check_expression(e2, module_id, types)?;

                let (e1_checked, e2_checked) = TypedExpression::align_without_integers(
                    e1_checked, e2_checked,
                )
                .map_err(|(e1, e2)| ErrorInner {
                    pos: Some(pos),
                    message: format!("Cannot apply `|` to {}, {}", e1.get_type(), e2.get_type()),
                })?;

                match (e1_checked, e2_checked) {
                    (TypedExpression::Int(e1), TypedExpression::Int(e2)) => {
                        Ok(IntExpression::Or(box e1, box e2).into())
                    }
                    (TypedExpression::Uint(e1), TypedExpression::Uint(e2))
                        if e1.bitwidth() == e2.bitwidth() =>
                    {
                        Ok(UExpression::or(e1, e2).into())
                    }
                    (e1, e2) => Err(ErrorInner {
                        pos: Some(pos),

                        message: format!(
                            "Cannot apply `|` to {}, {}",
                            e1.get_type(),
                            e2.get_type()
                        ),
                    }),
                }
            }
            Expression::BitAnd(box e1, box e2) => {
                let e1_checked = self.check_expression(e1, module_id, types)?;
                let e2_checked = self.check_expression(e2, module_id, types)?;

                let (e1_checked, e2_checked) = TypedExpression::align_without_integers(
                    e1_checked, e2_checked,
                )
                .map_err(|(e1, e2)| ErrorInner {
                    pos: Some(pos),
                    message: format!("Cannot apply `&` to {}, {}", e1.get_type(), e2.get_type()),
                })?;

                match (e1_checked, e2_checked) {
                    (TypedExpression::Int(e1), TypedExpression::Int(e2)) => {
                        Ok(IntExpression::And(box e1, box e2).into())
                    }
                    (TypedExpression::Uint(e1), TypedExpression::Uint(e2))
                        if e1.bitwidth() == e2.bitwidth() =>
                    {
                        Ok(UExpression::and(e1, e2).into())
                    }
                    (e1, e2) => Err(ErrorInner {
                        pos: Some(pos),

                        message: format!(
                            "Cannot apply `&` to {}, {}",
                            e1.get_type(),
                            e2.get_type()
                        ),
                    }),
                }
            }
            Expression::BitXor(box e1, box e2) => {
                let e1_checked = self.check_expression(e1, module_id, types)?;
                let e2_checked = self.check_expression(e2, module_id, types)?;

                let (e1_checked, e2_checked) = TypedExpression::align_without_integers(
                    e1_checked, e2_checked,
                )
                .map_err(|(e1, e2)| ErrorInner {
                    pos: Some(pos),
                    message: format!("Cannot apply `^` to {}, {}", e1.get_type(), e2.get_type()),
                })?;

                match (e1_checked, e2_checked) {
                    (TypedExpression::Int(e1), TypedExpression::Int(e2)) => {
                        Ok(IntExpression::Xor(box e1, box e2).into())
                    }
                    (TypedExpression::Uint(e1), TypedExpression::Uint(e2))
                        if e1.bitwidth() == e2.bitwidth() =>
                    {
                        Ok(UExpression::xor(e1, e2).into())
                    }
                    (e1, e2) => Err(ErrorInner {
                        pos: Some(pos),

                        message: format!(
                            "Cannot apply `^` to {}, {}",
                            e1.get_type(),
                            e2.get_type()
                        ),
                    }),
                }
            }
            Expression::Not(box e) => {
                let e_checked = self.check_expression(e, module_id, types)?;
                match e_checked {
                    TypedExpression::Int(e) => Ok(IntExpression::Not(box e).into()),
                    TypedExpression::Boolean(e) => Ok(BooleanExpression::Not(box e).into()),
                    TypedExpression::Uint(e) => Ok((!e).into()),
                    e => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!("Cannot negate {}", e.get_type()),
                    }),
                }
            }
        }
    }

    fn insert_into_scope(
        &mut self,
        id: SourceIdentifier<'ast>,
        ty: Type<'ast, T>,
        is_mutable: bool,
    ) -> bool {
        let info = IdentifierInfo {
            id: self.id_in_this_scope(id),
            ty,
            is_mutable,
        };
        self.scope.insert(id, info)
    }

    fn find_functions(
        &self,
        query: &FunctionQuery<'ast, T>,
    ) -> Vec<DeclarationFunctionKey<'ast, T>> {
        query.match_funcs(&self.functions)
    }

    fn enter_scope(&mut self) {
        self.scope.enter();
    }

    fn exit_scope(&mut self) {
        self.scope.exit();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use lazy_static::lazy_static;
    use zokrates_ast::typed;
    use zokrates_ast::untyped;
    use zokrates_field::Bn128Field;

    lazy_static! {
        static ref MODULE_ID: OwnedModuleId = OwnedModuleId::from("");
    }
    mod constants {
        use super::*;

        use std::ops::Add;

        #[test]
        fn field_in_range() {
            // The value of `P - 1` is a valid field literal
            let expr = Expression::FieldConstant(Bn128Field::max_value().to_biguint()).mock();
            assert!(Checker::<Bn128Field>::default()
                .check_expression(expr, &*MODULE_ID, &TypeMap::new())
                .is_ok());
        }

        #[test]
        fn field_overflow() {
            // the value of `P` is an invalid field literal
            let value = Bn128Field::max_value().to_biguint().add(1u32);
            let expr = Expression::FieldConstant(value).mock();

            assert!(Checker::<Bn128Field>::default()
                .check_expression(expr, &*MODULE_ID, &TypeMap::new())
                .is_err());
        }
    }

    mod array {
        use super::*;
        use num_bigint::BigUint;

        #[test]
        fn element_type_mismatch() {
            // having different types in an array isn't allowed
            // in the case of arrays, lengths do *not* have to match, as at this point they can be
            // generic, so we cannot tell yet
            let types = TypeMap::new();

            // [3, true]
            let a = Expression::InlineArray(vec![
                Expression::IntConstant(3usize.into()).mock().into(),
                Expression::BooleanConstant(true).mock().into(),
            ])
            .mock();
            assert!(Checker::<Bn128Field>::default()
                .check_expression(a, &*MODULE_ID, &types)
                .is_err());

            // [[0f], [0f, 0f]]
            // accepted at this stage, as we do not check array lengths (as they can be variable)
            let a = Expression::InlineArray(vec![
                Expression::InlineArray(vec![Expression::FieldConstant(BigUint::from(0u32))
                    .mock()
                    .into()])
                .mock()
                .into(),
                Expression::InlineArray(vec![
                    Expression::FieldConstant(BigUint::from(0u32)).mock().into(),
                    Expression::FieldConstant(BigUint::from(0u32)).mock().into(),
                ])
                .mock()
                .into(),
            ])
            .mock();
            assert!(Checker::<Bn128Field>::default()
                .check_expression(a, &*MODULE_ID, &types)
                .is_ok());

            // [[0f], true]
            let a = Expression::InlineArray(vec![
                Expression::InlineArray(vec![Expression::FieldConstant(BigUint::from(0u32))
                    .mock()
                    .into()])
                .mock()
                .into(),
                Expression::InlineArray(vec![Expression::BooleanConstant(true).mock().into()])
                    .mock()
                    .into(),
            ])
            .mock();
            assert!(Checker::<Bn128Field>::default()
                .check_expression(a, &*MODULE_ID, &types)
                .is_err());
        }
    }

    /// Helper function to create: () { return; }
    fn function0() -> FunctionNode<'static> {
        let statements = vec![Statement::Return(None).mock()];

        let arguments = vec![];

        let signature = UnresolvedSignature::new();

        Function {
            arguments,
            statements,
            signature,
        }
        .mock()
    }

    /// Helper function to create: (private field a) { return; }
    fn function1() -> FunctionNode<'static> {
        let statements = vec![Statement::Return(None).mock()];

        let arguments = vec![untyped::Parameter {
            id: untyped::Variable::immutable("a", UnresolvedType::FieldElement.mock()).mock(),
            is_private: true,
        }
        .mock()];

        let signature =
            UnresolvedSignature::new().inputs(vec![UnresolvedType::FieldElement.mock()]);

        Function {
            arguments,
            statements,
            signature,
        }
        .mock()
    }

    mod symbols {
        use super::*;

        fn struct0() -> StructDefinitionNode<'static> {
            StructDefinition {
                generics: vec![],
                fields: vec![],
            }
            .mock()
        }

        fn struct1() -> StructDefinitionNode<'static> {
            StructDefinition {
                generics: vec![],
                fields: vec![StructDefinitionField {
                    id: "foo",
                    ty: UnresolvedType::FieldElement.mock(),
                }
                .mock()],
            }
            .mock()
        }

        #[test]
        fn unifier() {
            // the unifier should only accept either a single type or many functions of different signatures for each symbol

            let mut unifier = SymbolUnifier::<Bn128Field>::default();

            // the `foo` type
            assert!(unifier.insert_type("foo"));
            // the `foo` type annot be declared a second time
            assert!(!unifier.insert_type("foo"));
            // the `foo` function cannot be declared as the name is already taken by a type
            assert!(!unifier.insert_function("foo", DeclarationSignature::new()));
            // the `bar` type
            assert!(unifier.insert_function("bar", DeclarationSignature::new()));
            // a second `bar` function of the same signature cannot be declared
            assert!(!unifier.insert_function("bar", DeclarationSignature::new()));
            // a second `bar` function of a different signature can be declared
            assert!(unifier.insert_function(
                "bar",
                DeclarationSignature::new().inputs(vec![DeclarationType::FieldElement])
            ));
            // a second `bar` function with a generic parameter, which *could* conflict with an existing one should not be allowed
            assert!(!unifier.insert_function(
                "bar",
                DeclarationSignature::new()
                    .generics(vec![Some(
                        GenericIdentifier::with_name("K").with_index(0).into()
                    )])
                    .inputs(vec![DeclarationType::FieldElement])
            ));
            // a `bar` function with a different signature
            assert!(unifier.insert_function(
                "bar",
                DeclarationSignature::new()
                    .generics(vec![Some(
                        GenericIdentifier::with_name("K").with_index(0).into()
                    )])
                    .inputs(vec![DeclarationType::array((
                        DeclarationType::FieldElement,
                        GenericIdentifier::with_name("K").with_index(0)
                    ))])
            ));
            // a `bar` function with an equivalent signature, just renaming generic parameters
            assert!(!unifier.insert_function(
                "bar",
                DeclarationSignature::new()
                    .generics(vec![Some(
                        GenericIdentifier::with_name("L").with_index(0).into()
                    )])
                    .inputs(vec![DeclarationType::array((
                        DeclarationType::FieldElement,
                        GenericIdentifier::with_name("L").with_index(0)
                    ))])
            ));
            // a `bar` type isn't allowed as the name is already taken by at least one function
            assert!(!unifier.insert_type("bar"));
        }

        #[test]
        fn imported_function() {
            // foo.zok
            // def main() {
            //   return;
            // }

            // bar.zok
            // from "./foo.zok" import main;

            // after semantic check, `bar` should import a checked function

            let foo: Module = Module {
                symbols: vec![SymbolDeclaration {
                    id: "main",
                    symbol: Symbol::Here(SymbolDefinition::Function(function0())),
                }
                .mock()],
            };

            let bar: Module = Module {
                symbols: vec![SymbolDeclaration {
                    id: "main",
                    symbol: Symbol::There(SymbolImport::with_id_in_module("main", "foo").mock()),
                }
                .mock()],
            };

            let mut state = State::<Bn128Field>::new(
                vec![("foo".into(), foo), ("bar".into(), bar)]
                    .into_iter()
                    .collect(),
            );

            let mut checker: Checker<Bn128Field> = Checker::default();

            assert_eq!(
                checker.check_module(&OwnedTypedModuleId::from("bar"), &mut state),
                Ok(())
            );
            assert_eq!(
                state.typed_modules.get(&PathBuf::from("bar")),
                Some(&TypedModule {
                    symbols: vec![TypedFunctionSymbolDeclaration::new(
                        DeclarationFunctionKey::with_location("bar", "main")
                            .signature(DeclarationSignature::new()),
                        TypedFunctionSymbol::There(
                            DeclarationFunctionKey::with_location("foo", "main")
                                .signature(DeclarationSignature::new()),
                        )
                    )
                    .into()]
                    .into_iter()
                    .collect(),
                })
            );
        }

        #[test]
        fn duplicate_function_declaration() {
            // def foo() {
            //   return;
            // }
            // def foo() {
            //   return;
            // }
            //
            // should fail

            let module = Module {
                symbols: vec![
                    SymbolDeclaration {
                        id: "foo",
                        symbol: Symbol::Here(SymbolDefinition::Function(function0())),
                    }
                    .mock(),
                    SymbolDeclaration {
                        id: "foo",
                        symbol: Symbol::Here(SymbolDefinition::Function(function0())),
                    }
                    .mock(),
                ],
            };

            let mut state = State::<Bn128Field>::new(
                vec![((*MODULE_ID).clone(), module)].into_iter().collect(),
            );

            let mut checker: Checker<Bn128Field> = Checker::default();
            assert_eq!(
                checker.check_module(&*MODULE_ID, &mut state).unwrap_err()[0]
                    .inner
                    .message,
                "foo conflicts with another symbol"
            );
        }

        #[test]
        fn duplicate_function_declaration_generic() {
            // def foo<P>(private field[P] a) {
            //   return;
            // }
            // def foo(private field[3] a) {
            //   return;
            // }
            //
            // should succeed as P could be different from 3

            let mut f0 = function0();

            f0.value.arguments = vec![untyped::Parameter::private(
                untyped::Variable::immutable(
                    "a",
                    UnresolvedType::array(
                        UnresolvedType::FieldElement.mock(),
                        Expression::Identifier("P").mock(),
                    )
                    .mock(),
                )
                .mock(),
            )
            .mock()];
            f0.value.signature = UnresolvedSignature::new()
                .generics(vec!["P".mock()])
                .inputs(vec![UnresolvedType::array(
                    UnresolvedType::FieldElement.mock(),
                    Expression::Identifier("P").mock(),
                )
                .mock()]);

            let mut f1 = function0();

            f1.value.arguments = vec![untyped::Parameter::private(
                untyped::Variable::immutable(
                    "a",
                    UnresolvedType::array(
                        UnresolvedType::FieldElement.mock(),
                        Expression::U32Constant(3).mock(),
                    )
                    .mock(),
                )
                .mock(),
            )
            .mock()];
            f1.value.signature = UnresolvedSignature::new().inputs(vec![UnresolvedType::array(
                UnresolvedType::FieldElement.mock(),
                Expression::U32Constant(3).mock(),
            )
            .mock()]);

            let module = Module {
                symbols: vec![
                    SymbolDeclaration {
                        id: "foo",
                        symbol: Symbol::Here(SymbolDefinition::Function(f0)),
                    }
                    .mock(),
                    SymbolDeclaration {
                        id: "foo",
                        symbol: Symbol::Here(SymbolDefinition::Function(f1)),
                    }
                    .mock(),
                ],
            };

            let mut state = State::new(vec![((*MODULE_ID).clone(), module)].into_iter().collect());

            let mut checker: Checker<Bn128Field> = Checker::default();
            assert!(checker.check_module(&*MODULE_ID, &mut state).is_ok());
        }

        mod generics {
            use super::*;

            #[test]
            fn unused_generic() {
                // def foo<P>() {
                //   return;
                // }
                // def main() {
                //   return;
                // }
                //
                // should succeed

                let mut foo = function0();

                foo.value.signature = UnresolvedSignature::new().generics(vec!["P".mock()]);

                let module = Module {
                    symbols: vec![
                        SymbolDeclaration {
                            id: "foo",
                            symbol: Symbol::Here(SymbolDefinition::Function(foo)),
                        }
                        .mock(),
                        SymbolDeclaration {
                            id: "main",
                            symbol: Symbol::Here(SymbolDefinition::Function(function0())),
                        }
                        .mock(),
                    ],
                };

                let mut state =
                    State::new(vec![((*MODULE_ID).clone(), module)].into_iter().collect());

                let mut checker: Checker<Bn128Field> = Checker::default();
                assert!(checker.check_module(&*MODULE_ID, &mut state).is_ok());
            }

            #[test]
            fn undeclared_generic() {
                // def foo(field[P] a) {
                //   return;
                // }
                // def main() {
                //   return;
                // }
                //
                // should fail

                let mut foo = function0();

                foo.value.arguments = vec![untyped::Parameter::private(
                    untyped::Variable::immutable(
                        "a",
                        UnresolvedType::array(
                            UnresolvedType::FieldElement.mock(),
                            Expression::Identifier("P").mock(),
                        )
                        .mock(),
                    )
                    .mock(),
                )
                .mock()];
                foo.value.signature =
                    UnresolvedSignature::new().inputs(vec![UnresolvedType::array(
                        UnresolvedType::FieldElement.mock(),
                        Expression::Identifier("P").mock(),
                    )
                    .mock()]);

                let module = Module {
                    symbols: vec![
                        SymbolDeclaration {
                            id: "foo",
                            symbol: Symbol::Here(SymbolDefinition::Function(foo)),
                        }
                        .mock(),
                        SymbolDeclaration {
                            id: "main",
                            symbol: Symbol::Here(SymbolDefinition::Function(function0())),
                        }
                        .mock(),
                    ],
                };

                let mut state =
                    State::new(vec![((*MODULE_ID).clone(), module)].into_iter().collect());

                let mut checker: Checker<Bn128Field> = Checker::default();
                assert_eq!(
                    checker.check_module(&*MODULE_ID, &mut state).unwrap_err()[0]
                        .inner
                        .message,
                    "Undeclared symbol `P`"
                );
            }
        }

        #[test]
        fn overloaded_function_declaration() {
            // def foo() {
            //   return;
            // }
            // def foo(a) {
            //   return;
            // }
            //
            // should succeed as overloading is allowed

            let module = Module {
                symbols: vec![
                    SymbolDeclaration {
                        id: "foo",
                        symbol: Symbol::Here(SymbolDefinition::Function(function0())),
                    }
                    .mock(),
                    SymbolDeclaration {
                        id: "foo",
                        symbol: Symbol::Here(SymbolDefinition::Function(function1())),
                    }
                    .mock(),
                ],
            };

            let mut state = State::<Bn128Field>::new(
                vec![((*MODULE_ID).clone(), module)].into_iter().collect(),
            );

            let mut checker: Checker<Bn128Field> = Checker::default();
            assert_eq!(checker.check_module(&*MODULE_ID, &mut state), Ok(()));
            assert!(state
                .typed_modules
                .get(&*MODULE_ID)
                .unwrap()
                .functions_iter()
                .any(|d| d.key
                    == DeclarationFunctionKey::with_location((*MODULE_ID).clone(), "foo")
                        .signature(DeclarationSignature::new())));

            assert!(state
                .typed_modules
                .get(&*MODULE_ID)
                .unwrap()
                .functions_iter()
                .any(|d| d.key
                    == DeclarationFunctionKey::with_location((*MODULE_ID).clone(), "foo")
                        .signature(
                            DeclarationSignature::new().inputs(vec![DeclarationType::FieldElement])
                        )));
        }

        #[test]
        fn duplicate_type_declaration() {
            // struct Foo {}
            // struct Foo { foo: field; }
            //
            // should fail

            let module: Module = Module {
                symbols: vec![
                    SymbolDeclaration {
                        id: "foo",
                        symbol: Symbol::Here(SymbolDefinition::Struct(struct0())),
                    }
                    .mock(),
                    SymbolDeclaration {
                        id: "foo",
                        symbol: Symbol::Here(SymbolDefinition::Struct(struct1())),
                    }
                    .mock(),
                ],
            };

            let mut state = State::<Bn128Field>::new(
                vec![((*MODULE_ID).clone(), module)].into_iter().collect(),
            );

            let mut checker: Checker<Bn128Field> = Checker::default();
            assert_eq!(
                checker.check_module(&*MODULE_ID, &mut state).unwrap_err()[0]
                    .inner
                    .message,
                "foo conflicts with another symbol"
            );
        }

        #[test]
        fn type_function_conflict() {
            // struct foo {}
            // def foo() {
            //   return;
            // }
            //
            // should fail

            let module = Module {
                symbols: vec![
                    SymbolDeclaration {
                        id: "foo",
                        symbol: Symbol::Here(SymbolDefinition::Function(function0())),
                    }
                    .mock(),
                    SymbolDeclaration {
                        id: "foo",
                        symbol: Symbol::Here(SymbolDefinition::Struct(
                            StructDefinition {
                                generics: vec![],
                                fields: vec![],
                            }
                            .mock(),
                        )),
                    }
                    .mock(),
                ],
            };

            let mut state = State::<Bn128Field>::new(
                vec![((*MODULE_ID).clone(), module)].into_iter().collect(),
            );

            let mut checker: Checker<Bn128Field> = Checker::default();
            assert_eq!(
                checker.check_module(&*MODULE_ID, &mut state).unwrap_err()[0]
                    .inner
                    .message,
                "foo conflicts with another symbol"
            );
        }

        #[test]
        fn type_imported_function_conflict() {
            // import first

            // // bar.code
            // def main() { return; }
            //
            // // main.code
            // import main from "bar" as foo;
            // struct foo {}
            //
            // should fail

            let bar = Module::with_symbols(vec![SymbolDeclaration {
                id: "main",
                symbol: Symbol::Here(SymbolDefinition::Function(function0())),
            }
            .mock()]);

            let main = Module {
                symbols: vec![
                    SymbolDeclaration {
                        id: "foo",
                        symbol: Symbol::There(
                            SymbolImport::with_id_in_module("main", "bar").mock(),
                        ),
                    }
                    .mock(),
                    SymbolDeclaration {
                        id: "foo",
                        symbol: Symbol::Here(SymbolDefinition::Struct(struct0())),
                    }
                    .mock(),
                ],
            };

            let mut state = State::<Bn128Field>::new(
                vec![((*MODULE_ID).clone(), main), ("bar".into(), bar)]
                    .into_iter()
                    .collect(),
            );

            let mut checker: Checker<Bn128Field> = Checker::default();
            assert_eq!(
                checker.check_module(&*MODULE_ID, &mut state).unwrap_err()[0]
                    .inner
                    .message,
                "foo conflicts with another symbol"
            );

            // type declaration first

            // // bar.code
            // def main() { return; }
            //
            // // main.code
            // struct foo {}
            // import main from "bar" as foo;
            //
            // should fail

            let bar = Module::with_symbols(vec![SymbolDeclaration {
                id: "main",
                symbol: Symbol::Here(SymbolDefinition::Function(function0())),
            }
            .mock()]);

            let main = Module {
                symbols: vec![
                    SymbolDeclaration {
                        id: "foo",
                        symbol: Symbol::Here(SymbolDefinition::Struct(struct0())),
                    }
                    .mock(),
                    SymbolDeclaration {
                        id: "foo",
                        symbol: Symbol::There(
                            SymbolImport::with_id_in_module("main", "bar").mock(),
                        ),
                    }
                    .mock(),
                ],
            };

            let mut state = State::<Bn128Field>::new(
                vec![((*MODULE_ID).clone(), main), ("bar".into(), bar)]
                    .into_iter()
                    .collect(),
            );

            let mut checker: Checker<Bn128Field> = Checker::default();
            assert_eq!(
                checker.check_module(&*MODULE_ID, &mut state).unwrap_err()[0]
                    .inner
                    .message,
                "foo conflicts with another symbol"
            );
        }
    }

    fn new_with_args<'ast, T: Field>(
        scope: Scope<'ast, T>,
        functions: HashSet<DeclarationFunctionKey<'ast, T>>,
    ) -> Checker<'ast, T> {
        Checker {
            scope,
            functions,
            return_type: None,
        }
    }

    // checking function signatures
    mod signature {
        use super::*;

        #[test]
        fn undeclared_generic() {
            let modules = Modules::new();
            let state = State::new(modules);

            let signature = UnresolvedSignature::new().inputs(vec![UnresolvedType::Array(
                box UnresolvedType::FieldElement.mock(),
                Expression::Identifier("K").mock(),
            )
            .mock()]);
            assert_eq!(
                Checker::<Bn128Field>::default().check_signature(signature, &*MODULE_ID, &state),
                Err(vec![ErrorInner {
                    pos: Some((Position::mock(), Position::mock())),
                    message: "Undeclared symbol `K`".to_string()
                }])
            );
        }

        #[test]
        fn success() {
            // <K, L, M>(field[L][K]) -> field[L][K]
            let modules = Modules::new();
            let state = State::new(modules);

            let signature = UnresolvedSignature::new()
                .generics(vec!["K".mock(), "L".mock(), "M".mock()])
                .inputs(vec![UnresolvedType::Array(
                    box UnresolvedType::Array(
                        box UnresolvedType::FieldElement.mock(),
                        Expression::Identifier("K").mock(),
                    )
                    .mock(),
                    Expression::Identifier("L").mock(),
                )
                .mock()])
                .output(
                    UnresolvedType::Array(
                        box UnresolvedType::Array(
                            box UnresolvedType::FieldElement.mock(),
                            Expression::Identifier("L").mock(),
                        )
                        .mock(),
                        Expression::Identifier("K").mock(),
                    )
                    .mock(),
                );
            assert_eq!(
                Checker::<Bn128Field>::default().check_signature(signature, &*MODULE_ID, &state),
                Ok(DeclarationSignature::new()
                    .inputs(vec![DeclarationType::array((
                        DeclarationType::array((
                            DeclarationType::FieldElement,
                            GenericIdentifier::with_name("K").with_index(0)
                        )),
                        GenericIdentifier::with_name("L").with_index(1)
                    ))])
                    .output(DeclarationType::array((
                        DeclarationType::array((
                            DeclarationType::FieldElement,
                            GenericIdentifier::with_name("L").with_index(1)
                        )),
                        GenericIdentifier::with_name("K").with_index(0)
                    ))))
            );
        }
    }

    #[test]
    fn undefined_variable_in_statement() {
        // field a = b;
        // b undefined

        let statement: StatementNode = Statement::Definition(
            untyped::Variable::immutable("a", UnresolvedType::FieldElement.mock()).mock(),
            Expression::Identifier("b").mock(),
        )
        .mock();

        let mut checker: Checker<Bn128Field> = Checker::default();
        checker.enter_scope();

        assert_eq!(
            checker.check_statement(statement, &*MODULE_ID, &TypeMap::new()),
            Err(vec![ErrorInner {
                pos: Some((Position::mock(), Position::mock())),
                message: "Identifier \"b\" is undefined".into()
            }])
        );
    }

    #[test]
    fn defined_variable_in_statement() {
        // field a = b;
        // b defined
        let statement: StatementNode = Statement::Definition(
            untyped::Variable::immutable("a", UnresolvedType::FieldElement.mock()).mock(),
            Expression::Identifier("b").mock(),
        )
        .mock();

        let mut scope = Scope::default();
        scope.insert(
            "b",
            IdentifierInfo {
                id: "b".into(),
                ty: Type::FieldElement,
                is_mutable: false,
            },
        );

        let mut checker: Checker<Bn128Field> = new_with_args(scope, HashSet::new());
        checker.enter_scope();
        assert_eq!(
            checker.check_statement(statement, &*MODULE_ID, &TypeMap::new()),
            Ok(TypedStatement::definition(
                typed::Variable::field_element("a").into(),
                FieldElementExpression::Identifier("b".into()).into()
            ))
        );
    }

    #[test]
    fn declared_in_other_function() {
        // def foo() {
        //   field a = 1;
        //   return;
        // }
        // def bar() {
        //   return a;
        // }
        //
        // should fail
        let foo_args = vec![];
        let foo_statements = vec![
            Statement::Definition(
                untyped::Variable::immutable("a", UnresolvedType::FieldElement.mock()).mock(),
                Expression::IntConstant(1usize.into()).mock(),
            )
            .mock(),
            Statement::Return(None).mock(),
        ];
        let foo = Function {
            arguments: foo_args,
            statements: foo_statements,
            signature: UnresolvedSignature::new(),
        }
        .mock();

        let bar_args = vec![];
        let bar_statements =
            vec![Statement::Return(Some(Expression::Identifier("a").mock())).mock()];

        let bar = Function {
            arguments: bar_args,
            statements: bar_statements,
            signature: UnresolvedSignature::new()
                .inputs(vec![])
                .output(UnresolvedType::FieldElement.mock()),
        }
        .mock();

        let symbols = vec![
            SymbolDeclaration {
                id: "foo",
                symbol: Symbol::Here(SymbolDefinition::Function(foo)),
            }
            .mock(),
            SymbolDeclaration {
                id: "bar",
                symbol: Symbol::Here(SymbolDefinition::Function(bar)),
            }
            .mock(),
        ];
        let module = Module { symbols };

        let mut state =
            State::<Bn128Field>::new(vec![((*MODULE_ID).clone(), module)].into_iter().collect());

        let mut checker: Checker<Bn128Field> = Checker::default();
        assert_eq!(
            checker.check_module(&*MODULE_ID, &mut state),
            Err(vec![Error {
                inner: ErrorInner {
                    pos: Some((Position::mock(), Position::mock())),
                    message: "Identifier \"a\" is undefined".into()
                },
                module_id: (*MODULE_ID).clone()
            }])
        );
    }

    #[test]
    fn declared_in_two_scopes() {
        // def foo() {
        //   field a = 1;
        //   return;
        // }
        // def bar() {
        //   field a = 2;
        //   return;
        // }
        // def main() {
        //   return 1;
        // }
        // should pass
        let foo_args = vec![];
        let foo_statements = vec![
            Statement::Definition(
                untyped::Variable::immutable("a", UnresolvedType::FieldElement.mock()).mock(),
                Expression::IntConstant(1usize.into()).mock(),
            )
            .mock(),
            Statement::Return(None).mock(),
        ];

        let foo = Function {
            arguments: foo_args,
            statements: foo_statements,
            signature: UnresolvedSignature::new(),
        }
        .mock();

        let bar_args = vec![];
        let bar_statements = vec![
            Statement::Definition(
                untyped::Variable::immutable("a", UnresolvedType::FieldElement.mock()).mock(),
                Expression::IntConstant(2usize.into()).mock(),
            )
            .mock(),
            Statement::Return(None).mock(),
        ];
        let bar = Function {
            arguments: bar_args,
            statements: bar_statements,
            signature: UnresolvedSignature::new(),
        }
        .mock();

        let main_args = vec![];
        let main_statements =
            vec![Statement::Return(Some(Expression::IntConstant(1usize.into()).mock())).mock()];

        let main = Function {
            arguments: main_args,
            statements: main_statements,
            signature: UnresolvedSignature::new()
                .inputs(vec![])
                .output(UnresolvedType::FieldElement.mock()),
        }
        .mock();

        let symbols = vec![
            SymbolDeclaration {
                id: "foo",
                symbol: Symbol::Here(SymbolDefinition::Function(foo)),
            }
            .mock(),
            SymbolDeclaration {
                id: "bar",
                symbol: Symbol::Here(SymbolDefinition::Function(bar)),
            }
            .mock(),
            SymbolDeclaration {
                id: "main",
                symbol: Symbol::Here(SymbolDefinition::Function(main)),
            }
            .mock(),
        ];
        let module = Module { symbols };

        let mut state =
            State::<Bn128Field>::new(vec![((*MODULE_ID).clone(), module)].into_iter().collect());

        let mut checker: Checker<Bn128Field> = Checker::default();
        assert!(checker.check_module(&*MODULE_ID, &mut state).is_ok());
    }

    #[test]
    fn for_index_after_end() {
        // def foo() {
        //   for u32 i in 0..10 { }
        //   return i;
        // }
        // should fail
        let foo_statements: Vec<StatementNode> = vec![
            Statement::For(
                untyped::Variable::immutable("i", UnresolvedType::Uint(32).mock()).mock(),
                Expression::IntConstant(0usize.into()).mock(),
                Expression::IntConstant(10usize.into()).mock(),
                vec![],
            )
            .mock(),
            Statement::Return(Some(Expression::Identifier("i").mock())).mock(),
        ];
        let foo = Function {
            arguments: vec![],
            statements: foo_statements,
            signature: UnresolvedSignature::new()
                .inputs(vec![])
                .output(UnresolvedType::FieldElement.mock()),
        }
        .mock();

        let modules = Modules::new();
        let state = State::new(modules);

        let mut checker: Checker<Bn128Field> = Checker::default();
        assert_eq!(
            checker.check_function(foo, &*MODULE_ID, &state),
            Err(vec![ErrorInner {
                pos: Some((Position::mock(), Position::mock())),
                message: "Identifier \"i\" is undefined".into()
            }])
        );
    }

    #[test]
    fn for_index_in_for() {
        // def foo() {
        //   for u32 i in 0..10 {
        //     field a = i;
        //   }
        //   return;
        // }
        // should pass

        let for_statements = vec![Statement::Definition(
            untyped::Variable::immutable("a", UnresolvedType::Uint(32).mock()).mock(),
            Expression::Identifier("i").mock(),
        )
        .mock()];

        let foo_statements = vec![
            Statement::For(
                untyped::Variable::immutable("i", UnresolvedType::Uint(32).mock()).mock(),
                Expression::IntConstant(0usize.into()).mock(),
                Expression::IntConstant(10usize.into()).mock(),
                for_statements,
            )
            .mock(),
            Statement::Return(None).mock(),
        ];

        let for_statements_checked = vec![TypedStatement::definition(
            typed::Variable::uint(
                CoreIdentifier::Source(ShadowedIdentifier::shadow("a", 1)),
                UBitwidth::B32,
            )
            .into(),
            UExpressionInner::Identifier(
                CoreIdentifier::Source(ShadowedIdentifier::shadow("i", 1)).into(),
            )
            .annotate(UBitwidth::B32)
            .into(),
        )];

        let foo_statements_checked = vec![
            TypedStatement::For(
                typed::Variable::uint(
                    CoreIdentifier::Source(ShadowedIdentifier::shadow("i", 1)),
                    UBitwidth::B32,
                ),
                0u32.into(),
                10u32.into(),
                for_statements_checked,
            ),
            TypedStatement::Return(TypedExpression::empty_tuple()),
        ];

        let foo = Function {
            arguments: vec![],
            statements: foo_statements,
            signature: UnresolvedSignature::new(),
        }
        .mock();

        let foo_checked = TypedFunction {
            arguments: vec![],
            statements: foo_statements_checked,
            signature: DeclarationSignature::default(),
        };

        let modules = Modules::new();
        let state = State::new(modules);

        let mut checker: Checker<Bn128Field> = Checker::default();
        assert_eq!(
            checker.check_function(foo, &*MODULE_ID, &state),
            Ok(foo_checked)
        );
    }

    #[test]
    fn arity_mismatch() {
        // def foo() -> bool {
        //   return true;
        // }
        // def bar() {
        //   field a = foo();
        //   return;
        // }
        // should fail
        let bar_statements: Vec<StatementNode> = vec![
            Statement::Definition(
                untyped::Variable::immutable("a", UnresolvedType::FieldElement.mock()).mock(),
                Expression::FunctionCall(box Expression::Identifier("foo").mock(), None, vec![])
                    .mock(),
            )
            .mock(),
            Statement::Return(None).mock(),
        ];

        let foo = DeclarationFunctionKey {
            module: (*MODULE_ID).clone(),
            id: "foo",
            signature: DeclarationSignature::new()
                .inputs(vec![])
                .output(DeclarationType::Boolean),
        };

        let functions = vec![foo].into_iter().collect();

        let bar = Function {
            arguments: vec![],
            statements: bar_statements,
            signature: UnresolvedSignature::new(),
        }
        .mock();

        let modules = Modules::new();
        let state = State::new(modules);

        let mut checker: Checker<Bn128Field> = new_with_args(Scope::default(), functions);
        assert_eq!(
            checker.check_function(bar, &*MODULE_ID, &state),
            Err(vec![ErrorInner {
                pos: Some((Position::mock(), Position::mock())),
                message:
                    "Function definition for function foo with signature () -> field not found."
                        .into()
            }])
        );
    }

    #[test]
    fn function_undefined_in_definition() {
        // def bar() {
        //   field a = foo();
        //   return;
        // }
        // should fail
        let bar_statements: Vec<StatementNode> = vec![
            Statement::Definition(
                untyped::Variable::immutable("a", UnresolvedType::FieldElement.mock()).mock(),
                Expression::FunctionCall(box Expression::Identifier("foo").mock(), None, vec![])
                    .mock(),
            )
            .mock(),
            Statement::Return(None).mock(),
        ];

        let bar = Function {
            arguments: vec![],
            statements: bar_statements,
            signature: UnresolvedSignature::new(),
        }
        .mock();

        let modules = Modules::new();
        let state = State::new(modules);

        let mut checker: Checker<Bn128Field> = new_with_args(Scope::default(), HashSet::new());
        assert_eq!(
            checker.check_function(bar, &*MODULE_ID, &state),
            Err(vec![ErrorInner {
                pos: Some((Position::mock(), Position::mock())),

                message:
                    "Function definition for function foo with signature () -> field not found."
                        .into()
            }])
        );
    }

    #[test]
    fn undeclared_variable() {
        // def foo() -> field {
        //   return 1;
        // }
        // def main() {
        //   a = foo();
        //   return;
        // }
        // should fail

        let foo_statements: Vec<StatementNode> =
            vec![Statement::Return(Some(Expression::IntConstant(1usize.into()).mock())).mock()];

        let foo = Function {
            arguments: vec![],
            statements: foo_statements,
            signature: UnresolvedSignature::new()
                .inputs(vec![])
                .output(UnresolvedType::FieldElement.mock()),
        }
        .mock();

        let main_statements: Vec<StatementNode> = vec![
            Statement::Assignment(
                Assignee::Identifier("a").mock(),
                Expression::FunctionCall(box Expression::Identifier("foo").mock(), None, vec![])
                    .mock(),
            )
            .mock(),
            Statement::Return(None).mock(),
        ];

        let main = Function {
            arguments: vec![],
            statements: main_statements,
            signature: UnresolvedSignature::new()
                .inputs(vec![])
                .output(UnresolvedType::Tuple(vec![]).mock()),
        }
        .mock();

        let module = Module {
            symbols: vec![
                SymbolDeclaration {
                    id: "foo",
                    symbol: Symbol::Here(SymbolDefinition::Function(foo)),
                }
                .mock(),
                SymbolDeclaration {
                    id: "main",
                    symbol: Symbol::Here(SymbolDefinition::Function(main)),
                }
                .mock(),
            ],
        };

        let mut state =
            State::<Bn128Field>::new(vec![((*MODULE_ID).clone(), module)].into_iter().collect());

        let mut checker: Checker<Bn128Field> = new_with_args(Scope::default(), HashSet::new());
        assert_eq!(
            checker.check_module(&*MODULE_ID, &mut state),
            Err(vec![Error {
                inner: ErrorInner {
                    pos: Some((Position::mock(), Position::mock())),
                    message: "Variable `a` is undeclared".into()
                },
                module_id: (*MODULE_ID).clone()
            }])
        );
    }

    #[test]
    fn assign_to_select() {
        // def foo() -> field {
        //   return 1;
        // }
        // def main() {
        //   field[1] mut a = [0];
        //   a[0] = foo();
        //   return;
        // }
        // should succeed

        let foo_statements: Vec<StatementNode> =
            vec![Statement::Return(Some(Expression::IntConstant(1usize.into()).mock())).mock()];

        let foo = Function {
            arguments: vec![],
            statements: foo_statements,
            signature: UnresolvedSignature::new()
                .inputs(vec![])
                .output(UnresolvedType::FieldElement.mock()),
        }
        .mock();

        let main_statements: Vec<StatementNode> = vec![
            Statement::Definition(
                untyped::Variable::mutable(
                    "a",
                    UnresolvedType::array(
                        UnresolvedType::FieldElement.mock(),
                        Expression::IntConstant(1usize.into()).mock(),
                    )
                    .mock(),
                )
                .mock(),
                Expression::InlineArray(vec![untyped::SpreadOrExpression::Expression(
                    Expression::IntConstant(0usize.into()).mock(),
                )])
                .mock(),
            )
            .mock(),
            Statement::Assignment(
                Assignee::Select(
                    box Assignee::Identifier("a").mock(),
                    box RangeOrExpression::Expression(
                        untyped::Expression::IntConstant(0usize.into()).mock(),
                    ),
                )
                .mock(),
                Expression::FunctionCall(box Expression::Identifier("foo").mock(), None, vec![])
                    .mock(),
            )
            .mock(),
            Statement::Return(None).mock(),
        ];

        let main = Function {
            arguments: vec![],
            statements: main_statements,
            signature: UnresolvedSignature::new()
                .inputs(vec![])
                .output(UnresolvedType::Tuple(vec![]).mock()),
        }
        .mock();

        let module = Module {
            symbols: vec![
                SymbolDeclaration {
                    id: "foo",
                    symbol: Symbol::Here(SymbolDefinition::Function(foo)),
                }
                .mock(),
                SymbolDeclaration {
                    id: "main",
                    symbol: Symbol::Here(SymbolDefinition::Function(main)),
                }
                .mock(),
            ],
        };

        let mut state =
            State::<Bn128Field>::new(vec![((*MODULE_ID).clone(), module)].into_iter().collect());

        let mut checker: Checker<Bn128Field> = new_with_args(Scope::default(), HashSet::new());
        assert!(checker.check_module(&*MODULE_ID, &mut state).is_ok());
    }

    #[test]
    fn function_undefined() {
        // def bar() {
        //   assert(1 == foo());
        //   return;
        // }
        // should fail

        let bar_statements: Vec<StatementNode> = vec![
            Statement::Assertion(
                Expression::Eq(
                    box Expression::IntConstant(1usize.into()).mock(),
                    box Expression::FunctionCall(
                        box Expression::Identifier("foo").mock(),
                        None,
                        vec![],
                    )
                    .mock(),
                )
                .mock(),
                None,
            )
            .mock(),
            Statement::Return(None).mock(),
        ];

        let bar = Function {
            arguments: vec![],
            statements: bar_statements,
            signature: UnresolvedSignature::new(),
        }
        .mock();

        let modules = Modules::new();
        let state = State::new(modules);

        let mut checker: Checker<Bn128Field> = new_with_args(Scope::default(), HashSet::new());
        assert_eq!(
            checker.check_function(bar, &*MODULE_ID, &state),
            Err(vec![ErrorInner {
                pos: Some((Position::mock(), Position::mock())),

                message: "Function definition for function foo with signature () -> _ not found."
                    .into()
            }])
        );
    }

    #[test]
    fn return_undefined() {
        // def bar() {
        //   return a;
        // }
        // should fail
        let bar_statements: Vec<StatementNode> =
            vec![Statement::Return(Some(Expression::Identifier("a").mock())).mock()];

        let bar = Function {
            arguments: vec![],
            statements: bar_statements,
            signature: UnresolvedSignature::new()
                .inputs(vec![])
                .output(UnresolvedType::FieldElement.mock()),
        }
        .mock();

        let modules = Modules::new();
        let state = State::new(modules);

        let mut checker: Checker<Bn128Field> = new_with_args(Scope::default(), HashSet::new());
        assert_eq!(
            checker.check_function(bar, &*MODULE_ID, &state),
            Err(vec![ErrorInner {
                pos: Some((Position::mock(), Position::mock())),
                message: "Identifier \"a\" is undefined".into()
            }])
        );
    }

    #[test]
    fn duplicate_argument_name() {
        // def main(field a, bool a) {
        //   return;
        // }
        //
        // should fail

        let mut f = function0();
        f.value.arguments = vec![
            untyped::Parameter::private(
                untyped::Variable::immutable("a", UnresolvedType::FieldElement.mock()).mock(),
            )
            .mock(),
            untyped::Parameter::private(
                untyped::Variable::immutable("a", UnresolvedType::Boolean.mock()).mock(),
            )
            .mock(),
        ];
        f.value.signature = UnresolvedSignature::new().inputs(vec![
            UnresolvedType::FieldElement.mock(),
            UnresolvedType::Boolean.mock(),
        ]);

        let modules = Modules::new();
        let state = State::new(modules);

        let mut checker: Checker<Bn128Field> = new_with_args(Scope::default(), HashSet::new());
        assert_eq!(
            checker
                .check_function(f, &*MODULE_ID, &state)
                .unwrap_err()[0]
                .message,
            "Duplicate name in function definition: `a` was previously declared as an argument, a generic parameter or a constant"
        );
    }

    #[test]
    fn duplicate_main_function() {
        // def main(a) -> field {
        //   return 1;
        // }
        // def main() -> field {
        //   return 1;
        // }
        //
        // should fail
        let main1_statements: Vec<StatementNode> =
            vec![Statement::Return(Some(Expression::IntConstant(1usize.into()).mock())).mock()];

        let main1_arguments = vec![zokrates_ast::untyped::Parameter {
            id: untyped::Variable::immutable("a", UnresolvedType::FieldElement.mock()).mock(),
            is_private: false,
        }
        .mock()];

        let main2_statements: Vec<StatementNode> =
            vec![Statement::Return(Some(Expression::IntConstant(1usize.into()).mock())).mock()];

        let main2_arguments = vec![];

        let main1 = Function {
            arguments: main1_arguments,
            statements: main1_statements,
            signature: UnresolvedSignature::new()
                .inputs(vec![UnresolvedType::FieldElement.mock()])
                .output(UnresolvedType::FieldElement.mock()),
        }
        .mock();

        let main2 = Function {
            arguments: main2_arguments,
            statements: main2_statements,
            signature: UnresolvedSignature::new()
                .inputs(vec![])
                .output(UnresolvedType::FieldElement.mock()),
        }
        .mock();

        let symbols = vec![
            SymbolDeclaration {
                id: "main",
                symbol: Symbol::Here(SymbolDefinition::Function(main1)),
            }
            .mock(),
            SymbolDeclaration {
                id: "main",
                symbol: Symbol::Here(SymbolDefinition::Function(main2)),
            }
            .mock(),
        ];

        let main_module = Module { symbols };

        let program = Program {
            modules: vec![((*MODULE_ID).clone(), main_module)]
                .into_iter()
                .collect(),
            main: (*MODULE_ID).clone(),
        };

        let mut checker: Checker<Bn128Field> = Checker::default();
        assert_eq!(
            checker.check_program(program),
            Err(vec![Error {
                inner: ErrorInner {
                    pos: None,
                    message: "Only one main function allowed, found 2".into()
                },
                module_id: (*MODULE_ID).clone()
            }])
        );
    }

    mod shadowing {

        use super::*;

        #[test]
        fn same_type() {
            // field a = 2;
            // field a = 2;
            //
            // should succeed

            let mut checker: Checker<Bn128Field> = Checker::default();
            checker.enter_scope();
            let _: Result<TypedStatement<Bn128Field>, Vec<ErrorInner>> = checker.check_statement(
                Statement::Definition(
                    untyped::Variable::immutable("a", UnresolvedType::FieldElement.mock()).mock(),
                    untyped::Expression::IntConstant(2usize.into()).mock(),
                )
                .mock(),
                &*MODULE_ID,
                &TypeMap::new(),
            );
            let s2_checked: Result<TypedStatement<Bn128Field>, Vec<ErrorInner>> = checker
                .check_statement(
                    Statement::Definition(
                        untyped::Variable::immutable("a", UnresolvedType::FieldElement.mock())
                            .mock(),
                        untyped::Expression::IntConstant(2usize.into()).mock(),
                    )
                    .mock(),
                    &*MODULE_ID,
                    &TypeMap::new(),
                );
            assert!(s2_checked.is_ok());
        }

        #[test]
        fn different_type() {
            // field a = 2;
            // bool a = true;
            //
            // should succeed

            let mut checker: Checker<Bn128Field> = Checker::default();
            checker.enter_scope();
            let _: Result<TypedStatement<Bn128Field>, Vec<ErrorInner>> = checker.check_statement(
                Statement::Definition(
                    untyped::Variable::immutable("a", UnresolvedType::FieldElement.mock()).mock(),
                    untyped::Expression::IntConstant(2usize.into()).mock(),
                )
                .mock(),
                &*MODULE_ID,
                &TypeMap::new(),
            );
            let s2_checked: Result<TypedStatement<Bn128Field>, Vec<ErrorInner>> = checker
                .check_statement(
                    Statement::Definition(
                        untyped::Variable::immutable("a", UnresolvedType::Boolean.mock()).mock(),
                        untyped::Expression::BooleanConstant(true).mock(),
                    )
                    .mock(),
                    &*MODULE_ID,
                    &TypeMap::new(),
                );
            assert!(s2_checked.is_ok());
            assert_eq!(
                checker.scope.get(&"a").unwrap().ty,
                DeclarationType::Boolean
            );
        }

        #[test]
        fn scopes() {
            // field mut a = 2;
            // for uint i in 0..0 {
            //    a = 3
            //    field a = 4
            // }
            // a = 5
            //
            // should be turned into
            //
            // field mut a_0 = 2;
            // for uint i_1 in 0..0 {
            //    a_0 = 3
            //    field a_1 = 4
            // }
            // a_0 = 5

            let mut checker: Checker<Bn128Field> = Checker::default();

            let statements = vec![
                Statement::Definition(
                    untyped::Variable::mutable("a", UnresolvedType::FieldElement.mock()).mock(),
                    untyped::Expression::IntConstant(2usize.into()).mock(),
                )
                .mock(),
                Statement::For(
                    untyped::Variable::immutable("i", UnresolvedType::Uint(32).mock()).mock(),
                    untyped::Expression::U32Constant(0).mock(),
                    untyped::Expression::U32Constant(0).mock(),
                    vec![
                        Statement::Assignment(
                            untyped::Assignee::Identifier("a").mock(),
                            untyped::Expression::IntConstant(3usize.into()).mock(),
                        )
                        .mock(),
                        Statement::Definition(
                            untyped::Variable::immutable("a", UnresolvedType::FieldElement.mock())
                                .mock(),
                            untyped::Expression::IntConstant(4usize.into()).mock(),
                        )
                        .mock(),
                    ],
                )
                .mock(),
                Statement::Assignment(
                    untyped::Assignee::Identifier("a").mock(),
                    untyped::Expression::IntConstant(5usize.into()).mock(),
                )
                .mock(),
            ];

            let expected = vec![
                TypedStatement::definition(
                    typed::Variable::new(
                        CoreIdentifier::from(ShadowedIdentifier::shadow("a", 0)),
                        Type::FieldElement,
                        true,
                    )
                    .into(),
                    FieldElementExpression::Number(2.into()).into(),
                ),
                TypedStatement::For(
                    typed::Variable::new(
                        CoreIdentifier::from(ShadowedIdentifier::shadow("i", 1)),
                        Type::Uint(UBitwidth::B32),
                        false,
                    ),
                    0u32.into(),
                    0u32.into(),
                    vec![
                        TypedStatement::definition(
                            typed::Variable::new(
                                CoreIdentifier::from(ShadowedIdentifier::shadow("a", 0)),
                                Type::FieldElement,
                                true,
                            )
                            .into(),
                            FieldElementExpression::Number(3.into()).into(),
                        ),
                        TypedStatement::definition(
                            typed::Variable::new(
                                CoreIdentifier::from(ShadowedIdentifier::shadow("a", 1)),
                                Type::FieldElement,
                                false,
                            )
                            .into(),
                            FieldElementExpression::Number(4.into()).into(),
                        ),
                    ],
                ),
                TypedStatement::definition(
                    typed::Variable::new(
                        CoreIdentifier::from(ShadowedIdentifier::shadow("a", 0)),
                        Type::FieldElement,
                        true,
                    )
                    .into(),
                    FieldElementExpression::Number(5.into()).into(),
                ),
            ];

            checker.enter_scope();
            let checked: Vec<_> = statements
                .into_iter()
                .map(|s| {
                    checker
                        .check_statement(s, &*MODULE_ID, &TypeMap::default())
                        .unwrap()
                })
                .collect();

            assert_eq!(checked, expected);
        }
    }

    mod structs {
        use super::*;
        use zokrates_ast::typed::types::StructMember;

        /// solver function to create a module at location "" with a single symbol `Foo { foo: field }`
        fn create_module_with_foo(
            s: StructDefinition<'static>,
        ) -> (Checker<Bn128Field>, State<Bn128Field>) {
            let module: Module = Module {
                symbols: vec![SymbolDeclaration {
                    id: "Foo",
                    symbol: Symbol::Here(SymbolDefinition::Struct(s.mock())),
                }
                .mock()],
            };

            let mut state = State::<Bn128Field>::new(
                vec![((*MODULE_ID).clone(), module)].into_iter().collect(),
            );

            let mut checker: Checker<Bn128Field> = Checker::default();

            checker.check_module(&*MODULE_ID, &mut state).unwrap();

            (checker, state)
        }

        /// tests about declaring a type
        mod declaration {
            use super::*;

            #[test]
            fn empty_def() {
                // an empty struct should be allowed to be defined
                let modules = Modules::new();
                let state = State::new(modules);

                let declaration: StructDefinitionNode = StructDefinition {
                    generics: vec![],
                    fields: vec![],
                }
                .mock();

                let expected_type =
                    DeclarationStructType::new("".into(), "Foo".into(), vec![], vec![]);

                assert_eq!(
                    Checker::<Bn128Field>::default().check_struct_type_declaration(
                        "Foo".into(),
                        declaration,
                        &*MODULE_ID,
                        &state
                    ),
                    Ok(expected_type)
                );
            }

            #[test]
            fn valid_def() {
                // a valid struct should be allowed to be defined
                let modules = Modules::new();
                let state = State::new(modules);

                let declaration: StructDefinitionNode = StructDefinition {
                    generics: vec![],
                    fields: vec![
                        StructDefinitionField {
                            id: "foo",
                            ty: UnresolvedType::FieldElement.mock(),
                        }
                        .mock(),
                        StructDefinitionField {
                            id: "bar",
                            ty: UnresolvedType::Boolean.mock(),
                        }
                        .mock(),
                    ],
                }
                .mock();

                let expected_type = DeclarationStructType::new(
                    "".into(),
                    "Foo".into(),
                    vec![],
                    vec![
                        DeclarationStructMember::new("foo".into(), DeclarationType::FieldElement),
                        DeclarationStructMember::new("bar".into(), DeclarationType::Boolean),
                    ],
                );

                assert_eq!(
                    Checker::<Bn128Field>::default().check_struct_type_declaration(
                        "Foo".into(),
                        declaration,
                        &*MODULE_ID,
                        &state
                    ),
                    Ok(expected_type)
                );
            }

            #[test]
            fn duplicate_member_def() {
                // definition of a struct with a duplicate member should be rejected
                let modules = Modules::new();
                let state = State::new(modules);

                let declaration: StructDefinitionNode = StructDefinition {
                    generics: vec![],
                    fields: vec![
                        StructDefinitionField {
                            id: "foo",
                            ty: UnresolvedType::FieldElement.mock(),
                        }
                        .mock(),
                        StructDefinitionField {
                            id: "foo",
                            ty: UnresolvedType::Boolean.mock(),
                        }
                        .mock(),
                    ],
                }
                .mock();

                assert_eq!(
                    Checker::<Bn128Field>::default()
                        .check_struct_type_declaration(
                            "Foo".into(),
                            declaration,
                            &*MODULE_ID,
                            &state
                        )
                        .unwrap_err()[0]
                        .message,
                    "Duplicate key foo in struct definition"
                );
            }

            #[test]
            fn recursive() {
                // a struct wrapping another struct should be allowed to be defined

                // struct Foo = { foo: field; }
                // struct Bar = { foo: Foo; }

                let module: Module = Module {
                    symbols: vec![
                        SymbolDeclaration {
                            id: "Foo",
                            symbol: Symbol::Here(SymbolDefinition::Struct(
                                StructDefinition {
                                    generics: vec![],
                                    fields: vec![StructDefinitionField {
                                        id: "foo",
                                        ty: UnresolvedType::FieldElement.mock(),
                                    }
                                    .mock()],
                                }
                                .mock(),
                            )),
                        }
                        .mock(),
                        SymbolDeclaration {
                            id: "Bar",
                            symbol: Symbol::Here(SymbolDefinition::Struct(
                                StructDefinition {
                                    generics: vec![],
                                    fields: vec![StructDefinitionField {
                                        id: "foo",
                                        ty: UnresolvedType::User("Foo".into(), None).mock(),
                                    }
                                    .mock()],
                                }
                                .mock(),
                            )),
                        }
                        .mock(),
                    ],
                };

                let mut state = State::<Bn128Field>::new(
                    vec![((*MODULE_ID).clone(), module)].into_iter().collect(),
                );

                assert!(Checker::default()
                    .check_module(&*MODULE_ID, &mut state)
                    .is_ok());
                assert_eq!(
                    state
                        .types
                        .get(&*MODULE_ID)
                        .unwrap()
                        .get(&"Bar".to_string())
                        .map(|ty| &ty.ty)
                        .unwrap(),
                    &DeclarationType::Struct(DeclarationStructType::new(
                        (*MODULE_ID).clone(),
                        "Bar".into(),
                        vec![],
                        vec![DeclarationStructMember::new(
                            "foo".into(),
                            DeclarationType::Struct(DeclarationStructType::new(
                                (*MODULE_ID).clone(),
                                "Foo".into(),
                                vec![],
                                vec![DeclarationStructMember::new(
                                    "foo".into(),
                                    DeclarationType::FieldElement
                                )]
                            ))
                        )]
                    ))
                );
            }

            #[test]
            fn recursive_undefined() {
                // a struct wrapping an undefined struct should be rejected

                // struct Bar = { foo: Foo; }

                let module: Module = Module {
                    symbols: vec![SymbolDeclaration {
                        id: "Bar",
                        symbol: Symbol::Here(SymbolDefinition::Struct(
                            StructDefinition {
                                generics: vec![],
                                fields: vec![StructDefinitionField {
                                    id: "foo",
                                    ty: UnresolvedType::User("Foo".into(), None).mock(),
                                }
                                .mock()],
                            }
                            .mock(),
                        )),
                    }
                    .mock()],
                };

                let mut state = State::<Bn128Field>::new(
                    vec![((*MODULE_ID).clone(), module)].into_iter().collect(),
                );

                assert!(Checker::default()
                    .check_module(&*MODULE_ID, &mut state)
                    .is_err());
            }

            #[test]
            fn self_referential() {
                // a struct wrapping itself should be rejected

                // struct Foo = { foo: Foo; }

                let module: Module = Module {
                    symbols: vec![SymbolDeclaration {
                        id: "Foo",
                        symbol: Symbol::Here(SymbolDefinition::Struct(
                            StructDefinition {
                                generics: vec![],
                                fields: vec![StructDefinitionField {
                                    id: "foo",
                                    ty: UnresolvedType::User("Foo".into(), None).mock(),
                                }
                                .mock()],
                            }
                            .mock(),
                        )),
                    }
                    .mock()],
                };

                let mut state = State::<Bn128Field>::new(
                    vec![((*MODULE_ID).clone(), module)].into_iter().collect(),
                );

                assert!(Checker::default()
                    .check_module(&*MODULE_ID, &mut state)
                    .is_err());
            }

            #[test]
            fn cyclic() {
                // A wrapping B wrapping A should be rejected

                // struct Foo = { bar: Bar; }
                // struct Bar = { foo: Foo; }

                let module: Module = Module {
                    symbols: vec![
                        SymbolDeclaration {
                            id: "Foo",
                            symbol: Symbol::Here(SymbolDefinition::Struct(
                                StructDefinition {
                                    generics: vec![],
                                    fields: vec![StructDefinitionField {
                                        id: "bar",
                                        ty: UnresolvedType::User("Bar".into(), None).mock(),
                                    }
                                    .mock()],
                                }
                                .mock(),
                            )),
                        }
                        .mock(),
                        SymbolDeclaration {
                            id: "Bar",
                            symbol: Symbol::Here(SymbolDefinition::Struct(
                                StructDefinition {
                                    generics: vec![],
                                    fields: vec![StructDefinitionField {
                                        id: "foo",
                                        ty: UnresolvedType::User("Foo".into(), None).mock(),
                                    }
                                    .mock()],
                                }
                                .mock(),
                            )),
                        }
                        .mock(),
                    ],
                };

                let mut state = State::<Bn128Field>::new(
                    vec![((*MODULE_ID).clone(), module)].into_iter().collect(),
                );

                assert!(Checker::default()
                    .check_module(&*MODULE_ID, &mut state)
                    .is_err());
            }
        }

        /// tests about using the defined type identifier
        mod usage {
            use super::*;

            #[test]
            fn ty() {
                // a defined type can be checked
                // Foo { foo: field; }
                // Foo

                // an undefined type cannot be checked
                // Bar

                let (mut checker, state) = create_module_with_foo(StructDefinition {
                    generics: vec![],
                    fields: vec![StructDefinitionField {
                        id: "foo",
                        ty: UnresolvedType::FieldElement.mock(),
                    }
                    .mock()],
                });

                assert_eq!(
                    checker.check_type(
                        UnresolvedType::User("Foo".into(), None).mock(),
                        &*MODULE_ID,
                        &state.types
                    ),
                    Ok(Type::Struct(StructType::new(
                        "".into(),
                        "Foo".into(),
                        vec![],
                        vec![StructMember::new("foo".into(), Type::FieldElement)]
                    )))
                );

                assert_eq!(
                    checker
                        .check_type(
                            UnresolvedType::User("Bar".into(), None).mock(),
                            &*MODULE_ID,
                            &state.types
                        )
                        .unwrap_err()
                        .message,
                    "Undefined type Bar"
                );
            }
        }

        /// tests about accessing members
        mod member {
            use super::*;

            #[test]
            fn valid() {
                // accessing a member on a struct should succeed and return the right type

                // struct Foo = { foo: field; }
                // Foo { foo: 42 }.foo

                let (mut checker, state) = create_module_with_foo(StructDefinition {
                    generics: vec![],
                    fields: vec![StructDefinitionField {
                        id: "foo",
                        ty: UnresolvedType::FieldElement.mock(),
                    }
                    .mock()],
                });

                assert_eq!(
                    checker.check_expression(
                        Expression::Member(
                            box Expression::InlineStruct(
                                "Foo".into(),
                                vec![("foo", Expression::IntConstant(42usize.into()).mock())]
                            )
                            .mock(),
                            "foo".into()
                        )
                        .mock(),
                        &*MODULE_ID,
                        &state.types
                    ),
                    Ok(FieldElementExpression::member(
                        StructExpressionInner::Value(vec![FieldElementExpression::Number(
                            Bn128Field::from(42u32)
                        )
                        .into()])
                        .annotate(StructType::new(
                            "".into(),
                            "Foo".into(),
                            vec![],
                            vec![StructMember::new("foo".into(), Type::FieldElement)]
                        )),
                        "foo".into()
                    )
                    .into())
                );
            }

            #[test]
            fn invalid() {
                // accessing an undefined member on a struct should fail

                // struct Foo = { foo: field; }
                // Foo { foo: 42 }.bar

                let (mut checker, state) = create_module_with_foo(StructDefinition {
                    generics: vec![],
                    fields: vec![StructDefinitionField {
                        id: "foo",
                        ty: UnresolvedType::FieldElement.mock(),
                    }
                    .mock()],
                });

                assert_eq!(
                    checker
                        .check_expression(
                            Expression::Member(
                                box Expression::InlineStruct(
                                    "Foo".into(),
                                    vec![("foo", Expression::IntConstant(42usize.into()).mock())]
                                )
                                .mock(),
                                "bar".into()
                            )
                            .mock(),
                            &*MODULE_ID,
                            &state.types
                        )
                        .unwrap_err()
                        .message,
                    "Foo {foo: field} doesn\'t have member bar"
                );
            }
        }

        /// tests about defining struct instance inline
        mod value {
            use super::*;

            #[test]
            fn wrong_name() {
                // a A value cannot be defined with B as id, even if A and B have the same members

                let (mut checker, state) = create_module_with_foo(StructDefinition {
                    generics: vec![],
                    fields: vec![StructDefinitionField {
                        id: "foo",
                        ty: UnresolvedType::FieldElement.mock(),
                    }
                    .mock()],
                });

                assert_eq!(
                    checker
                        .check_expression(
                            Expression::InlineStruct(
                                "Bar".into(),
                                vec![("foo", Expression::IntConstant(42usize.into()).mock())]
                            )
                            .mock(),
                            &*MODULE_ID,
                            &state.types
                        )
                        .unwrap_err()
                        .message,
                    "Undefined type `Bar`"
                );
            }

            #[test]
            fn valid() {
                // a A value can be defined with members ordered as in the declaration of A

                // struct Foo { foo: field; bar: bool; }
                // Foo foo = Foo { foo: 42, bar: true };

                let (mut checker, state) = create_module_with_foo(StructDefinition {
                    generics: vec![],
                    fields: vec![
                        StructDefinitionField {
                            id: "foo",
                            ty: UnresolvedType::FieldElement.mock(),
                        }
                        .mock(),
                        StructDefinitionField {
                            id: "bar",
                            ty: UnresolvedType::Boolean.mock(),
                        }
                        .mock(),
                    ],
                });

                assert_eq!(
                    checker.check_expression(
                        Expression::InlineStruct(
                            "Foo".into(),
                            vec![
                                ("foo", Expression::IntConstant(42usize.into()).mock()),
                                ("bar", Expression::BooleanConstant(true).mock())
                            ]
                        )
                        .mock(),
                        &*MODULE_ID,
                        &state.types
                    ),
                    Ok(StructExpressionInner::Value(vec![
                        FieldElementExpression::Number(Bn128Field::from(42u32)).into(),
                        BooleanExpression::Value(true).into()
                    ])
                    .annotate(StructType::new(
                        "".into(),
                        "Foo".into(),
                        vec![],
                        vec![
                            StructMember::new("foo".into(), Type::FieldElement),
                            StructMember::new("bar".into(), Type::Boolean)
                        ]
                    ))
                    .into())
                );
            }

            #[test]
            fn shuffled() {
                // a A value can be defined with shuffled members compared to the declaration of A

                // struct Foo { foo: field; bar: bool; }
                // Foo foo = Foo { bar: true, foo: 42 };

                let (mut checker, state) = create_module_with_foo(StructDefinition {
                    generics: vec![],
                    fields: vec![
                        StructDefinitionField {
                            id: "foo",
                            ty: UnresolvedType::FieldElement.mock(),
                        }
                        .mock(),
                        StructDefinitionField {
                            id: "bar",
                            ty: UnresolvedType::Boolean.mock(),
                        }
                        .mock(),
                    ],
                });

                assert_eq!(
                    checker.check_expression(
                        Expression::InlineStruct(
                            "Foo".into(),
                            vec![
                                ("bar", Expression::BooleanConstant(true).mock()),
                                ("foo", Expression::IntConstant(42usize.into()).mock())
                            ]
                        )
                        .mock(),
                        &*MODULE_ID,
                        &state.types
                    ),
                    Ok(StructExpressionInner::Value(vec![
                        FieldElementExpression::Number(Bn128Field::from(42u32)).into(),
                        BooleanExpression::Value(true).into()
                    ])
                    .annotate(StructType::new(
                        "".into(),
                        "Foo".into(),
                        vec![],
                        vec![
                            StructMember::new("foo".into(), Type::FieldElement),
                            StructMember::new("bar".into(), Type::Boolean)
                        ]
                    ))
                    .into())
                );
            }

            #[test]
            fn subset() {
                // a A value cannot be defined with A as id if members are a subset of the declaration

                // struct Foo { foo: field; bar: bool; }
                // Foo foo = Foo { foo: 42 };

                let (mut checker, state) = create_module_with_foo(StructDefinition {
                    generics: vec![],
                    fields: vec![
                        StructDefinitionField {
                            id: "foo",
                            ty: UnresolvedType::FieldElement.mock(),
                        }
                        .mock(),
                        StructDefinitionField {
                            id: "bar",
                            ty: UnresolvedType::Boolean.mock(),
                        }
                        .mock(),
                    ],
                });

                assert_eq!(
                    checker
                        .check_expression(
                            Expression::InlineStruct(
                                "Foo".into(),
                                vec![("foo", Expression::IntConstant(42usize.into()).mock())]
                            )
                            .mock(),
                            &*MODULE_ID,
                            &state.types
                        )
                        .unwrap_err()
                        .message,
                    "Inline struct Foo {foo: 42} does not match Foo {foo: field, bar: bool}"
                );
            }

            #[test]
            fn invalid() {
                // a A value cannot be defined with A as id if members are different ids than the declaration
                // a A value cannot be defined with A as id if members are different types than the declaration

                // struct Foo { foo: field; bar: bool; }
                // Foo { foo: 42, baz: bool } // error
                // Foo { foo: 42, baz: 42 } // error

                let (mut checker, state) = create_module_with_foo(StructDefinition {
                    generics: vec![],
                    fields: vec![
                        StructDefinitionField {
                            id: "foo",
                            ty: UnresolvedType::FieldElement.mock(),
                        }
                        .mock(),
                        StructDefinitionField {
                            id: "bar",
                            ty: UnresolvedType::Boolean.mock(),
                        }
                        .mock(),
                    ],
                });

                assert_eq!(
                    checker
                        .check_expression(
                            Expression::InlineStruct(
                                "Foo".into(),
                                vec![(
                                    "baz",
                                    Expression::BooleanConstant(true).mock()
                                ),(
                                    "foo",
                                    Expression::IntConstant(42usize.into()).mock()
                                )]
                            )
                            .mock(),
                            &*MODULE_ID,
                            &state.types
                        ).unwrap_err()
                        .message,
                    "Member bar of struct Foo {foo: field, bar: bool} not found in value Foo {baz: true, foo: 42}"
                );

                assert_eq!(
                    checker
                        .check_expression(
                            Expression::InlineStruct(
                                "Foo".into(),
                                vec![
                                    ("bar", Expression::IntConstant(42usize.into()).mock()),
                                    ("foo", Expression::IntConstant(42usize.into()).mock())
                                ]
                            )
                            .mock(),
                            &*MODULE_ID,
                            &state.types
                        )
                        .unwrap_err()
                        .message,
                    "Member bar of struct Foo has type bool, found 42 of type {integer}"
                );
            }
        }
    }

    mod int_inference {
        use super::*;

        #[test]
        fn two_candidates() {
            // def foo(field a) -> field {
            //   return 0;
            // }

            // def foo(u32 a) -> field {
            //   return 0;
            // }

            // def main() -> field {
            //   return foo(0);
            // }

            // should fail

            let mut foo_field = function0();

            foo_field.value.arguments = vec![untyped::Parameter::private(
                untyped::Variable::immutable("a", UnresolvedType::FieldElement.mock()).mock(),
            )
            .mock()];
            foo_field.value.statements =
                vec![Statement::Return(Some(Expression::IntConstant(0usize.into()).mock())).mock()];
            foo_field.value.signature = UnresolvedSignature::new()
                .inputs(vec![UnresolvedType::FieldElement.mock()])
                .output(UnresolvedType::FieldElement.mock());

            let mut foo_u32 = function0();

            foo_u32.value.arguments = vec![untyped::Parameter::private(
                untyped::Variable::immutable("a", UnresolvedType::Uint(32).mock()).mock(),
            )
            .mock()];
            foo_u32.value.statements =
                vec![Statement::Return(Some(Expression::IntConstant(0usize.into()).mock())).mock()];
            foo_u32.value.signature = UnresolvedSignature::new()
                .inputs(vec![UnresolvedType::Uint(32).mock()])
                .output(UnresolvedType::FieldElement.mock());

            let mut main = function0();

            main.value.statements = vec![Statement::Return(Some(
                Expression::FunctionCall(
                    box Expression::Identifier("foo").mock(),
                    None,
                    vec![Expression::IntConstant(0usize.into()).mock()],
                )
                .mock(),
            ))
            .mock()];
            main.value.signature =
                UnresolvedSignature::new().output(UnresolvedType::FieldElement.mock());

            let m = Module::with_symbols(vec![
                untyped::SymbolDeclaration {
                    id: "foo",
                    symbol: Symbol::Here(SymbolDefinition::Function(foo_field)),
                }
                .mock(),
                untyped::SymbolDeclaration {
                    id: "foo",
                    symbol: Symbol::Here(SymbolDefinition::Function(foo_u32)),
                }
                .mock(),
                untyped::SymbolDeclaration {
                    id: "main",
                    symbol: Symbol::Here(SymbolDefinition::Function(main)),
                }
                .mock(),
            ]);

            let p = Program {
                main: "".into(),
                modules: vec![("".into(), m)].into_iter().collect(),
            };

            let errors = Checker::<Bn128Field>::default()
                .check_program(p)
                .unwrap_err();

            assert_eq!(errors.len(), 1);

            assert_eq!(
                errors[0].inner.message,
                "Ambiguous call to function foo, 2 candidates were found. Please be more explicit."
            );
        }
    }

    mod assignee {
        use super::*;

        #[test]
        fn identifier() {
            // a = 42;
            let a = Assignee::Identifier("a").mock();

            let mut checker: Checker<Bn128Field> = Checker::default();
            checker.enter_scope();

            checker
                .check_statement(
                    Statement::Definition(
                        untyped::Variable::mutable("a", UnresolvedType::FieldElement.mock()).mock(),
                        Expression::FieldConstant(42u32.into()).mock(),
                    )
                    .mock(),
                    &*MODULE_ID,
                    &TypeMap::new(),
                )
                .unwrap();

            assert_eq!(
                checker.check_assignee(a, &*MODULE_ID, &TypeMap::new()),
                Ok(TypedAssignee::Identifier(typed::Variable::new(
                    "a",
                    Type::FieldElement,
                    true
                )))
            );
        }

        #[test]
        fn array_element() {
            // field[3] a = [1, 2, 3]
            // a[2] = 42
            let a = Assignee::Select(
                box Assignee::Identifier("a").mock(),
                box RangeOrExpression::Expression(Expression::IntConstant(2usize.into()).mock()),
            )
            .mock();

            let mut checker: Checker<Bn128Field> = Checker::default();
            checker.enter_scope();

            checker
                .check_statement(
                    Statement::Definition(
                        untyped::Variable::mutable(
                            "a",
                            UnresolvedType::array(
                                UnresolvedType::FieldElement.mock(),
                                Expression::IntConstant(3usize.into()).mock(),
                            )
                            .mock(),
                        )
                        .mock(),
                        Expression::InlineArray(
                            (1..4)
                                .map(|i| {
                                    Expression::FieldConstant(BigUint::from(i as u32))
                                        .mock()
                                        .into()
                                })
                                .collect(),
                        )
                        .mock(),
                    )
                    .mock(),
                    &*MODULE_ID,
                    &TypeMap::new(),
                )
                .unwrap();

            assert_eq!(
                checker.check_assignee(a, &*MODULE_ID, &TypeMap::new()),
                Ok(TypedAssignee::Select(
                    box TypedAssignee::Identifier(typed::Variable::new(
                        "a",
                        Type::array((Type::FieldElement, 3u32)),
                        true,
                    )),
                    box 2u32.into()
                ))
            );
        }

        #[test]
        fn array_of_array_element() {
            // field[1][1] a = [[1]]
            // a[0][0]
            let a: AssigneeNode = Assignee::Select(
                box Assignee::Select(
                    box Assignee::Identifier("a").mock(),
                    box RangeOrExpression::Expression(
                        Expression::IntConstant(0usize.into()).mock(),
                    ),
                )
                .mock(),
                box RangeOrExpression::Expression(Expression::IntConstant(0usize.into()).mock()),
            )
            .mock();

            let mut checker: Checker<Bn128Field> = Checker::default();
            checker.enter_scope();

            checker
                .check_statement(
                    Statement::Definition(
                        untyped::Variable::mutable(
                            "a",
                            UnresolvedType::array(
                                UnresolvedType::array(
                                    UnresolvedType::FieldElement.mock(),
                                    Expression::IntConstant(1usize.into()).mock(),
                                )
                                .mock(),
                                Expression::IntConstant(1usize.into()).mock(),
                            )
                            .mock(),
                        )
                        .mock(),
                        Expression::InlineArray(vec![Expression::InlineArray(vec![
                            Expression::IntConstant(1usize.into()).mock().into(),
                        ])
                        .mock()
                        .into()])
                        .mock(),
                    )
                    .mock(),
                    &*MODULE_ID,
                    &TypeMap::new(),
                )
                .unwrap();

            assert_eq!(
                checker.check_assignee(a, &*MODULE_ID, &TypeMap::new()),
                Ok(TypedAssignee::Select(
                    box TypedAssignee::Select(
                        box TypedAssignee::Identifier(typed::Variable::new(
                            "a",
                            Type::array((Type::array((Type::FieldElement, 1u32)), 1u32)),
                            true,
                        )),
                        box 0u32.into()
                    ),
                    box 0u32.into()
                ))
            );
        }
    }
}
