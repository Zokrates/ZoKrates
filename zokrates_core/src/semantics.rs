//! Module containing semantic analysis tools to run at compile time
//!
//! @file semantics.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2017

use crate::absy::Identifier;
use crate::absy::*;
use crate::typed_absy::*;
use crate::typed_absy::{DeclarationParameter, DeclarationVariable, Variable};
use num_bigint::BigUint;
use std::collections::{hash_map::Entry, BTreeSet, HashMap, HashSet};
use std::fmt;
use std::path::PathBuf;
use zokrates_field::Field;

use crate::parser::Position;

use crate::absy::types::{UnresolvedSignature, UnresolvedType, UserTypeId};

use crate::typed_absy::types::{
    ArrayType, Constant, DeclarationArrayType, DeclarationFunctionKey, DeclarationSignature,
    DeclarationStructMember, DeclarationStructType, DeclarationType, StructLocation,
};
use std::hash::{Hash, Hasher};

#[derive(PartialEq, Debug)]
pub struct ErrorInner {
    pos: Option<(Position, Position)>,
    message: String,
}

#[derive(PartialEq, Debug)]
pub struct Error {
    pub inner: ErrorInner,
    pub module_id: PathBuf,
}

impl ErrorInner {
    fn in_file(self, id: &ModuleId) -> Error {
        Error {
            inner: self,
            module_id: id.to_path_buf(),
        }
    }
}

type TypeMap<'ast> = HashMap<OwnedModuleId, HashMap<UserTypeId, DeclarationType<'ast>>>;

/// The global state of the program during semantic checks
#[derive(Debug)]
struct State<'ast, T> {
    /// The modules yet to be checked, which we consume as we explore the dependency tree
    modules: Modules<'ast>,
    /// The already checked modules, which we're returning at the end
    typed_modules: TypedModules<'ast, T>,
    /// The user-defined types, which we keep track at this phase only. In later phases, we rely only on basic types and combinations thereof
    types: TypeMap<'ast>,
}

/// A symbol for a given name: either a type or a group of functions. Not both!
#[derive(PartialEq, Hash, Eq, Debug)]
enum SymbolType<'ast> {
    Type,
    Functions(BTreeSet<DeclarationSignature<'ast>>),
}

/// A data structure to keep track of all symbols in a module
#[derive(Default)]
struct SymbolUnifier<'ast> {
    symbols: HashMap<String, SymbolType<'ast>>,
}

impl<'ast> SymbolUnifier<'ast> {
    fn insert_type<S: Into<String>>(&mut self, id: S) -> bool {
        let s_type = self.symbols.entry(id.into());
        match s_type {
            // if anything is already called `id`, we cannot introduce this type
            Entry::Occupied(..) => false,
            // otherwise, we can!
            Entry::Vacant(v) => {
                v.insert(SymbolType::Type);
                true
            }
        }
    }

    fn insert_function<S: Into<String>>(
        &mut self,
        id: S,
        signature: DeclarationSignature<'ast>,
    ) -> bool {
        let s_type = self.symbols.entry(id.into());
        match s_type {
            // if anything is already called `id`, it depends what it is
            Entry::Occupied(mut o) => {
                match o.get_mut() {
                    // if it's a Type, then we can't introduce a function
                    SymbolType::Type => false,
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
            typed_modules: HashMap::new(),
            types: HashMap::new(),
        }
    }
}

impl fmt::Display for ErrorInner {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let location = self
            .pos
            .map(|p| format!("{}", p.0))
            .unwrap_or_else(|| "?".to_string());
        write!(f, "{}\n\t{}", location, self.message)
    }
}

/// A function query in the current module.
#[derive(Debug)]
struct FunctionQuery<'ast, T> {
    id: Identifier<'ast>,
    inputs: Vec<Type<'ast, T>>,
    /// Output types are optional as we try to infer them
    outputs: Vec<Option<Type<'ast, T>>>,
}

impl<'ast, T: fmt::Display> fmt::Display for FunctionQuery<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "(")?;
        for (i, t) in self.inputs.iter().enumerate() {
            write!(f, "{}", t)?;
            if i < self.inputs.len() - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, ")")?;

        match self.outputs.len() {
            0 => write!(f, ""),
            1 => write!(
                f,
                " -> {}",
                match &self.outputs[0] {
                    Some(t) => format!("{}", t),
                    None => "_".into(),
                }
            ),
            _ => {
                write!(f, " -> (")?;
                for (i, t) in self.outputs.iter().enumerate() {
                    match t {
                        Some(t) => write!(f, "{}", t)?,
                        None => write!(f, "_")?,
                    }
                    if i < self.outputs.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
        }
    }
}

impl<'ast, T: Field> FunctionQuery<'ast, T> {
    /// Create a new query.
    fn new(
        id: Identifier<'ast>,
        inputs: &[Type<'ast, T>],
        outputs: &[Option<Type<'ast, T>>],
    ) -> Self {
        FunctionQuery {
            id,
            inputs: inputs.to_owned(),
            outputs: outputs.to_owned(),
        }
    }

    /// match a `FunctionKey` against this `FunctionQuery`
    fn match_func(&self, func: &DeclarationFunctionKey<'ast>) -> bool {
        self.id == func.id
            && self
                .inputs
                .iter()
                .zip(func.signature.inputs.iter())
                .all(|(input_ty, sig_ty)| input_ty.can_be_specialized_to(&sig_ty))
            && self.outputs.len() == func.signature.outputs.len()
            && self
                .outputs
                .iter()
                .zip(func.signature.outputs.iter())
                .all(|(output_ty, sig_ty)| {
                    output_ty
                        .as_ref()
                        .map(|output_ty| output_ty.can_be_specialized_to(&sig_ty))
                        .unwrap_or(true)
                })
    }

    fn match_funcs(
        &self,
        funcs: &HashSet<DeclarationFunctionKey<'ast>>,
    ) -> Vec<DeclarationFunctionKey<'ast>> {
        funcs
            .iter()
            .filter(|func| self.match_func(func))
            .cloned()
            .collect()
    }
}

/// A scoped variable, so that we can delete all variables of a given scope when exiting it
#[derive(Clone, Debug)]
pub struct ScopedVariable<'ast, T> {
    id: Variable<'ast, T>,
    level: usize,
}

/// Identifiers of different `ScopedVariable`s should not conflict, so we define them as equivalent
impl<'ast, T> PartialEq for ScopedVariable<'ast, T> {
    fn eq(&self, other: &Self) -> bool {
        self.id.id == other.id.id
    }
}

impl<'ast, T> Hash for ScopedVariable<'ast, T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.id.hash(state);
    }
}

impl<'ast, T> Eq for ScopedVariable<'ast, T> {}

/// Checker checks the semantics of a program, keeping track of functions and variables in scope
pub struct Checker<'ast, T> {
    return_types: Option<Vec<DeclarationType<'ast>>>,
    scope: HashSet<ScopedVariable<'ast, T>>,
    functions: HashSet<DeclarationFunctionKey<'ast>>,
    level: usize,
}

impl<'ast, T: Field> Checker<'ast, T> {
    fn new() -> Self {
        Checker {
            return_types: None,
            scope: HashSet::new(),
            functions: HashSet::new(),
            level: 0,
        }
    }

    /// Check a `Program`
    ///
    /// # Arguments
    ///
    /// * `prog` - The `Program` to be checked
    pub fn check(prog: Program<'ast>) -> Result<TypedProgram<'ast, T>, Vec<Error>> {
        Checker::new().check_program(prog)
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

    fn check_struct_type_declaration(
        &mut self,
        id: String,
        s: StructDefinitionNode<'ast>,
        module_id: &ModuleId,
        types: &TypeMap<'ast>,
    ) -> Result<DeclarationType<'ast>, Vec<ErrorInner>> {
        let pos = s.pos();
        let s = s.value;

        let mut errors = vec![];
        let mut fields: Vec<(_, _)> = vec![];
        let mut fields_set = HashSet::new();

        for field in s.fields {
            let member_id = field.value.id.to_string();
            match self
                .check_declaration_type(field.value.ty, module_id, &types, &HashSet::new())
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

        if !errors.is_empty() {
            return Err(errors);
        }

        Ok(DeclarationType::Struct(DeclarationStructType::new(
            module_id.to_path_buf(),
            id,
            fields
                .iter()
                .map(|f| DeclarationStructMember::new(f.0.clone(), f.1.clone()))
                .collect(),
        )))
    }

    fn check_symbol_declaration(
        &mut self,
        declaration: SymbolDeclarationNode<'ast>,
        module_id: &ModuleId,
        state: &mut State<'ast, T>,
        functions: &mut HashMap<DeclarationFunctionKey<'ast>, TypedFunctionSymbol<'ast, T>>,
        symbol_unifier: &mut SymbolUnifier<'ast>,
    ) -> Result<(), Vec<Error>> {
        let mut errors: Vec<Error> = vec![];

        let pos = declaration.pos();
        let declaration = declaration.value;

        match declaration.symbol.clone() {
            Symbol::HereType(t) => {
                match self.check_struct_type_declaration(
                    declaration.id.to_string(),
                    t.clone(),
                    module_id,
                    &state.types,
                ) {
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
                                // there should be no entry in the map for this type yet
                                assert!(state
                                    .types
                                    .entry(module_id.to_path_buf())
                                    .or_default()
                                    .insert(declaration.id.to_string(), ty)
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
            Symbol::HereFunction(f) => match self.check_function(f, module_id, &state.types) {
                Ok(funct) => {
                    match symbol_unifier.insert_function(declaration.id, funct.signature.clone()) {
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
                        true => {}
                    };

                    self.functions.insert(
                        DeclarationFunctionKey::with_location(
                            module_id.to_path_buf(),
                            declaration.id,
                        )
                        .signature(funct.signature.clone()),
                    );
                    functions.insert(
                        DeclarationFunctionKey::with_location(
                            module_id.to_path_buf(),
                            declaration.id,
                        )
                        .signature(funct.signature.clone()),
                        TypedFunctionSymbol::Here(funct),
                    );
                }
                Err(e) => {
                    errors.extend(e.into_iter().map(|inner| inner.in_file(module_id)));
                }
            },
            Symbol::There(import) => {
                let pos = import.pos();
                let import = import.value;

                match Checker::new().check_module(&import.module_id, state) {
                    Ok(()) => {
                        // find candidates in the checked module
                        let function_candidates: Vec<_> = state
                            .typed_modules
                            .get(&import.module_id)
                            .unwrap()
                            .functions
                            .iter()
                            .filter(|(k, _)| k.id == import.symbol_id)
                            .map(|(_, v)| DeclarationFunctionKey {
                                module: import.module_id.to_path_buf(),
                                id: import.symbol_id,
                                signature: v.signature(&state.typed_modules).clone(),
                            })
                            .collect();

                        // find candidates in the types
                        let type_candidate = state
                            .types
                            .entry(import.module_id.to_path_buf())
                            .or_default()
                            .get(import.symbol_id)
                            .cloned();

                        match (function_candidates.len(), type_candidate) {
                            (0, Some(t)) => {

                                // rename the type to the declared symbol
                                let t = match t {
                                    DeclarationType::Struct(t) => DeclarationType::Struct(DeclarationStructType {
                                        location: Some(StructLocation {
                                            name: declaration.id.into(),
                                            module: module_id.to_path_buf()
                                        }),
                                        ..t
                                    }),
                                    _ => unreachable!()
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
                            (0, None) => {
                                errors.push(ErrorInner {
                                    pos: Some(pos),
                                    message: format!(
                                        "Could not find symbol {} in module {}",
                                        import.symbol_id, import.module_id.display(),
                                    ),
                                }.in_file(module_id));
                            }
                            (_, Some(_)) => unreachable!("collision in module we're importing from should have been caught when checking it"),
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
                                    functions.insert(
                                        local_key,
                                        TypedFunctionSymbol::There(candidate,
                                        ),
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
                match symbol_unifier.insert_function(declaration.id, funct.signature()) {
                    false => {
                        errors.push(
                            ErrorInner {
                                pos: Some(pos),
                                message: format!(
                                    "{} conflicts with another symbol",
                                    declaration.id,
                                ),
                            }
                            .in_file(module_id),
                        );
                    }
                    true => {}
                };

                self.functions.insert(
                    DeclarationFunctionKey::with_location(module_id.to_path_buf(), declaration.id)
                        .signature(funct.signature()),
                );
                functions.insert(
                    DeclarationFunctionKey::with_location(module_id.to_path_buf(), declaration.id)
                        .signature(funct.signature()),
                    TypedFunctionSymbol::Flat(funct),
                );
            }
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
        let mut checked_functions = HashMap::new();

        // check if the module was already removed from the untyped ones
        let to_insert = match state.modules.remove(module_id) {
            // if it was, do nothing
            None => None,
            // if it was not, check it
            Some(module) => {
                assert_eq!(module.imports.len(), 0);

                // we need to create an entry in the types map to store types for this module
                state.types.entry(module_id.to_path_buf()).or_default();

                // we keep track of the introduced symbols to avoid colisions between types and functions
                let mut symbol_unifier = SymbolUnifier::default();

                // we go through symbol declarations and check them
                for declaration in module.symbols {
                    self.check_symbol_declaration(
                        declaration,
                        module_id,
                        state,
                        &mut checked_functions,
                        &mut symbol_unifier,
                    )?
                }

                Some(TypedModule {
                    functions: checked_functions,
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
            .functions
            .iter()
            .filter(|(key, _)| key.id == "main")
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

    fn check_for_var(&self, var: &VariableNode<'ast>) -> Result<(), ErrorInner> {
        match var.value.get_type() {
            UnresolvedType::Uint(32) => Ok(()),
            t => Err(ErrorInner {
                pos: Some(var.pos()),
                message: format!("Variable in for loop cannot have type {}", t),
            }),
        }
    }

    fn check_function(
        &mut self,
        funct_node: FunctionNode<'ast>,
        module_id: &ModuleId,
        types: &TypeMap<'ast>,
    ) -> Result<TypedFunction<'ast, T>, Vec<ErrorInner>> {
        assert!(self.scope.is_empty());
        assert!(self.return_types.is_none());

        self.enter_scope();

        let pos = funct_node.pos();

        let mut errors = vec![];
        let funct = funct_node.value;
        let mut signature = None;

        assert_eq!(funct.arguments.len(), funct.signature.inputs.len());

        let mut arguments_checked = vec![];

        let mut statements_checked = vec![];

        match self.check_signature(funct.signature, module_id, types) {
            Ok(s) => {
                // define variables for the constants
                for generic in &s.generics {
                    let generic = generic.clone().unwrap(); // for declaration signatures, generics cannot be ignored

                    let v = Variable::with_id_and_type(
                        match generic {
                            Constant::Generic(g) => g,
                            _ => unreachable!(),
                        },
                        Type::Uint(UBitwidth::B32),
                    );
                    // we don't have to check for conflicts here, because this was done when checking the signature
                    self.insert_into_scope(v.clone());
                }

                for (arg, decl_ty) in funct.arguments.into_iter().zip(s.inputs.iter()) {
                    let pos = arg.pos();

                    let arg = arg.value;

                    let decl_v =
                        DeclarationVariable::with_id_and_type(arg.id.value.id, decl_ty.clone());

                    match self.insert_into_scope(decl_v.clone()) {
                        true => {}
                        false => {
                            errors.push(ErrorInner {
                                pos: Some(pos),
                                message: format!("Duplicate name in function definition: `{}` was previously declared as an argument or a generic constant", arg.id.value.id)
                            });
                        }
                    };
                    arguments_checked.push(DeclarationParameter {
                        id: decl_v,
                        private: arg.private,
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

                    match self.check_statement(stat, module_id, types) {
                        Ok(statement) => {
                            if let TypedStatement::Return(e) = &statement {
                                match e.iter().map(|e| e.get_type()).collect::<Vec<_>>()
                                    == s.outputs
                                {
                                    true => {}
                                    false => errors.push(ErrorInner {
                                        pos,
                                        message: format!(
                                            "Expected ({}) in return statement, found ({})",
                                            s.outputs
                                                .iter()
                                                .map(|t| t.to_string())
                                                .collect::<Vec<_>>()
                                                .join(", "),
                                            e.iter()
                                                .map(|e| e.get_type())
                                                .map(|t| t.to_string())
                                                .collect::<Vec<_>>()
                                                .join(", ")
                                        ),
                                    }),
                                }
                            };
                            statements_checked.push(statement);
                        }
                        Err(e) => {
                            errors.extend(e);
                        }
                    }
                }

                if !found_return {
                    errors.push(ErrorInner {
                        pos: Some(pos),
                        message: "Expected a return statement".to_string(),
                    });
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

        self.return_types = None;
        assert!(self.scope.is_empty());

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
        types: &TypeMap<'ast>,
    ) -> Result<DeclarationSignature<'ast>, Vec<ErrorInner>> {
        let mut errors = vec![];
        let mut inputs = vec![];
        let mut outputs = vec![];
        let mut generics = vec![];

        let mut constants = HashSet::new();

        for g in signature.generics {
            match constants.insert(g.value) {
                true => {
                    generics.push(Some(Constant::Generic(g.value)));
                }
                false => {
                    errors.push(ErrorInner {
                        pos: Some(g.pos()),
                        message: format!("Generic parameter {} is already declared", g.value),
                    });
                }
            }
        }

        for t in signature.inputs {
            match self.check_declaration_type(t, module_id, types, &constants) {
                Ok(t) => {
                    inputs.push(t);
                }
                Err(e) => {
                    errors.push(e);
                }
            }
        }

        for t in signature.outputs {
            match self.check_declaration_type(t, module_id, types, &constants) {
                Ok(t) => {
                    outputs.push(t);
                }
                Err(e) => {
                    errors.push(e);
                }
            }
        }

        if !errors.is_empty() {
            return Err(errors);
        }

        self.return_types = Some(outputs.clone());

        Ok(DeclarationSignature {
            generics,
            inputs,
            outputs,
        })
    }

    fn check_type(
        &mut self,
        ty: UnresolvedTypeNode<'ast>,
        module_id: &ModuleId,
        types: &TypeMap<'ast>,
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
                    TypedExpression::Int(v) => UExpression::try_from_int(v.clone(), UBitwidth::B32)
                        .map_err(|_| ErrorInner {
                            pos: Some(pos),
                            message: format!(
                            "Expected array dimension to be a u32 constant, found {} of type {}",
                            v, ty
                        ),
                        }),
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
            UnresolvedType::User(id) => types
                .get(module_id)
                .unwrap()
                .get(&id)
                .cloned()
                .ok_or_else(|| ErrorInner {
                    pos: Some(pos),
                    message: format!("Undefined type {}", id),
                })
                .map(|t| t.into()),
        }
    }

    fn check_generic_expression(
        &mut self,
        expr: ExpressionNode<'ast>,
    ) -> Result<Constant<'ast>, ErrorInner> {
        let pos = expr.pos();

        match expr.value {
            Expression::U32Constant(c) => Ok(Constant::Concrete(c)),
            Expression::IntConstant(c) => {
                if c <= BigUint::from(2u128.pow(32) - 1) {
                    Ok(Constant::Concrete(
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
            Expression::Identifier(name) => Ok(Constant::Generic(name)),
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
        types: &TypeMap<'ast>,
        constants: &HashSet<Identifier<'ast>>,
    ) -> Result<DeclarationType<'ast>, ErrorInner> {
        let pos = ty.pos();
        let ty = ty.value;

        match ty {
            UnresolvedType::FieldElement => Ok(DeclarationType::FieldElement),
            UnresolvedType::Boolean => Ok(DeclarationType::Boolean),
            UnresolvedType::Uint(bitwidth) => Ok(DeclarationType::uint(bitwidth)),
            UnresolvedType::Array(t, size) => {
                let checked_size = self.check_generic_expression(size.clone())?;

                if let Constant::Generic(g) = checked_size {
                    if !constants.contains(g) {
                        return Err(ErrorInner {
                            pos: Some(pos),
                            message: format!("Undeclared generic parameter in function definition: `{}` isn\'t declared as a generic constant", g)
                        });
                    }
                };

                Ok(DeclarationType::Array(DeclarationArrayType::new(
                    self.check_declaration_type(*t, module_id, types, constants)?,
                    checked_size,
                )))
            }
            UnresolvedType::User(id) => {
                types
                    .get(module_id)
                    .unwrap()
                    .get(&id)
                    .cloned()
                    .ok_or_else(|| ErrorInner {
                        pos: Some(pos),
                        message: format!("Undefined type {}", id),
                    })
            }
        }
    }

    fn check_variable(
        &mut self,
        v: crate::absy::VariableNode<'ast>,
        module_id: &ModuleId,
        types: &TypeMap<'ast>,
    ) -> Result<Variable<'ast, T>, Vec<ErrorInner>> {
        Ok(Variable::with_id_and_type(
            v.value.id,
            self.check_type(v.value._type, module_id, types)
                .map_err(|e| vec![e])?,
        ))
    }

    fn check_for_loop(
        &mut self,
        var: crate::absy::VariableNode<'ast>,
        range: (ExpressionNode<'ast>, ExpressionNode<'ast>),
        statements: Vec<StatementNode<'ast>>,
        pos: (Position, Position),
        module_id: &ModuleId,
        types: &TypeMap<'ast>,
    ) -> Result<TypedStatement<'ast, T>, Vec<ErrorInner>> {
        self.check_for_var(&var).map_err(|e| vec![e])?;

        let var = self.check_variable(var, module_id, types).unwrap();

        let from = self
            .check_expression(range.0, module_id, &types)
            .map_err(|e| vec![e])?;
        let to = self
            .check_expression(range.1, module_id, &types)
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
                UExpression::try_from_int(v, UBitwidth::B32).map_err(|_| ErrorInner {
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
                UExpression::try_from_int(v, UBitwidth::B32).map_err(|_| ErrorInner {
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

        self.insert_into_scope(var.clone());

        let mut checked_statements = vec![];

        for stat in statements {
            let checked_stat = self.check_statement(stat, module_id, types)?;
            checked_statements.push(checked_stat);
        }

        Ok(TypedStatement::For(var, from, to, checked_statements))
    }

    fn check_statement(
        &mut self,
        stat: StatementNode<'ast>,
        module_id: &ModuleId,
        types: &TypeMap<'ast>,
    ) -> Result<TypedStatement<'ast, T>, Vec<ErrorInner>> {
        let pos = stat.pos();

        match stat.value {
            Statement::Return(e) => {
                let mut expression_list_checked = vec![];
                let mut errors = vec![];

                // we clone the return types because there might be other return statements
                let return_types = self.return_types.clone().unwrap();

                for e in e.value.expressions.into_iter() {
                    let e_checked = self
                        .check_expression(e, module_id, &types)
                        .map_err(|e| vec![e])?;
                    expression_list_checked.push(e_checked);
                }

                let res = match expression_list_checked.len() == return_types.len() {
                    true => match expression_list_checked
                        .iter()
                        .zip(return_types.clone())
                        .map(|(e, t)| TypedExpression::align_to_type(e.clone(), t.into()))
                        .collect::<Result<Vec<_>, _>>()
                        .map_err(|e| {
                            vec![ErrorInner {
                                pos: Some(pos),
                                message: format!(
                                    "Expected return value to be of type {}, found {}",
                                    e.1, e.0
                                ),
                            }]
                        }) {
                        Ok(e) => {
                            match e.iter().map(|e| e.get_type()).collect::<Vec<_>>() == return_types
                            {
                                true => {}
                                false => errors.push(ErrorInner {
                                    pos: Some(pos),
                                    message: format!(
                                        "Expected ({}) in return statement, found ({})",
                                        return_types
                                            .iter()
                                            .map(|t| t.to_string())
                                            .collect::<Vec<_>>()
                                            .join(", "),
                                        e.iter()
                                            .map(|e| e.get_type())
                                            .map(|t| t.to_string())
                                            .collect::<Vec<_>>()
                                            .join(", ")
                                    ),
                                }),
                            };
                            TypedStatement::Return(e)
                        }
                        Err(err) => {
                            errors.extend(err);
                            TypedStatement::Return(expression_list_checked)
                        }
                    },
                    false => {
                        errors.push(ErrorInner {
                            pos: Some(pos),
                            message: format!(
                                "Expected {} expressions in return statement, found {}",
                                return_types.len(),
                                expression_list_checked.len()
                            ),
                        });
                        TypedStatement::Return(expression_list_checked)
                    }
                };

                if !errors.is_empty() {
                    return Err(errors);
                }

                Ok(res)
            }
            Statement::Declaration(var) => {
                let var = self.check_variable(var, module_id, types)?;
                match self.insert_into_scope(var.clone()) {
                    true => Ok(TypedStatement::Declaration(var)),
                    false => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!("Duplicate declaration for variable named {}", var.id),
                    }),
                }
                .map_err(|e| vec![e])
            }
            Statement::Definition(assignee, expr) => {
                // we create multidef when rhs is a function call to benefit from inference
                // check rhs is not a function call here
                if let Expression::FunctionCall(..) = expr.value {
                    panic!("Parser should not generate Definition where the right hand side is a FunctionCall")
                }

                // check the expression to be assigned
                let checked_expr = self
                    .check_expression(expr, module_id, &types)
                    .map_err(|e| vec![e])?;

                // check that the assignee is declared and is well formed
                let var = self
                    .check_assignee(assignee, module_id, &types)
                    .map_err(|e| vec![e])?;

                let var_type = var.get_type();

                // make sure the assignee has the same type as the rhs
                match var_type.clone() {
                    Type::FieldElement => FieldElementExpression::try_from_typed(checked_expr)
                        .map(TypedExpression::from),
                    Type::Boolean => {
                        BooleanExpression::try_from_typed(checked_expr).map(TypedExpression::from)
                    }
                    Type::Uint(bitwidth) => UExpression::try_from_typed(checked_expr, bitwidth)
                        .map(TypedExpression::from),
                    Type::Array(array_ty) => {
                        ArrayExpression::try_from_typed(checked_expr, *array_ty.ty)
                            .map(TypedExpression::from)
                    }
                    Type::Struct(struct_ty) => {
                        StructExpression::try_from_typed(checked_expr, struct_ty)
                            .map(TypedExpression::from)
                    }
                    Type::Int => Err(checked_expr), // Integers cannot be assigned
                }
                .map_err(|e| ErrorInner {
                    pos: Some(pos),
                    message: format!(
                        "Expression {} of type {} cannot be assigned to {} of type {}",
                        e,
                        e.get_type(),
                        var.clone(),
                        var_type
                    ),
                })
                .map(|rhs| TypedStatement::Definition(var, rhs))
                .map_err(|e| vec![e])
            }
            Statement::Assertion(e) => {
                let e = self
                    .check_expression(e, module_id, &types)
                    .map_err(|e| vec![e])?;

                match e {
                    TypedExpression::Boolean(e) => Ok(TypedStatement::Assertion(e)),
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
            Statement::MultipleDefinition(assignees, rhs) => {
                match rhs.value {
                    // Right side has to be a function call
                    Expression::FunctionCall(fun_id, generics, arguments) => {
                        // check the generic arguments, if any
                        let generics_checked: Option<Vec<Option<UExpression<'ast, T>>>> = generics
                            .map(|generics|
                                generics.into_iter().map(|g|
                                    g.map(|g| {
                                        let pos = g.pos();
                                        self.check_expression(g, module_id, &types).and_then(|g| {
                                            UExpression::try_from_typed(g, UBitwidth::B32).map_err(
                                                |e| ErrorInner {
                                                    pos: Some(pos),
                                                    message: format!(
                                                        "Expected {} to be of type u32, found {}",
                                                        e,
                                                        e.get_type(),
                                                    ),
                                                },
                                            )
                                        })
                                    })
                                    .transpose()
                                )
                            .collect::<Result<_, _>>()
                        ).transpose().map_err(|e| vec![e])?;

                        // check lhs assignees are defined
                        let (assignees, errors): (Vec<_>, Vec<_>) = assignees.into_iter().map(|a| self.check_assignee(a, module_id, types)).partition(|r| r.is_ok());

                        if !errors.is_empty() {
                            return Err(errors.into_iter().map(|e| e.unwrap_err()).collect());
                        }

                        let assignees: Vec<_> = assignees.into_iter().map(|a| a.unwrap()).collect();

                        let assignee_types: Vec<_> = assignees.iter().map(|a| Some(a.get_type().clone())).collect();

                        // find argument types
                        let mut arguments_checked = vec![];
                        for arg in arguments {
                            let arg_checked = self.check_expression(arg, module_id, &types).map_err(|e| vec![e])?;
                            arguments_checked.push(arg_checked);
                        }

                        let arguments_types: Vec<_> =
                            arguments_checked.iter().map(|a| a.get_type()).collect();

                        let query = FunctionQuery::new(&fun_id, &arguments_types, &assignee_types);

                        let functions = self.find_functions(&query);

                        match functions.len() {
                    		// the function has to be defined
                    		1 => {

                                let mut functions = functions;
                                let f = functions.pop().unwrap();

                                let arguments_checked = arguments_checked.into_iter().zip(f.signature.inputs.clone()).map(|(a, t)| TypedExpression::align_to_type(a, t.into())).collect::<Result<Vec<_>, _>>().map_err(|e| vec![ErrorInner {
                                    pos: Some(pos),
                                    message: format!("Expected function call argument to be of type {}, found {} of type {}", e.1, e.0, e.0.get_type())
                                }])?;

                                let call = TypedExpressionList::FunctionCall(f.clone(), generics_checked.unwrap_or_else(|| vec![None; f.signature.generics.len()]), arguments_checked, assignees.iter().map(|a| a.get_type()).collect());

                                Ok(TypedStatement::MultipleDefinition(assignees, call))
                    		},
                    		0 => Err(ErrorInner {                         pos: Some(pos),
 message: format!("Function definition for function {} with signature {} not found.", fun_id, query) }),
                            n => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!("Ambiguous call to function {}, {} candidates were found. Please be more explicit.", fun_id, n)
                    })
                    	}
                    }
                    _ => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!("{} should be a function call", rhs),
                    }),
                }.map_err(|e| vec![e])
            }
        }
    }

    fn check_assignee(
        &mut self,
        assignee: AssigneeNode<'ast>,
        module_id: &ModuleId,
        types: &TypeMap<'ast>,
    ) -> Result<TypedAssignee<'ast, T>, ErrorInner> {
        let pos = assignee.pos();
        // check that the assignee is declared
        match assignee.value {
            Assignee::Identifier(variable_name) => match self.get_scope(&variable_name) {
                Some(var) => Ok(TypedAssignee::Identifier(Variable::with_id_and_type(
                    variable_name,
                    var.id._type.clone(),
                ))),
                None => Err(ErrorInner {
                    pos: Some(assignee.pos()),
                    message: format!("Variable `{}` is undeclared", variable_name),
                }),
            },
            Assignee::Select(box assignee, box index) => {
                let checked_assignee = self.check_assignee(assignee, module_id, &types)?;

                let ty = checked_assignee.get_type();
                match ty {
                    Type::Array(..) => {
                        let checked_index = match index {
                            RangeOrExpression::Expression(e) => {
                                self.check_expression(e, module_id, &types)?
                            }
                            r => unimplemented!(
                                "Using slices in assignments is not supported yet, found {}",
                                r
                            ),
                        };

                        let checked_typed_index =
                            UExpression::try_from_typed(checked_index, UBitwidth::B32).map_err(
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
                let checked_assignee = self.check_assignee(assignee, module_id, &types)?;

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
                            "Cannot access field {} on {} as of type {}",
                            member, checked_assignee, ty,
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
        types: &TypeMap<'ast>,
    ) -> Result<TypedExpressionOrSpread<'ast, T>, ErrorInner> {
        match spread_or_expression {
            SpreadOrExpression::Spread(s) => {
                let pos = s.pos();

                let checked_expression =
                    self.check_expression(s.value.expression, module_id, &types)?;

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
            SpreadOrExpression::Expression(e) => self
                .check_expression(e, module_id, &types)
                .map(|r| r.into()),
        }
    }

    fn check_expression(
        &mut self,
        expr: ExpressionNode<'ast>,
        module_id: &ModuleId,
        types: &TypeMap<'ast>,
    ) -> Result<TypedExpression<'ast, T>, ErrorInner> {
        let pos = expr.pos();

        match expr.value {
            Expression::IntConstant(v) => Ok(IntExpression::Value(v).into()),
            Expression::BooleanConstant(b) => Ok(BooleanExpression::Value(b).into()),
            Expression::Identifier(name) => {
                // check that `id` is defined in the scope
                match self.get_scope(&name) {
                    Some(v) => match v.id.get_type() {
                        Type::Boolean => Ok(BooleanExpression::Identifier(name.into()).into()),
                        Type::Uint(bitwidth) => Ok(UExpressionInner::Identifier(name.into())
                            .annotate(bitwidth)
                            .into()),
                        Type::FieldElement => {
                            Ok(FieldElementExpression::Identifier(name.into()).into())
                        }
                        Type::Array(array_type) => {
                            Ok(ArrayExpressionInner::Identifier(name.into())
                                .annotate(*array_type.ty, array_type.size)
                                .into())
                        }
                        Type::Struct(members) => Ok(StructExpressionInner::Identifier(name.into())
                            .annotate(members)
                            .into()),
                        Type::Int => unreachable!(),
                    },
                    None => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!("Identifier \"{}\" is undefined", name),
                    }),
                }
            }
            Expression::Add(box e1, box e2) => {
                let e1_checked = self.check_expression(e1, module_id, &types)?;
                let e2_checked = self.check_expression(e2, module_id, &types)?;

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
                let e1_checked = self.check_expression(e1, module_id, &types)?;
                let e2_checked = self.check_expression(e2, module_id, &types)?;

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
                let e1_checked = self.check_expression(e1, module_id, &types)?;
                let e2_checked = self.check_expression(e2, module_id, &types)?;

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
                let e1_checked = self.check_expression(e1, module_id, &types)?;
                let e2_checked = self.check_expression(e2, module_id, &types)?;

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
                let e1_checked = self.check_expression(e1, module_id, &types)?;
                let e2_checked = self.check_expression(e2, module_id, &types)?;

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
                let e1_checked = self.check_expression(e1, module_id, &types)?;
                let e2_checked = self.check_expression(e2, module_id, &types)?;

                let e1_checked = match FieldElementExpression::try_from_typed(e1_checked) {
                    Ok(e) => e.into(),
                    Err(e) => e,
                };
                let e2_checked = match UExpression::try_from_typed(e2_checked, UBitwidth::B32) {
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
                let e = self.check_expression(e, module_id, &types)?;

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
                let e = self.check_expression(e, module_id, &types)?;

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
            Expression::IfElse(box condition, box consequence, box alternative) => {
                let condition_checked = self.check_expression(condition, module_id, &types)?;
                let consequence_checked = self.check_expression(consequence, module_id, &types)?;
                let alternative_checked = self.check_expression(alternative, module_id, &types)?;

                let (consequence_checked, alternative_checked) =
                    TypedExpression::align_without_integers(
                        consequence_checked,
                        alternative_checked,
                    )
                    .map_err(|(e1, e2)| ErrorInner {
                        pos: Some(pos),
                        message: format!("{{consequence}} and {{alternative}} in `if/else` expression should have the same type, found {}, {}", e1.get_type(), e2.get_type()),
                    })?;

                match condition_checked {
                    TypedExpression::Boolean(condition) => {
                        match (consequence_checked, alternative_checked) {
                            (TypedExpression::FieldElement(consequence), TypedExpression::FieldElement(alternative)) => {
                                Ok(FieldElementExpression::IfElse(box condition, box consequence, box alternative).into())
                            },
                            (TypedExpression::Boolean(consequence), TypedExpression::Boolean(alternative)) => {
                                Ok(BooleanExpression::IfElse(box condition, box consequence, box alternative).into())
                            },
                            (TypedExpression::Array(consequence), TypedExpression::Array(alternative)) => {
                                let inner_type = consequence.inner_type().clone();
                                let size = consequence.size();
                                Ok(ArrayExpressionInner::IfElse(box condition, box consequence, box alternative).annotate(inner_type, size).into())
                            },
                            (TypedExpression::Struct(consequence), TypedExpression::Struct(alternative)) => {
                                let ty = consequence.ty().clone();
                                Ok(StructExpressionInner::IfElse(box condition, box consequence, box alternative).annotate(ty).into())
                            },
                            (TypedExpression::Uint(consequence), TypedExpression::Uint(alternative)) => {
                                let bitwidth = consequence.bitwidth();
                                Ok(UExpressionInner::IfElse(box condition, box consequence, box alternative).annotate(bitwidth).into())
                            },
                            (TypedExpression::Int(consequence), TypedExpression::Int(alternative)) => {
                                Ok(IntExpression::IfElse(box condition, box consequence, box alternative).into())
                            },
                            (c, a) => Err(ErrorInner {
                                pos: Some(pos),
                                message: format!("{{consequence}} and {{alternative}} in `if/else` expression should have the same type, found {}, {}", c.get_type(), a.get_type())
                            })
                        }
                    }
                    c => Err(ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "{{condition}} after `if` should be a boolean, found {}",
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
            Expression::FunctionCall(fun_id, generics, arguments) => {
                // check the generic arguments, if any
                let generics_checked: Option<Vec<Option<UExpression<'ast, T>>>> = generics
                    .map(|generics| {
                        generics
                            .into_iter()
                            .map(|g| {
                                g.map(|g| {
                                    let pos = g.pos();
                                    self.check_expression(g, module_id, &types).and_then(|g| {
                                        UExpression::try_from_typed(g, UBitwidth::B32).map_err(
                                            |e| ErrorInner {
                                                pos: Some(pos),
                                                message: format!(
                                                    "Expected {} to be of type u32, found {}",
                                                    e,
                                                    e.get_type(),
                                                ),
                                            },
                                        )
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
                    let arg_checked = self.check_expression(arg, module_id, &types)?;
                    arguments_checked.push(arg_checked);
                }

                let mut arguments_types = vec![];
                for arg in arguments_checked.iter() {
                    arguments_types.push(arg.get_type());
                }

                // outside of multidef, function calls must have a single return value
                // we use type inference to determine the type of the return, so we don't specify it
                let query = FunctionQuery::new(&fun_id, &arguments_types, &[None]);

                let functions = self.find_functions(&query);

                match functions.len() {
                    // the function has to be defined
                    1 => {
                        let mut functions = functions;

                        let f = functions.pop().unwrap();

                        let signature = f.signature;

                        let arguments_checked = arguments_checked.into_iter().zip(signature.inputs.clone()).map(|(a, t)| TypedExpression::align_to_type(a, t.into())).collect::<Result<Vec<_>, _>>().map_err(|e| ErrorInner {
                           pos: Some(pos),
                           message: format!("Expected function call argument to be of type {}, found {}", e.1, e.0)
                        })?;

                        let output_types = signature.get_output_types(arguments_checked.iter().map(|a| a.get_type()).collect()).map_err(|e| ErrorInner {
                            pos: Some(pos),
                            message: format!(
                                "Failed to infer value for generic parameter `{}`, try being more explicit by using an intermediate variable",
                                e,
                            ),
                        })?;

                        let generics_checked = generics_checked.unwrap_or_else(|| vec![None; signature.generics.len()]);

                        // the return count has to be 1
                        match output_types.len() {
                            1 => match &output_types[0] {
                                Type::Int => unreachable!(),
                                Type::FieldElement => Ok(FieldElementExpression::FunctionCall(
                                    DeclarationFunctionKey {
                                        module: module_id.to_path_buf(),
                                        id: f.id,
                                        signature: signature.clone(),
                                    },
                                    generics_checked,
                                    arguments_checked,
                                )
                                .into()),
                                Type::Boolean => Ok(BooleanExpression::FunctionCall(
                                    DeclarationFunctionKey {
                                        module: module_id.to_path_buf(),
                                        id: f.id,
                                        signature: signature.clone(),
                                    },
                                    generics_checked,
                                    arguments_checked,
                                )
                                .into()),
                                Type::Uint(bitwidth) => Ok(UExpressionInner::FunctionCall(
                                    DeclarationFunctionKey {
                                        module: module_id.to_path_buf(),
                                        id: f.id,
                                        signature: signature.clone(),
                                    },
                                    generics_checked,
                                    arguments_checked,
                                )
                                .annotate(*bitwidth)
                                .into()),
                                Type::Struct(members) => Ok(StructExpressionInner::FunctionCall(
                                    DeclarationFunctionKey {
                                        module: module_id.to_path_buf(),
                                        id: f.id,
                                        signature: signature.clone(),
                                    },
                                    generics_checked,
                                    arguments_checked,
                                )
                                .annotate(members.clone())
                                .into()),
                                Type::Array(array_type) => Ok(ArrayExpressionInner::FunctionCall(
                                    DeclarationFunctionKey {
                                        module: module_id.to_path_buf(),
                                        id: f.id,
                                        signature: signature.clone(),
                                    },
                                    generics_checked,
                                    arguments_checked,
                                )
                                .annotate(*array_type.ty.clone(), array_type.size.clone())
                                .into()),
                            },
                            n => Err(ErrorInner {
                                pos: Some(pos),

                                message: format!(
                                    "{} returns {} values but is called outside of a definition",
                                    f.id, n
                                ),
                            }),
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
            Expression::Lt(box e1, box e2) => {
                let e1_checked = self.check_expression(e1, module_id, &types)?;
                let e2_checked = self.check_expression(e2, module_id, &types)?;

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
                let e1_checked = self.check_expression(e1, module_id, &types)?;
                let e2_checked = self.check_expression(e2, module_id, &types)?;

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
                let e1_checked = self.check_expression(e1, module_id, &types)?;
                let e2_checked = self.check_expression(e2, module_id, &types)?;

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
                        Ok(BooleanExpression::FieldEq(box e1, box e2).into())
                    }
                    (TypedExpression::Boolean(e1), TypedExpression::Boolean(e2)) => {
                        Ok(BooleanExpression::BoolEq(box e1, box e2).into())
                    }
                    (TypedExpression::Array(e1), TypedExpression::Array(e2)) => {
                        Ok(BooleanExpression::ArrayEq(box e1, box e2).into())
                    }
                    (TypedExpression::Struct(e1), TypedExpression::Struct(e2))
                        if e1.get_type() == e2.get_type() =>
                    {
                        Ok(BooleanExpression::StructEq(box e1, box e2).into())
                    }
                    (TypedExpression::Uint(e1), TypedExpression::Uint(e2))
                        if e1.get_type() == e2.get_type() =>
                    {
                        Ok(BooleanExpression::UintEq(box e1, box e2).into())
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
                let e1_checked = self.check_expression(e1, module_id, &types)?;
                let e2_checked = self.check_expression(e2, module_id, &types)?;

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
                let e1_checked = self.check_expression(e1, module_id, &types)?;
                let e2_checked = self.check_expression(e2, module_id, &types)?;

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
                let array = self.check_expression(array, module_id, &types)?;

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
                                    .map(|e| self.check_expression(e, module_id, &types))
                                    .unwrap_or_else(|| Ok(UExpression::from(0u32).into()))?;

                                let to = r
                                    .value
                                    .to
                                    .map(|e| self.check_expression(e, module_id, &types))
                                    .unwrap_or_else(|| Ok(array_size.clone().into()))?;

                                let from = UExpression::try_from_typed(from, UBitwidth::B32).map_err(|e| ErrorInner {
                                                    pos: Some(pos),
                                                    message: format!(
                                                        "Expected the lower bound of the range to be a u32, found {} of type {}",
                                                        e,
                                                        e.get_type()
                                                    ),
                                                })?;

                                let to = UExpression::try_from_typed(to, UBitwidth::B32).map_err(|e| ErrorInner {
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
                        let index = self.check_expression(index, module_id, &types)?;

                        let index =
                            UExpression::try_from_typed(index, UBitwidth::B32).map_err(|e| {
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
                                    Type::Int => unreachable!(),
                                }
                            }
                            a => Err(ErrorInner {
                                pos: Some(pos),
                                message: format!(
                                    "Cannot access element as index {} of type {} on expression {} of type {}",
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
            Expression::Member(box e, box id) => {
                let e = self.check_expression(e, module_id, &types)?;

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
                                Type::Array(array_type) => {
                                    Ok(ArrayExpressionInner::Member(box s.clone(), id.to_string())
                                        .annotate(*array_type.ty.clone(), array_type.size)
                                        .into())
                                }
                                Type::Struct(..) => {
                                    Ok(StructExpression::member(s.clone(), id.to_string()).into())
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
                    let e_checked = self.check_spread_or_expression(e, module_id, &types)?;
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

                let unwrapped_expressions_or_spreads = match &inferred_type {
                    Type::Int => expressions_or_spreads_checked,
                    t => expressions_or_spreads_checked
                        .into_iter()
                        .map(|e| {
                            TypedExpressionOrSpread::align_to_type(e, t.clone()).map_err(
                                |(e, ty)| ErrorInner {
                                    pos: Some(pos),
                                    message: format!("Expected {} to have type {}", e, ty,),
                                },
                            )
                        })
                        .collect::<Result<Vec<_>, _>>()?,
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
            Expression::ArrayInitializer(box e, box count) => {
                let e = self.check_expression(e, module_id, &types)?;
                let ty = e.get_type();

                let count = self.check_expression(count, module_id, &types)?;

                let count =
                    UExpression::try_from_typed(count, UBitwidth::B32).map_err(|e| ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "Expected array initializer count to be a u32, found {} of type {}",
                            e,
                            e.get_type(),
                        ),
                    })?;

                Ok(ArrayExpressionInner::Repeat(box e, box count.clone())
                    .annotate(ty, count)
                    .into())
            }
            Expression::InlineStruct(id, inline_members) => {
                let ty = self.check_type(
                    UnresolvedType::User(id.clone()).at(42, 42, 42),
                    module_id,
                    &types,
                )?;
                let struct_type = match ty {
                    Type::Struct(struct_type) => struct_type,
                    _ => unreachable!(),
                };

                // check that we provided the required number of values

                if struct_type.members_count() != inline_members.len() {
                    return Err(ErrorInner {
                        pos: Some(pos),
                        message: format!(
                            "Inline struct {} does not match {} {{{}}}",
                            Expression::InlineStruct(id, inline_members),
                            Type::Struct(struct_type.clone()),
                            struct_type
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
                    .collect::<HashMap<_, _>>();
                let mut result: Vec<TypedExpression<'ast, T>> = vec![];

                for member in struct_type.iter() {
                    match inline_members_map.remove(member.id.as_str()) {
                        Some(value) => {
                            let expression_checked =
                                self.check_expression(value, module_id, &types)?;

                            let expression_checked = TypedExpression::align_to_type(
                                expression_checked,
                                *member.ty.clone(),
                            )
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

                            result.push(expression_checked);
                        }
                        None => {
                            return Err(ErrorInner {
                                pos: Some(pos),
                                message: format!(
                                    "Member {} of struct {} {{{}}} not found in value {}",
                                    member.id,
                                    Type::Struct(struct_type.clone()),
                                    struct_type
                                        .members
                                        .iter()
                                        .map(|m| format!("{}: {}", m.id, m.ty))
                                        .collect::<Vec<_>>()
                                        .join(", "),
                                    Expression::InlineStruct(id, inline_members),
                                ),
                            })
                        }
                    }
                }

                Ok(StructExpressionInner::Value(result)
                    .annotate(struct_type)
                    .into())
            }
            Expression::And(box e1, box e2) => {
                let e1_checked = self.check_expression(e1, module_id, &types)?;
                let e2_checked = self.check_expression(e2, module_id, &types)?;

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
                let e1_checked = self.check_expression(e1, module_id, &types)?;
                let e2_checked = self.check_expression(e2, module_id, &types)?;
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
                let e1 = self.check_expression(e1, module_id, &types)?;
                let e2 = self.check_expression(e2, module_id, &types)?;

                let e2 =
                    UExpression::try_from_typed(e2, UBitwidth::B32).map_err(|e| ErrorInner {
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
                let e1 = self.check_expression(e1, module_id, &types)?;
                let e2 = self.check_expression(e2, module_id, &types)?;

                let e2 =
                    UExpression::try_from_typed(e2, UBitwidth::B32).map_err(|e| ErrorInner {
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
                let e1_checked = self.check_expression(e1, module_id, &types)?;
                let e2_checked = self.check_expression(e2, module_id, &types)?;

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
                let e1_checked = self.check_expression(e1, module_id, &types)?;
                let e2_checked = self.check_expression(e2, module_id, &types)?;

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
                let e1_checked = self.check_expression(e1, module_id, &types)?;
                let e2_checked = self.check_expression(e2, module_id, &types)?;

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
                let e_checked = self.check_expression(e, module_id, &types)?;
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

    fn get_scope<'a>(&'a self, variable_name: &'ast str) -> Option<&'a ScopedVariable<'ast, T>> {
        // we take advantage of the fact that all ScopedVariable of the same identifier hash to the same thing
        // and by construction only one can be in the set
        self.scope.get(&ScopedVariable {
            id: Variable::with_id_and_type(
                crate::typed_absy::Identifier::from(variable_name),
                Type::FieldElement,
            ),
            level: 0,
        })
    }

    fn insert_into_scope<U: Into<Variable<'ast, T>>>(&mut self, v: U) -> bool {
        self.scope.insert(ScopedVariable {
            id: v.into(),
            level: self.level,
        })
    }

    fn find_functions(&self, query: &FunctionQuery<'ast, T>) -> Vec<DeclarationFunctionKey<'ast>> {
        query.match_funcs(&self.functions)
    }

    fn enter_scope(&mut self) {
        self.level += 1;
    }

    fn exit_scope(&mut self) {
        let current_level = self.level;
        self.scope
            .retain(|ref scoped_variable| scoped_variable.level < current_level);
        self.level -= 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::absy;
    use crate::typed_absy;
    use lazy_static::lazy_static;
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

            let types = HashMap::new();

            let expr = Expression::FieldConstant(Bn128Field::max_value().to_biguint()).mock();
            assert!(Checker::<Bn128Field>::new()
                .check_expression(expr, &*MODULE_ID, &types)
                .is_ok());
        }

        #[test]
        fn field_overflow() {
            // the value of `P` is an invalid field literal

            let types = HashMap::new();

            let value = Bn128Field::max_value().to_biguint().add(1u32);
            let expr = Expression::FieldConstant(value).mock();

            assert!(Checker::<Bn128Field>::new()
                .check_expression(expr, &*MODULE_ID, &types)
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

            let types = HashMap::new();
            // [3, true]
            let a = Expression::InlineArray(vec![
                Expression::IntConstant(3usize.into()).mock().into(),
                Expression::BooleanConstant(true).mock().into(),
            ])
            .mock();
            assert!(Checker::<Bn128Field>::new()
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
            assert!(Checker::<Bn128Field>::new()
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
            assert!(Checker::<Bn128Field>::new()
                .check_expression(a, &*MODULE_ID, &types)
                .is_err());
        }
    }

    /// Helper function to create ((): return)
    fn function0() -> FunctionNode<'static> {
        let statements = vec![Statement::Return(
            ExpressionList {
                expressions: vec![],
            }
            .mock(),
        )
        .mock()];

        let arguments = vec![];

        let signature = UnresolvedSignature::new();

        Function {
            arguments,
            statements,
            signature,
        }
        .mock()
    }

    /// Helper function to create ((private field a): return)
    fn function1() -> FunctionNode<'static> {
        let statements = vec![Statement::Return(
            ExpressionList {
                expressions: vec![],
            }
            .mock(),
        )
        .mock()];

        let arguments = vec![absy::Parameter {
            id: absy::Variable::new("a", UnresolvedType::FieldElement.mock()).mock(),
            private: true,
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
            StructDefinition { fields: vec![] }.mock()
        }

        fn struct1() -> StructDefinitionNode<'static> {
            StructDefinition {
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

            let mut unifier = SymbolUnifier::default();

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
                    .generics(vec![Some("K".into())])
                    .inputs(vec![DeclarationType::FieldElement])
            ));
            // a `bar` function with a different signature
            assert!(unifier.insert_function(
                "bar",
                DeclarationSignature::new()
                    .generics(vec![Some("K".into())])
                    .inputs(vec![DeclarationType::array((
                        DeclarationType::FieldElement,
                        "K"
                    ))])
            ));
            // a `bar` function with a different signature, but which could conflict with the previous one
            assert!(!unifier.insert_function(
                "bar",
                DeclarationSignature::new().inputs(vec![DeclarationType::array((
                    DeclarationType::FieldElement,
                    42u32
                ))])
            ));
            // a `bar` type isn't allowed as the name is already taken by at least one function
            assert!(!unifier.insert_type("bar"));
        }

        #[test]
        fn imported_function() {
            // foo.zok
            // def main():
            // 		return

            // bar.zok
            // from "./foo.zok" import main

            // after semantic check, `bar` should import a checked function

            let foo: Module = Module {
                symbols: vec![SymbolDeclaration {
                    id: "main",
                    symbol: Symbol::HereFunction(function0()),
                }
                .mock()],
                imports: vec![],
            };

            let bar: Module = Module {
                symbols: vec![SymbolDeclaration {
                    id: "main",
                    symbol: Symbol::There(SymbolImport::with_id_in_module("main", "foo").mock()),
                }
                .mock()],
                imports: vec![],
            };

            let mut state = State::<Bn128Field>::new(
                vec![("foo".into(), foo), ("bar".into(), bar)]
                    .into_iter()
                    .collect(),
            );

            let mut checker: Checker<Bn128Field> = Checker::new();

            assert_eq!(
                checker.check_module(&OwnedTypedModuleId::from("bar"), &mut state),
                Ok(())
            );
            assert_eq!(
                state.typed_modules.get(&PathBuf::from("bar")),
                Some(&TypedModule {
                    functions: vec![(
                        DeclarationFunctionKey::with_location("bar", "main")
                            .signature(DeclarationSignature::new()),
                        TypedFunctionSymbol::There(
                            DeclarationFunctionKey::with_location("foo", "main")
                                .signature(DeclarationSignature::new()),
                        )
                    )]
                    .into_iter()
                    .collect(),
                })
            );
        }

        #[test]
        fn duplicate_function_declaration() {
            // def foo():
            //   return
            // def foo():
            //   return
            //
            // should fail

            let module = Module {
                symbols: vec![
                    SymbolDeclaration {
                        id: "foo",
                        symbol: Symbol::HereFunction(function0()),
                    }
                    .mock(),
                    SymbolDeclaration {
                        id: "foo",
                        symbol: Symbol::HereFunction(function0()),
                    }
                    .mock(),
                ],
                imports: vec![],
            };

            let mut state = State::<Bn128Field>::new(
                vec![((*MODULE_ID).clone(), module)].into_iter().collect(),
            );

            let mut checker: Checker<Bn128Field> = Checker::new();
            assert_eq!(
                checker.check_module(&*MODULE_ID, &mut state).unwrap_err()[0]
                    .inner
                    .message,
                "foo conflicts with another symbol"
            );
        }

        #[test]
        fn duplicate_function_declaration_generic() {
            // def foo<P>(private field[P] a):
            //   return
            // def foo(private field[3] a):
            //   return
            //
            // should fail as P could be equal to 3

            let mut f0 = function0();

            f0.value.arguments = vec![absy::Parameter::private(
                absy::Variable::new(
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
            f1.value.arguments = vec![absy::Parameter::private(
                absy::Variable::new(
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
                        symbol: Symbol::HereFunction(f0),
                    }
                    .mock(),
                    SymbolDeclaration {
                        id: "foo",
                        symbol: Symbol::HereFunction(f1),
                    }
                    .mock(),
                ],
                imports: vec![],
            };

            let mut state = State::new(vec![((*MODULE_ID).clone(), module)].into_iter().collect());

            let mut checker: Checker<Bn128Field> = Checker::new();
            assert_eq!(
                checker.check_module(&*MODULE_ID, &mut state).unwrap_err()[0]
                    .inner
                    .message,
                "foo conflicts with another symbol"
            );
        }

        mod generics {
            use super::*;

            #[test]
            fn unused_generic() {
                // def foo<P>():
                //   return
                // def main():
                //   return
                //
                // should succeed

                let mut foo = function0();

                foo.value.signature = UnresolvedSignature::new().generics(vec!["P".mock()]);

                let module = Module {
                    symbols: vec![
                        SymbolDeclaration {
                            id: "foo",
                            symbol: Symbol::HereFunction(foo),
                        }
                        .mock(),
                        SymbolDeclaration {
                            id: "main",
                            symbol: Symbol::HereFunction(function0()),
                        }
                        .mock(),
                    ],
                    imports: vec![],
                };

                let mut state =
                    State::new(vec![((*MODULE_ID).clone(), module)].into_iter().collect());

                let mut checker: Checker<Bn128Field> = Checker::new();
                assert!(checker.check_module(&*MODULE_ID, &mut state).is_ok());
            }

            #[test]
            fn undeclared_generic() {
                // def foo(field[P] a):
                //   return
                // def main():
                //   return
                //
                // should fail

                let mut foo = function0();

                foo.value.arguments = vec![absy::Parameter::private(
                    absy::Variable::new(
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
                            symbol: Symbol::HereFunction(foo),
                        }
                        .mock(),
                        SymbolDeclaration {
                            id: "main",
                            symbol: Symbol::HereFunction(function0()),
                        }
                        .mock(),
                    ],
                    imports: vec![],
                };

                let mut state =
                    State::new(vec![((*MODULE_ID).clone(), module)].into_iter().collect());

                let mut checker: Checker<Bn128Field> = Checker::new();
                assert_eq!(
                    checker
                        .check_module(&*MODULE_ID, &mut state)
                        .unwrap_err()[0]
                        .inner
                        .message,
                    "Undeclared generic parameter in function definition: `P` isn\'t declared as a generic constant"
                );
            }
        }

        #[test]
        fn overloaded_function_declaration() {
            // def foo():
            //   return
            // def foo(a):
            //   return
            //
            // should succeed as overloading is allowed

            let module = Module {
                symbols: vec![
                    SymbolDeclaration {
                        id: "foo",
                        symbol: Symbol::HereFunction(function0()),
                    }
                    .mock(),
                    SymbolDeclaration {
                        id: "foo",
                        symbol: Symbol::HereFunction(function1()),
                    }
                    .mock(),
                ],
                imports: vec![],
            };

            let mut state = State::<Bn128Field>::new(
                vec![((*MODULE_ID).clone(), module)].into_iter().collect(),
            );

            let mut checker: Checker<Bn128Field> = Checker::new();
            assert_eq!(checker.check_module(&*MODULE_ID, &mut state), Ok(()));
            assert!(state
                .typed_modules
                .get(&*MODULE_ID)
                .unwrap()
                .functions
                .contains_key(
                    &DeclarationFunctionKey::with_location((*MODULE_ID).clone(), "foo")
                        .signature(DeclarationSignature::new())
                ));
            assert!(state
                .typed_modules
                .get(&*MODULE_ID)
                .unwrap()
                .functions
                .contains_key(
                    &DeclarationFunctionKey::with_location((*MODULE_ID).clone(), "foo").signature(
                        DeclarationSignature::new().inputs(vec![DeclarationType::FieldElement])
                    )
                ))
        }

        #[test]
        fn duplicate_type_declaration() {
            // struct Foo {}
            // struct Foo { foo: field }
            //
            // should fail

            let module: Module = Module {
                symbols: vec![
                    SymbolDeclaration {
                        id: "foo",
                        symbol: Symbol::HereType(struct0()),
                    }
                    .mock(),
                    SymbolDeclaration {
                        id: "foo",
                        symbol: Symbol::HereType(struct1()),
                    }
                    .mock(),
                ],
                imports: vec![],
            };

            let mut state = State::<Bn128Field>::new(
                vec![((*MODULE_ID).clone(), module)].into_iter().collect(),
            );

            let mut checker: Checker<Bn128Field> = Checker::new();
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
            // def foo():
            //   return
            //
            // should fail

            let module = Module {
                symbols: vec![
                    SymbolDeclaration {
                        id: "foo",
                        symbol: Symbol::HereFunction(function0()),
                    }
                    .mock(),
                    SymbolDeclaration {
                        id: "foo",
                        symbol: Symbol::HereType(StructDefinition { fields: vec![] }.mock()),
                    }
                    .mock(),
                ],
                imports: vec![],
            };

            let mut state = State::<Bn128Field>::new(
                vec![((*MODULE_ID).clone(), module)].into_iter().collect(),
            );

            let mut checker: Checker<Bn128Field> = Checker::new();
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
            // def main(): return
            //
            // // main.code
            // import main from "bar" as foo
            // struct foo {}
            //
            // should fail

            let bar = Module::with_symbols(vec![SymbolDeclaration {
                id: "main",
                symbol: Symbol::HereFunction(function0()),
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
                        symbol: Symbol::HereType(struct0()),
                    }
                    .mock(),
                ],
                imports: vec![],
            };

            let mut state = State::<Bn128Field>::new(
                vec![((*MODULE_ID).clone(), main), ("bar".into(), bar)]
                    .into_iter()
                    .collect(),
            );

            let mut checker: Checker<Bn128Field> = Checker::new();
            assert_eq!(
                checker.check_module(&*MODULE_ID, &mut state).unwrap_err()[0]
                    .inner
                    .message,
                "foo conflicts with another symbol"
            );

            // type declaration first

            // // bar.code
            // def main(): return
            //
            // // main.code
            // struct foo {}
            // import main from "bar" as foo
            //
            // should fail

            let bar = Module::with_symbols(vec![SymbolDeclaration {
                id: "main",
                symbol: Symbol::HereFunction(function0()),
            }
            .mock()]);

            let main = Module {
                symbols: vec![
                    SymbolDeclaration {
                        id: "foo",
                        symbol: Symbol::HereType(struct0()),
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
                imports: vec![],
            };

            let mut state = State::<Bn128Field>::new(
                vec![((*MODULE_ID).clone(), main), ("bar".into(), bar)]
                    .into_iter()
                    .collect(),
            );

            let mut checker: Checker<Bn128Field> = Checker::new();
            assert_eq!(
                checker.check_module(&*MODULE_ID, &mut state).unwrap_err()[0]
                    .inner
                    .message,
                "foo conflicts with another symbol"
            );
        }
    }

    pub fn new_with_args<'ast, T: Field>(
        scope: HashSet<ScopedVariable<'ast, T>>,
        level: usize,
        functions: HashSet<DeclarationFunctionKey<'ast>>,
    ) -> Checker<'ast, T> {
        Checker {
            scope,
            functions,
            level,
            return_types: None,
        }
    }

    // checking function signatures
    mod signature {
        use super::*;

        #[test]
        fn undeclared_generic() {
            let signature = UnresolvedSignature::new().inputs(vec![UnresolvedType::Array(
                box UnresolvedType::FieldElement.mock(),
                Expression::Identifier("K").mock(),
            )
            .mock()]);
            assert_eq!(Checker::<Bn128Field>::new().check_signature(signature, &*MODULE_ID, &TypeMap::default()), Err(vec![ErrorInner {
                pos: Some((Position::mock(), Position::mock())),
                message: "Undeclared generic parameter in function definition: `K` isn\'t declared as a generic constant".to_string()
            }]));
        }

        #[test]
        fn success() {
            // <K, L, M>(field[L][K]) -> field[L][K]

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
                .outputs(vec![UnresolvedType::Array(
                    box UnresolvedType::Array(
                        box UnresolvedType::FieldElement.mock(),
                        Expression::Identifier("L").mock(),
                    )
                    .mock(),
                    Expression::Identifier("K").mock(),
                )
                .mock()]);
            assert_eq!(
                Checker::<Bn128Field>::new().check_signature(
                    signature,
                    &*MODULE_ID,
                    &TypeMap::default()
                ),
                Ok(DeclarationSignature::new()
                    .inputs(vec![DeclarationType::array((
                        DeclarationType::array((DeclarationType::FieldElement, "K")),
                        "L"
                    ))])
                    .outputs(vec![DeclarationType::array((
                        DeclarationType::array((DeclarationType::FieldElement, "L")),
                        "K"
                    ))]))
            );
        }
    }

    #[test]
    fn undefined_variable_in_statement() {
        // a = b
        // b undefined
        let statement: StatementNode = Statement::Definition(
            Assignee::Identifier("a").mock(),
            Expression::Identifier("b").mock(),
        )
        .mock();

        let types = HashMap::new();

        let mut checker: Checker<Bn128Field> = Checker::new();
        assert_eq!(
            checker.check_statement(statement, &*MODULE_ID, &types),
            Err(vec![ErrorInner {
                pos: Some((Position::mock(), Position::mock())),
                message: "Identifier \"b\" is undefined".into()
            }])
        );
    }

    #[test]
    fn defined_variable_in_statement() {
        // a = b
        // b defined
        let statement: StatementNode = Statement::Definition(
            Assignee::Identifier("a").mock(),
            Expression::Identifier("b").mock(),
        )
        .mock();

        let types = HashMap::new();

        let mut scope = HashSet::new();
        scope.insert(ScopedVariable {
            id: Variable::field_element("a"),
            level: 0,
        });
        scope.insert(ScopedVariable {
            id: Variable::field_element("b"),
            level: 0,
        });
        let mut checker: Checker<Bn128Field> = new_with_args(scope, 1, HashSet::new());
        assert_eq!(
            checker.check_statement(statement, &*MODULE_ID, &types),
            Ok(TypedStatement::Definition(
                TypedAssignee::Identifier(typed_absy::Variable::field_element("a")),
                FieldElementExpression::Identifier("b".into()).into()
            ))
        );
    }

    #[test]
    fn declared_in_other_function() {
        // def foo():
        //   field a = 1
        //   return
        // def bar():
        //   return a
        // should fail
        let foo_args = vec![];
        let foo_statements = vec![
            Statement::Declaration(
                absy::Variable::new("a", UnresolvedType::FieldElement.mock()).mock(),
            )
            .mock(),
            Statement::Definition(
                Assignee::Identifier("a").mock(),
                Expression::IntConstant(1usize.into()).mock(),
            )
            .mock(),
            Statement::Return(
                ExpressionList {
                    expressions: vec![],
                }
                .mock(),
            )
            .mock(),
        ];
        let foo = Function {
            arguments: foo_args,
            statements: foo_statements,
            signature: UnresolvedSignature::new(),
        }
        .mock();

        let bar_args = vec![];
        let bar_statements = vec![Statement::Return(
            ExpressionList {
                expressions: vec![Expression::Identifier("a").mock()],
            }
            .mock(),
        )
        .mock()];

        let bar = Function {
            arguments: bar_args,
            statements: bar_statements,
            signature: UnresolvedSignature::new()
                .inputs(vec![])
                .outputs(vec![UnresolvedType::FieldElement.mock()]),
        }
        .mock();

        let symbols = vec![
            SymbolDeclaration {
                id: "foo",
                symbol: Symbol::HereFunction(foo),
            }
            .mock(),
            SymbolDeclaration {
                id: "bar",
                symbol: Symbol::HereFunction(bar),
            }
            .mock(),
        ];
        let module = Module {
            symbols,
            imports: vec![],
        };

        let mut state =
            State::<Bn128Field>::new(vec![((*MODULE_ID).clone(), module)].into_iter().collect());

        let mut checker: Checker<Bn128Field> = Checker::new();
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
        // def foo():
        //   a = 1
        //   return
        // def bar():
        //   a = 2
        //   return
        // def main():
        //   return 1
        // should pass
        let foo_args = vec![];
        let foo_statements = vec![
            Statement::Declaration(
                absy::Variable::new("a", UnresolvedType::FieldElement.mock()).mock(),
            )
            .mock(),
            Statement::Definition(
                Assignee::Identifier("a").mock(),
                Expression::IntConstant(1usize.into()).mock(),
            )
            .mock(),
            Statement::Return(
                ExpressionList {
                    expressions: vec![],
                }
                .mock(),
            )
            .mock(),
        ];

        let foo = Function {
            arguments: foo_args,
            statements: foo_statements,
            signature: UnresolvedSignature::new(),
        }
        .mock();

        let bar_args = vec![];
        let bar_statements = vec![
            Statement::Declaration(
                absy::Variable::new("a", UnresolvedType::FieldElement.mock()).mock(),
            )
            .mock(),
            Statement::Definition(
                Assignee::Identifier("a").mock(),
                Expression::IntConstant(2usize.into()).mock(),
            )
            .mock(),
            Statement::Return(
                ExpressionList {
                    expressions: vec![],
                }
                .mock(),
            )
            .mock(),
        ];
        let bar = Function {
            arguments: bar_args,
            statements: bar_statements,
            signature: UnresolvedSignature::new(),
        }
        .mock();

        let main_args = vec![];
        let main_statements = vec![Statement::Return(
            ExpressionList {
                expressions: vec![Expression::IntConstant(1usize.into()).mock()],
            }
            .mock(),
        )
        .mock()];

        let main = Function {
            arguments: main_args,
            statements: main_statements,
            signature: UnresolvedSignature::new()
                .inputs(vec![])
                .outputs(vec![UnresolvedType::FieldElement.mock()]),
        }
        .mock();

        let symbols = vec![
            SymbolDeclaration {
                id: "foo",
                symbol: Symbol::HereFunction(foo),
            }
            .mock(),
            SymbolDeclaration {
                id: "bar",
                symbol: Symbol::HereFunction(bar),
            }
            .mock(),
            SymbolDeclaration {
                id: "main",
                symbol: Symbol::HereFunction(main),
            }
            .mock(),
        ];
        let module = Module {
            symbols,
            imports: vec![],
        };

        let mut state =
            State::<Bn128Field>::new(vec![((*MODULE_ID).clone(), module)].into_iter().collect());

        let mut checker: Checker<Bn128Field> = Checker::new();
        assert!(checker.check_module(&*MODULE_ID, &mut state).is_ok());
    }

    #[test]
    fn for_index_after_end() {
        // def foo():
        //   for field i in 0..10 do
        //   endfor
        //   return i
        // should fail
        let foo_statements: Vec<StatementNode> = vec![
            Statement::For(
                absy::Variable::new("i", UnresolvedType::Uint(32).mock()).mock(),
                Expression::IntConstant(0usize.into()).mock(),
                Expression::IntConstant(10usize.into()).mock(),
                vec![],
            )
            .mock(),
            Statement::Return(
                ExpressionList {
                    expressions: vec![Expression::Identifier("i").mock()],
                }
                .mock(),
            )
            .mock(),
        ];
        let foo = Function {
            arguments: vec![],
            statements: foo_statements,
            signature: UnresolvedSignature::new()
                .inputs(vec![])
                .outputs(vec![UnresolvedType::FieldElement.mock()]),
        }
        .mock();

        let types = HashMap::new();

        let mut checker: Checker<Bn128Field> = Checker::new();
        assert_eq!(
            checker.check_function(foo, &*MODULE_ID, &types),
            Err(vec![ErrorInner {
                pos: Some((Position::mock(), Position::mock())),
                message: "Identifier \"i\" is undefined".into()
            }])
        );
    }

    #[test]
    fn for_index_in_for() {
        // def foo():
        //   for field i in 0..10 do
        //     a = i
        //   endfor
        //   return
        // should pass

        let for_statements = vec![
            Statement::Declaration(
                absy::Variable::new("a", UnresolvedType::Uint(32).mock()).mock(),
            )
            .mock(),
            Statement::Definition(
                Assignee::Identifier("a").mock(),
                Expression::Identifier("i").mock(),
            )
            .mock(),
        ];

        let foo_statements = vec![
            Statement::For(
                absy::Variable::new("i", UnresolvedType::Uint(32).mock()).mock(),
                Expression::IntConstant(0usize.into()).mock(),
                Expression::IntConstant(10usize.into()).mock(),
                for_statements,
            )
            .mock(),
            Statement::Return(
                ExpressionList {
                    expressions: vec![],
                }
                .mock(),
            )
            .mock(),
        ];

        let for_statements_checked = vec![
            TypedStatement::Declaration(typed_absy::Variable::uint("a", UBitwidth::B32)),
            TypedStatement::Definition(
                TypedAssignee::Identifier(typed_absy::Variable::uint("a", UBitwidth::B32)),
                UExpressionInner::Identifier("i".into())
                    .annotate(UBitwidth::B32)
                    .into(),
            ),
        ];

        let foo_statements_checked = vec![
            TypedStatement::For(
                typed_absy::Variable::uint("i", UBitwidth::B32),
                0u32.into(),
                10u32.into(),
                for_statements_checked,
            ),
            TypedStatement::Return(vec![]),
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

        let types = HashMap::new();

        let mut checker: Checker<Bn128Field> = Checker::new();
        assert_eq!(
            checker.check_function(foo, &*MODULE_ID, &types),
            Ok(foo_checked)
        );
    }

    #[test]
    fn arity_mismatch() {
        // def foo():
        //   return 1, 2
        // def bar():
        //   field a = foo()
        // should fail
        let bar_statements: Vec<StatementNode> = vec![
            Statement::Declaration(
                absy::Variable::new("a", UnresolvedType::FieldElement.mock()).mock(),
            )
            .mock(),
            Statement::MultipleDefinition(
                vec![Assignee::Identifier("a").mock()],
                Expression::FunctionCall("foo", None, vec![]).mock(),
            )
            .mock(),
            Statement::Return(
                ExpressionList {
                    expressions: vec![],
                }
                .mock(),
            )
            .mock(),
        ];

        let foo = DeclarationFunctionKey {
            module: (*MODULE_ID).clone(),
            id: "foo",
            signature: DeclarationSignature::new().inputs(vec![]).outputs(vec![
                DeclarationType::FieldElement,
                DeclarationType::FieldElement,
            ]),
        };

        let functions = vec![foo].into_iter().collect();

        let bar = Function {
            arguments: vec![],
            statements: bar_statements,
            signature: UnresolvedSignature::new(),
        }
        .mock();

        let types = HashMap::new();

        let mut checker: Checker<Bn128Field> = new_with_args(HashSet::new(), 0, functions);
        assert_eq!(
            checker.check_function(bar, &*MODULE_ID, &types),
            Err(vec![ErrorInner {
                pos: Some((Position::mock(), Position::mock())),
                message:
                    "Function definition for function foo with signature () -> field not found."
                        .into()
            }])
        );
    }

    #[test]
    fn multi_return_outside_multidef() {
        // def foo() -> (field, field):
        //   return 1, 2
        // def bar():
        //   2 == foo()
        //   return
        // should fail
        let bar_statements: Vec<StatementNode> = vec![
            Statement::Assertion(
                Expression::Eq(
                    box Expression::IntConstant(2usize.into()).mock(),
                    box Expression::FunctionCall("foo", None, vec![]).mock(),
                )
                .mock(),
            )
            .mock(),
            Statement::Return(
                ExpressionList {
                    expressions: vec![],
                }
                .mock(),
            )
            .mock(),
        ];

        let foo = DeclarationFunctionKey {
            module: (*MODULE_ID).clone(),
            id: "foo",
            signature: DeclarationSignature::new().inputs(vec![]).outputs(vec![
                DeclarationType::FieldElement,
                DeclarationType::FieldElement,
            ]),
        };

        let functions = vec![foo].into_iter().collect();

        let bar = Function {
            arguments: vec![],
            statements: bar_statements,
            signature: UnresolvedSignature::new(),
        }
        .mock();

        let types = HashMap::new();

        let mut checker: Checker<Bn128Field> = new_with_args(HashSet::new(), 0, functions);
        assert_eq!(
            checker.check_function(bar, &*MODULE_ID, &types),
            Err(vec![ErrorInner {
                pos: Some((Position::mock(), Position::mock())),
                message: "Function definition for function foo with signature () -> _ not found."
                    .into()
            }])
        );
    }

    #[test]
    fn function_undefined_in_multidef() {
        // def bar():
        //   field a = foo()
        //   return
        // should fail
        let bar_statements: Vec<StatementNode> = vec![
            Statement::Declaration(
                absy::Variable::new("a", UnresolvedType::FieldElement.mock()).mock(),
            )
            .mock(),
            Statement::MultipleDefinition(
                vec![Assignee::Identifier("a").mock()],
                Expression::FunctionCall("foo", None, vec![]).mock(),
            )
            .mock(),
            Statement::Return(
                ExpressionList {
                    expressions: vec![],
                }
                .mock(),
            )
            .mock(),
        ];

        let bar = Function {
            arguments: vec![],
            statements: bar_statements,
            signature: UnresolvedSignature::new(),
        }
        .mock();

        let types = HashMap::new();

        let mut checker: Checker<Bn128Field> = new_with_args(HashSet::new(), 0, HashSet::new());
        assert_eq!(
            checker.check_function(bar, &*MODULE_ID, &types),
            Err(vec![ErrorInner {
                pos: Some((Position::mock(), Position::mock())),

                message:
                    "Function definition for function foo with signature () -> field not found."
                        .into()
            }])
        );
    }

    #[test]
    fn undefined_variable_in_multireturn_call() {
        // def foo(x):
        // 	return 1, 2
        // def main():
        // 	a, b = foo(x)
        // 	return 1
        // should fail

        let foo_statements: Vec<StatementNode> = vec![Statement::Return(
            ExpressionList {
                expressions: vec![
                    Expression::IntConstant(1usize.into()).mock(),
                    Expression::IntConstant(2usize.into()).mock(),
                ],
            }
            .mock(),
        )
        .mock()];

        let foo = Function {
            arguments: vec![crate::absy::Parameter {
                id: absy::Variable::new("x", UnresolvedType::FieldElement.mock()).mock(),
                private: false,
            }
            .mock()],
            statements: foo_statements,
            signature: UnresolvedSignature::new()
                .inputs(vec![UnresolvedType::FieldElement.mock()])
                .outputs(vec![
                    UnresolvedType::FieldElement.mock(),
                    UnresolvedType::FieldElement.mock(),
                ]),
        }
        .mock();

        let main_statements: Vec<StatementNode> = vec![
            Statement::Declaration(
                absy::Variable::new("a", UnresolvedType::FieldElement.mock()).mock(),
            )
            .mock(),
            Statement::Declaration(
                absy::Variable::new("b", UnresolvedType::FieldElement.mock()).mock(),
            )
            .mock(),
            Statement::MultipleDefinition(
                vec![
                    Assignee::Identifier("a").mock(),
                    Assignee::Identifier("b").mock(),
                ],
                Expression::FunctionCall("foo", None, vec![Expression::Identifier("x").mock()])
                    .mock(),
            )
            .mock(),
            Statement::Return(
                ExpressionList {
                    expressions: vec![Expression::IntConstant(1usize.into()).mock()],
                }
                .mock(),
            )
            .mock(),
        ];

        let main = Function {
            arguments: vec![],
            statements: main_statements,
            signature: UnresolvedSignature::new()
                .inputs(vec![])
                .outputs(vec![UnresolvedType::FieldElement.mock()]),
        }
        .mock();

        let module = Module {
            symbols: vec![
                SymbolDeclaration {
                    id: "foo",
                    symbol: Symbol::HereFunction(foo),
                }
                .mock(),
                SymbolDeclaration {
                    id: "main",
                    symbol: Symbol::HereFunction(main),
                }
                .mock(),
            ],
            imports: vec![],
        };

        let mut state =
            State::<Bn128Field>::new(vec![((*MODULE_ID).clone(), module)].into_iter().collect());

        let mut checker: Checker<Bn128Field> = new_with_args(HashSet::new(), 0, HashSet::new());
        assert_eq!(
            checker.check_module(&*MODULE_ID, &mut state),
            Err(vec![Error {
                inner: ErrorInner {
                    pos: Some((Position::mock(), Position::mock())),
                    message: "Identifier \"x\" is undefined".into()
                },
                module_id: (*MODULE_ID).clone()
            }])
        );
    }

    #[test]
    fn undeclared_variables() {
        // def foo() -> (field, field):
        //  return 1, 2
        // def main():
        //  a, b = foo()
        //  return 1
        // should fail

        let foo_statements: Vec<StatementNode> = vec![Statement::Return(
            ExpressionList {
                expressions: vec![
                    Expression::IntConstant(1usize.into()).mock(),
                    Expression::IntConstant(2usize.into()).mock(),
                ],
            }
            .mock(),
        )
        .mock()];

        let foo = Function {
            arguments: vec![],
            statements: foo_statements,
            signature: UnresolvedSignature::new().inputs(vec![]).outputs(vec![
                UnresolvedType::FieldElement.mock(),
                UnresolvedType::FieldElement.mock(),
            ]),
        }
        .mock();

        let main_statements: Vec<StatementNode> = vec![
            Statement::MultipleDefinition(
                vec![
                    Assignee::Identifier("a").mock(),
                    Assignee::Identifier("b").mock(),
                ],
                Expression::FunctionCall("foo", None, vec![]).mock(),
            )
            .mock(),
            Statement::Return(
                ExpressionList {
                    expressions: vec![],
                }
                .mock(),
            )
            .mock(),
        ];

        let main = Function {
            arguments: vec![],
            statements: main_statements,
            signature: UnresolvedSignature::new().inputs(vec![]).outputs(vec![]),
        }
        .mock();

        let module = Module {
            symbols: vec![
                SymbolDeclaration {
                    id: "foo",
                    symbol: Symbol::HereFunction(foo),
                }
                .mock(),
                SymbolDeclaration {
                    id: "main",
                    symbol: Symbol::HereFunction(main),
                }
                .mock(),
            ],
            imports: vec![],
        };

        let mut state =
            State::<Bn128Field>::new(vec![((*MODULE_ID).clone(), module)].into_iter().collect());

        let mut checker: Checker<Bn128Field> = new_with_args(HashSet::new(), 0, HashSet::new());
        assert_eq!(
            checker.check_module(&*MODULE_ID, &mut state),
            Err(vec![
                Error {
                    inner: ErrorInner {
                        pos: Some((Position::mock(), Position::mock())),
                        message: "Variable `a` is undeclared".into()
                    },
                    module_id: (*MODULE_ID).clone()
                },
                Error {
                    inner: ErrorInner {
                        pos: Some((Position::mock(), Position::mock())),
                        message: "Variable `b` is undeclared".into()
                    },
                    module_id: (*MODULE_ID).clone()
                }
            ])
        );
    }

    #[test]
    fn assign_to_select() {
        // def foo() -> field:
        //  return 1
        // def main():
        //  field[1] a = [0]
        //  a[0] = foo()
        //  return
        // should succeed

        let foo_statements: Vec<StatementNode> = vec![Statement::Return(
            ExpressionList {
                expressions: vec![Expression::IntConstant(1usize.into()).mock()],
            }
            .mock(),
        )
        .mock()];

        let foo = Function {
            arguments: vec![],
            statements: foo_statements,
            signature: UnresolvedSignature::new()
                .inputs(vec![])
                .outputs(vec![UnresolvedType::FieldElement.mock()]),
        }
        .mock();

        let main_statements: Vec<StatementNode> = vec![
            Statement::Declaration(
                absy::Variable::new(
                    "a",
                    UnresolvedType::array(
                        UnresolvedType::FieldElement.mock(),
                        Expression::IntConstant(1usize.into()).mock(),
                    )
                    .mock(),
                )
                .mock(),
            )
            .mock(),
            Statement::Definition(
                Assignee::Identifier("a").mock(),
                Expression::InlineArray(vec![absy::SpreadOrExpression::Expression(
                    Expression::IntConstant(0usize.into()).mock(),
                )])
                .mock(),
            )
            .mock(),
            Statement::MultipleDefinition(
                vec![Assignee::Select(
                    box Assignee::Identifier("a").mock(),
                    box RangeOrExpression::Expression(
                        absy::Expression::IntConstant(0usize.into()).mock(),
                    ),
                )
                .mock()],
                Expression::FunctionCall("foo", None, vec![]).mock(),
            )
            .mock(),
            Statement::Return(
                ExpressionList {
                    expressions: vec![],
                }
                .mock(),
            )
            .mock(),
        ];

        let main = Function {
            arguments: vec![],
            statements: main_statements,
            signature: UnresolvedSignature::new().inputs(vec![]).outputs(vec![]),
        }
        .mock();

        let module = Module {
            symbols: vec![
                SymbolDeclaration {
                    id: "foo",
                    symbol: Symbol::HereFunction(foo),
                }
                .mock(),
                SymbolDeclaration {
                    id: "main",
                    symbol: Symbol::HereFunction(main),
                }
                .mock(),
            ],
            imports: vec![],
        };

        let mut state =
            State::<Bn128Field>::new(vec![((*MODULE_ID).clone(), module)].into_iter().collect());

        let mut checker: Checker<Bn128Field> = new_with_args(HashSet::new(), 0, HashSet::new());
        assert!(checker.check_module(&*MODULE_ID, &mut state).is_ok());
    }

    #[test]
    fn function_undefined() {
        // def bar():
        //   1 == foo()
        //   return
        // should fail

        let bar_statements: Vec<StatementNode> = vec![
            Statement::Assertion(
                Expression::Eq(
                    box Expression::IntConstant(1usize.into()).mock(),
                    box Expression::FunctionCall("foo", None, vec![]).mock(),
                )
                .mock(),
            )
            .mock(),
            Statement::Return(
                ExpressionList {
                    expressions: vec![],
                }
                .mock(),
            )
            .mock(),
        ];

        let bar = Function {
            arguments: vec![],
            statements: bar_statements,
            signature: UnresolvedSignature::new(),
        }
        .mock();

        let types = HashMap::new();

        let mut checker: Checker<Bn128Field> = new_with_args(HashSet::new(), 0, HashSet::new());
        assert_eq!(
            checker.check_function(bar, &*MODULE_ID, &types),
            Err(vec![ErrorInner {
                pos: Some((Position::mock(), Position::mock())),

                message: "Function definition for function foo with signature () -> _ not found."
                    .into()
            }])
        );
    }

    #[test]
    fn return_undefined() {
        // def bar():
        //   return a, b
        // should fail
        let bar_statements: Vec<StatementNode> = vec![Statement::Return(
            ExpressionList {
                expressions: vec![
                    Expression::Identifier("a").mock(),
                    Expression::Identifier("b").mock(),
                ],
            }
            .mock(),
        )
        .mock()];

        let bar = Function {
            arguments: vec![],
            statements: bar_statements,
            signature: UnresolvedSignature::new().inputs(vec![]).outputs(vec![
                UnresolvedType::FieldElement.mock(),
                UnresolvedType::FieldElement.mock(),
            ]),
        }
        .mock();

        let types = HashMap::new();

        let mut checker: Checker<Bn128Field> = new_with_args(HashSet::new(), 0, HashSet::new());
        assert_eq!(
            checker.check_function(bar, &*MODULE_ID, &types),
            Err(vec![ErrorInner {
                pos: Some((Position::mock(), Position::mock())),
                message: "Identifier \"a\" is undefined".into()
            }])
        );
    }

    #[test]
    fn multi_def() {
        // def foo():
        //   return 1, 2
        // def bar():
        //   field a, field b = foo()
        //   return a + b
        //
        // should pass
        let bar_statements: Vec<StatementNode> = vec![
            Statement::Declaration(
                absy::Variable::new("a", UnresolvedType::FieldElement.mock()).mock(),
            )
            .mock(),
            Statement::Declaration(
                absy::Variable::new("b", UnresolvedType::FieldElement.mock()).mock(),
            )
            .mock(),
            Statement::MultipleDefinition(
                vec![
                    Assignee::Identifier("a").mock(),
                    Assignee::Identifier("b").mock(),
                ],
                Expression::FunctionCall("foo", None, vec![]).mock(),
            )
            .mock(),
            Statement::Return(
                ExpressionList {
                    expressions: vec![Expression::Add(
                        box Expression::Identifier("a").mock(),
                        box Expression::Identifier("b").mock(),
                    )
                    .mock()],
                }
                .mock(),
            )
            .mock(),
        ];

        let bar_statements_checked: Vec<TypedStatement<Bn128Field>> = vec![
            TypedStatement::Declaration(typed_absy::Variable::field_element("a")),
            TypedStatement::Declaration(typed_absy::Variable::field_element("b")),
            TypedStatement::MultipleDefinition(
                vec![
                    typed_absy::Variable::field_element("a").into(),
                    typed_absy::Variable::field_element("b").into(),
                ],
                TypedExpressionList::FunctionCall(
                    DeclarationFunctionKey::with_location((*MODULE_ID).clone(), "foo").signature(
                        DeclarationSignature::new().outputs(vec![
                            DeclarationType::FieldElement,
                            DeclarationType::FieldElement,
                        ]),
                    ),
                    vec![],
                    vec![],
                    vec![Type::FieldElement, Type::FieldElement],
                ),
            ),
            TypedStatement::Return(vec![FieldElementExpression::Add(
                box FieldElementExpression::Identifier("a".into()),
                box FieldElementExpression::Identifier("b".into()),
            )
            .into()]),
        ];

        let foo = DeclarationFunctionKey {
            module: (*MODULE_ID).clone(),
            id: "foo",
            signature: DeclarationSignature::new().inputs(vec![]).outputs(vec![
                DeclarationType::FieldElement,
                DeclarationType::FieldElement,
            ]),
        };

        let mut functions = HashSet::new();
        functions.insert(foo);

        let bar = Function {
            arguments: vec![],
            statements: bar_statements,
            signature: UnresolvedSignature::new()
                .inputs(vec![])
                .outputs(vec![UnresolvedType::FieldElement.mock()]),
        }
        .mock();

        let bar_checked = TypedFunction {
            arguments: vec![],
            statements: bar_statements_checked,
            signature: DeclarationSignature::new()
                .inputs(vec![])
                .outputs(vec![DeclarationType::FieldElement]),
        };

        let types = HashMap::new();

        let mut checker: Checker<Bn128Field> = new_with_args(HashSet::new(), 0, functions);
        assert_eq!(
            checker.check_function(bar, &*MODULE_ID, &types),
            Ok(bar_checked)
        );
    }

    #[test]
    fn duplicate_argument_name() {
        // def main(field a, bool a):
        //     return

        // should fail

        let mut f = function0();
        f.value.arguments = vec![
            absy::Parameter::private(
                absy::Variable::new("a", UnresolvedType::FieldElement.mock()).mock(),
            )
            .mock(),
            absy::Parameter::private(
                absy::Variable::new("a", UnresolvedType::Boolean.mock()).mock(),
            )
            .mock(),
        ];
        f.value.signature = UnresolvedSignature::new().inputs(vec![
            UnresolvedType::FieldElement.mock(),
            UnresolvedType::Boolean.mock(),
        ]);

        let mut checker: Checker<Bn128Field> = new_with_args(HashSet::new(), 0, HashSet::new());
        assert_eq!(
            checker
                .check_function(f, &*MODULE_ID, &HashMap::new())
                .unwrap_err()[0]
                .message,
            "Duplicate name in function definition: `a` was previously declared as an argument or a generic constant"
        );
    }

    #[test]
    fn duplicate_main_function() {
        // def main(a):
        //   return 1
        // def main():
        //   return 1
        //
        // should fail
        let main1_statements: Vec<StatementNode> = vec![Statement::Return(
            ExpressionList {
                expressions: vec![Expression::IntConstant(1usize.into()).mock()],
            }
            .mock(),
        )
        .mock()];

        let main1_arguments = vec![crate::absy::Parameter {
            id: absy::Variable::new("a", UnresolvedType::FieldElement.mock()).mock(),
            private: false,
        }
        .mock()];

        let main2_statements: Vec<StatementNode> = vec![Statement::Return(
            ExpressionList {
                expressions: vec![Expression::IntConstant(1usize.into()).mock()],
            }
            .mock(),
        )
        .mock()];

        let main2_arguments = vec![];

        let main1 = Function {
            arguments: main1_arguments,
            statements: main1_statements,
            signature: UnresolvedSignature::new()
                .inputs(vec![UnresolvedType::FieldElement.mock()])
                .outputs(vec![UnresolvedType::FieldElement.mock()]),
        }
        .mock();

        let main2 = Function {
            arguments: main2_arguments,
            statements: main2_statements,
            signature: UnresolvedSignature::new()
                .inputs(vec![])
                .outputs(vec![UnresolvedType::FieldElement.mock()]),
        }
        .mock();

        let symbols = vec![
            SymbolDeclaration {
                id: "main",
                symbol: Symbol::HereFunction(main1),
            }
            .mock(),
            SymbolDeclaration {
                id: "main",
                symbol: Symbol::HereFunction(main2),
            }
            .mock(),
        ];

        let main_module = Module {
            symbols,
            imports: vec![],
        };

        let program = Program {
            modules: vec![((*MODULE_ID).clone(), main_module)]
                .into_iter()
                .collect(),
            main: (*MODULE_ID).clone(),
        };

        let mut checker: Checker<Bn128Field> = Checker::new();
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

    #[test]
    fn shadowing_with_same_type() {
        //   field a
        //	 field a
        //
        // should fail

        let types = HashMap::new();
        let mut checker: Checker<Bn128Field> = Checker::new();
        let _: Result<TypedStatement<Bn128Field>, Vec<ErrorInner>> = checker.check_statement(
            Statement::Declaration(
                absy::Variable::new("a", UnresolvedType::FieldElement.mock()).mock(),
            )
            .mock(),
            &*MODULE_ID,
            &types,
        );
        let s2_checked: Result<TypedStatement<Bn128Field>, Vec<ErrorInner>> = checker
            .check_statement(
                Statement::Declaration(
                    absy::Variable::new("a", UnresolvedType::FieldElement.mock()).mock(),
                )
                .mock(),
                &*MODULE_ID,
                &types,
            );
        assert_eq!(
            s2_checked,
            Err(vec![ErrorInner {
                pos: Some((Position::mock(), Position::mock())),
                message: "Duplicate declaration for variable named a".into()
            }])
        );
    }

    #[test]
    fn shadowing_with_different_type() {
        //   field a
        //	 bool a
        //
        // should fail

        let types = HashMap::new();

        let mut checker: Checker<Bn128Field> = Checker::new();
        let _: Result<TypedStatement<Bn128Field>, Vec<ErrorInner>> = checker.check_statement(
            Statement::Declaration(
                absy::Variable::new("a", UnresolvedType::FieldElement.mock()).mock(),
            )
            .mock(),
            &*MODULE_ID,
            &types,
        );
        let s2_checked: Result<TypedStatement<Bn128Field>, Vec<ErrorInner>> = checker
            .check_statement(
                Statement::Declaration(
                    absy::Variable::new("a", UnresolvedType::Boolean.mock()).mock(),
                )
                .mock(),
                &*MODULE_ID,
                &types,
            );
        assert_eq!(
            s2_checked,
            Err(vec![ErrorInner {
                pos: Some((Position::mock(), Position::mock())),
                message: "Duplicate declaration for variable named a".into()
            }])
        );
    }

    mod structs {
        use super::*;
        use crate::typed_absy::types::StructMember;

        /// solver function to create a module at location "" with a single symbol `Foo { foo: field }`
        fn create_module_with_foo(
            s: StructDefinition<'static>,
        ) -> (Checker<Bn128Field>, State<Bn128Field>) {
            let module: Module = Module {
                imports: vec![],
                symbols: vec![SymbolDeclaration {
                    id: "Foo",
                    symbol: Symbol::HereType(s.mock()),
                }
                .mock()],
            };

            let mut state = State::<Bn128Field>::new(
                vec![((*MODULE_ID).clone(), module)].into_iter().collect(),
            );

            let mut checker: Checker<Bn128Field> = Checker::new();

            checker.check_module(&*MODULE_ID, &mut state).unwrap();

            (checker, state)
        }

        /// tests about declaring a type
        mod declaration {
            use super::*;

            #[test]
            fn empty_def() {
                // an empty struct should be allowed to be defined
                let types = HashMap::new();
                let declaration: StructDefinitionNode = StructDefinition { fields: vec![] }.mock();

                let expected_type = DeclarationType::Struct(DeclarationStructType::new(
                    "".into(),
                    "Foo".into(),
                    vec![],
                ));

                assert_eq!(
                    Checker::<Bn128Field>::new().check_struct_type_declaration(
                        "Foo".into(),
                        declaration,
                        &*MODULE_ID,
                        &types
                    ),
                    Ok(expected_type)
                );
            }

            #[test]
            fn valid_def() {
                // a valid struct should be allowed to be defined
                let types = HashMap::new();
                let declaration: StructDefinitionNode = StructDefinition {
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

                let expected_type = DeclarationType::Struct(DeclarationStructType::new(
                    "".into(),
                    "Foo".into(),
                    vec![
                        DeclarationStructMember::new("foo".into(), DeclarationType::FieldElement),
                        DeclarationStructMember::new("bar".into(), DeclarationType::Boolean),
                    ],
                ));

                assert_eq!(
                    Checker::<Bn128Field>::new().check_struct_type_declaration(
                        "Foo".into(),
                        declaration,
                        &*MODULE_ID,
                        &types
                    ),
                    Ok(expected_type)
                );
            }

            #[test]
            fn duplicate_member_def() {
                // definition of a struct with a duplicate member should be rejected
                let types = HashMap::new();

                let declaration: StructDefinitionNode = StructDefinition {
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
                    Checker::<Bn128Field>::new()
                        .check_struct_type_declaration(
                            "Foo".into(),
                            declaration,
                            &*MODULE_ID,
                            &types
                        )
                        .unwrap_err()[0]
                        .message,
                    "Duplicate key foo in struct definition"
                );
            }

            #[test]
            fn recursive() {
                // a struct wrapping another struct should be allowed to be defined

                // struct Foo = { foo: field }
                // struct Bar = { foo: Foo }

                let module: Module = Module {
                    imports: vec![],
                    symbols: vec![
                        SymbolDeclaration {
                            id: "Foo",
                            symbol: Symbol::HereType(
                                StructDefinition {
                                    fields: vec![StructDefinitionField {
                                        id: "foo",
                                        ty: UnresolvedType::FieldElement.mock(),
                                    }
                                    .mock()],
                                }
                                .mock(),
                            ),
                        }
                        .mock(),
                        SymbolDeclaration {
                            id: "Bar",
                            symbol: Symbol::HereType(
                                StructDefinition {
                                    fields: vec![StructDefinitionField {
                                        id: "foo",
                                        ty: UnresolvedType::User("Foo".into()).mock(),
                                    }
                                    .mock()],
                                }
                                .mock(),
                            ),
                        }
                        .mock(),
                    ],
                };

                let mut state = State::<Bn128Field>::new(
                    vec![((*MODULE_ID).clone(), module)].into_iter().collect(),
                );

                assert!(Checker::new().check_module(&*MODULE_ID, &mut state).is_ok());
                assert_eq!(
                    state
                        .types
                        .get(&*MODULE_ID)
                        .unwrap()
                        .get(&"Bar".to_string())
                        .unwrap(),
                    &DeclarationType::Struct(DeclarationStructType::new(
                        (*MODULE_ID).clone(),
                        "Bar".into(),
                        vec![DeclarationStructMember::new(
                            "foo".into(),
                            DeclarationType::Struct(DeclarationStructType::new(
                                (*MODULE_ID).clone(),
                                "Foo".into(),
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

                // struct Bar = { foo: Foo }

                let module: Module = Module {
                    imports: vec![],
                    symbols: vec![SymbolDeclaration {
                        id: "Bar",
                        symbol: Symbol::HereType(
                            StructDefinition {
                                fields: vec![StructDefinitionField {
                                    id: "foo",
                                    ty: UnresolvedType::User("Foo".into()).mock(),
                                }
                                .mock()],
                            }
                            .mock(),
                        ),
                    }
                    .mock()],
                };

                let mut state = State::<Bn128Field>::new(
                    vec![((*MODULE_ID).clone(), module)].into_iter().collect(),
                );

                assert!(Checker::new()
                    .check_module(&*MODULE_ID, &mut state)
                    .is_err());
            }

            #[test]
            fn self_referential() {
                // a struct wrapping itself should be rejected

                // struct Foo = { foo: Foo }

                let module: Module = Module {
                    imports: vec![],
                    symbols: vec![SymbolDeclaration {
                        id: "Foo",
                        symbol: Symbol::HereType(
                            StructDefinition {
                                fields: vec![StructDefinitionField {
                                    id: "foo",
                                    ty: UnresolvedType::User("Foo".into()).mock(),
                                }
                                .mock()],
                            }
                            .mock(),
                        ),
                    }
                    .mock()],
                };

                let mut state = State::<Bn128Field>::new(
                    vec![((*MODULE_ID).clone(), module)].into_iter().collect(),
                );

                assert!(Checker::new()
                    .check_module(&*MODULE_ID, &mut state)
                    .is_err());
            }

            #[test]
            fn cyclic() {
                // A wrapping B wrapping A should be rejected

                // struct Foo = { bar: Bar }
                // struct Bar = { foo: Foo }

                let module: Module = Module {
                    imports: vec![],
                    symbols: vec![
                        SymbolDeclaration {
                            id: "Foo",
                            symbol: Symbol::HereType(
                                StructDefinition {
                                    fields: vec![StructDefinitionField {
                                        id: "bar",
                                        ty: UnresolvedType::User("Bar".into()).mock(),
                                    }
                                    .mock()],
                                }
                                .mock(),
                            ),
                        }
                        .mock(),
                        SymbolDeclaration {
                            id: "Bar",
                            symbol: Symbol::HereType(
                                StructDefinition {
                                    fields: vec![StructDefinitionField {
                                        id: "foo",
                                        ty: UnresolvedType::User("Foo".into()).mock(),
                                    }
                                    .mock()],
                                }
                                .mock(),
                            ),
                        }
                        .mock(),
                    ],
                };

                let mut state = State::<Bn128Field>::new(
                    vec![((*MODULE_ID).clone(), module)].into_iter().collect(),
                );

                assert!(Checker::new()
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
                // Foo { foo: field }
                // Foo

                // an undefined type cannot be checked
                // Bar

                let (mut checker, state) = create_module_with_foo(StructDefinition {
                    fields: vec![StructDefinitionField {
                        id: "foo",
                        ty: UnresolvedType::FieldElement.mock(),
                    }
                    .mock()],
                });

                assert_eq!(
                    checker.check_type(
                        UnresolvedType::User("Foo".into()).mock(),
                        &*MODULE_ID,
                        &state.types
                    ),
                    Ok(Type::Struct(StructType::new(
                        "".into(),
                        "Foo".into(),
                        vec![StructMember::new("foo".into(), Type::FieldElement)]
                    )))
                );

                assert_eq!(
                    checker
                        .check_type(
                            UnresolvedType::User("Bar".into()).mock(),
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

                // struct Foo = { foo: field }
                // Foo { foo: 42 }.foo

                let (mut checker, state) = create_module_with_foo(StructDefinition {
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
                    Ok(FieldElementExpression::Member(
                        box StructExpressionInner::Value(vec![FieldElementExpression::Number(
                            Bn128Field::from(42u32)
                        )
                        .into()])
                        .annotate(StructType::new(
                            "".into(),
                            "Foo".into(),
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

                // struct Foo = { foo: field }
                // Foo { foo: 42 }.bar

                let (mut checker, state) = create_module_with_foo(StructDefinition {
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
                    "Undefined type Bar"
                );
            }

            #[test]
            fn valid() {
                // a A value can be defined with members ordered as in the declaration of A

                // struct Foo = { foo: field, bar: bool }
                // Foo foo = Foo { foo: 42, bar: true }

                let (mut checker, state) = create_module_with_foo(StructDefinition {
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

                // struct Foo = { foo: field, bar: bool }
                // Foo foo = Foo { bar: true, foo: 42 }

                let (mut checker, state) = create_module_with_foo(StructDefinition {
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

                // struct Foo = { foo: field, bar: bool }
                // Foo foo = Foo { foo: 42 }

                let (mut checker, state) = create_module_with_foo(StructDefinition {
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

                // struct Foo = { foo: field, bar: bool }
                // Foo { foo: 42, baz: bool } // error
                // Foo { foo: 42, baz: 42 } // error

                let (mut checker, state) = create_module_with_foo(StructDefinition {
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
            // def foo(field a) -> field:
            //     return 0

            // def foo(u32 a) -> field:
            //     return 0

            // def main() -> field:
            //     return foo(0)

            // should fail

            let mut foo_field = function0();

            foo_field.value.arguments = vec![absy::Parameter::private(
                absy::Variable {
                    id: "a",
                    _type: UnresolvedType::FieldElement.mock(),
                }
                .mock(),
            )
            .mock()];
            foo_field.value.statements = vec![Statement::Return(
                ExpressionList {
                    expressions: vec![Expression::IntConstant(0usize.into()).mock()],
                }
                .mock(),
            )
            .mock()];
            foo_field.value.signature = UnresolvedSignature::new()
                .inputs(vec![UnresolvedType::FieldElement.mock()])
                .outputs(vec![UnresolvedType::FieldElement.mock()]);

            let mut foo_u32 = function0();

            foo_u32.value.arguments = vec![absy::Parameter::private(
                absy::Variable {
                    id: "a",
                    _type: UnresolvedType::Uint(32).mock(),
                }
                .mock(),
            )
            .mock()];
            foo_u32.value.statements = vec![Statement::Return(
                ExpressionList {
                    expressions: vec![Expression::IntConstant(0usize.into()).mock()],
                }
                .mock(),
            )
            .mock()];
            foo_u32.value.signature = UnresolvedSignature::new()
                .inputs(vec![UnresolvedType::Uint(32).mock()])
                .outputs(vec![UnresolvedType::FieldElement.mock()]);

            let mut main = function0();

            main.value.statements = vec![Statement::Return(
                ExpressionList {
                    expressions: vec![Expression::FunctionCall(
                        "foo",
                        None,
                        vec![Expression::IntConstant(0usize.into()).mock()],
                    )
                    .mock()],
                }
                .mock(),
            )
            .mock()];
            main.value.signature =
                UnresolvedSignature::new().outputs(vec![UnresolvedType::FieldElement.mock()]);

            let m = Module::with_symbols(vec![
                absy::SymbolDeclaration {
                    id: "foo",
                    symbol: Symbol::HereFunction(foo_field),
                }
                .mock(),
                absy::SymbolDeclaration {
                    id: "foo",
                    symbol: Symbol::HereFunction(foo_u32),
                }
                .mock(),
                absy::SymbolDeclaration {
                    id: "main",
                    symbol: Symbol::HereFunction(main),
                }
                .mock(),
            ]);

            let p = Program {
                main: "".into(),
                modules: vec![("".into(), m)].into_iter().collect(),
            };

            let errors = Checker::<Bn128Field>::new().check_program(p).unwrap_err();

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
            // a = 42
            let a = Assignee::Identifier("a").mock();

            let types = HashMap::new();

            let mut checker: Checker<Bn128Field> = Checker::new();

            checker
                .check_statement(
                    Statement::Declaration(
                        absy::Variable::new("a", UnresolvedType::FieldElement.mock()).mock(),
                    )
                    .mock(),
                    &*MODULE_ID,
                    &types,
                )
                .unwrap();

            assert_eq!(
                checker.check_assignee(a, &*MODULE_ID, &types),
                Ok(TypedAssignee::Identifier(
                    typed_absy::Variable::field_element("a")
                ))
            );
        }

        #[test]
        fn array_element() {
            // field[33] a
            // a[2] = 42
            let a = Assignee::Select(
                box Assignee::Identifier("a").mock(),
                box RangeOrExpression::Expression(Expression::IntConstant(2usize.into()).mock()),
            )
            .mock();

            let types = HashMap::new();

            let mut checker: Checker<Bn128Field> = Checker::new();
            checker
                .check_statement(
                    Statement::Declaration(
                        absy::Variable::new(
                            "a",
                            UnresolvedType::array(
                                UnresolvedType::FieldElement.mock(),
                                Expression::IntConstant(33usize.into()).mock(),
                            )
                            .mock(),
                        )
                        .mock(),
                    )
                    .mock(),
                    &*MODULE_ID,
                    &types,
                )
                .unwrap();

            assert_eq!(
                checker.check_assignee(a, &*MODULE_ID, &types),
                Ok(TypedAssignee::Select(
                    box TypedAssignee::Identifier(typed_absy::Variable::field_array(
                        "a",
                        33u32.into()
                    )),
                    box 2u32.into()
                ))
            );
        }

        #[test]
        fn array_of_array_element() {
            // field[33][42] a
            // a[1][2]
            let a: AssigneeNode = Assignee::Select(
                box Assignee::Select(
                    box Assignee::Identifier("a").mock(),
                    box RangeOrExpression::Expression(
                        Expression::IntConstant(1usize.into()).mock(),
                    ),
                )
                .mock(),
                box RangeOrExpression::Expression(Expression::IntConstant(2usize.into()).mock()),
            )
            .mock();

            let types = HashMap::new();

            let mut checker: Checker<Bn128Field> = Checker::new();
            checker
                .check_statement(
                    Statement::Declaration(
                        absy::Variable::new(
                            "a",
                            UnresolvedType::array(
                                UnresolvedType::array(
                                    UnresolvedType::FieldElement.mock(),
                                    Expression::IntConstant(33usize.into()).mock(),
                                )
                                .mock(),
                                Expression::IntConstant(42usize.into()).mock(),
                            )
                            .mock(),
                        )
                        .mock(),
                    )
                    .mock(),
                    &*MODULE_ID,
                    &types,
                )
                .unwrap();

            assert_eq!(
                checker.check_assignee(a, &*MODULE_ID, &types),
                Ok(TypedAssignee::Select(
                    box TypedAssignee::Select(
                        box TypedAssignee::Identifier(typed_absy::Variable::array(
                            "a",
                            Type::array((Type::FieldElement, 33u32)),
                            42u32,
                        )),
                        box 1u32.into()
                    ),
                    box 2u32.into()
                ))
            );
        }
    }
}
