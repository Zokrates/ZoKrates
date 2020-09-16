//! Module containing structs and enums to represent a program.
//!
//! @file absy.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

pub mod abi;
pub mod folder;
pub mod identifier;

mod parameter;
pub mod types;
mod uint;
mod variable;

pub use self::identifier::CoreIdentifier;
pub use self::parameter::Parameter;
use self::types::ArrayType;
pub use self::types::{Signature, StructType, Type, UBitwidth};
use num_bigint::BigUint;

pub use self::variable::Variable;
use std::path::PathBuf;
pub use typed_absy::uint::{bitwidth, UExpression, UExpressionInner, UMetadata};

use crate::typed_absy::types::{FunctionKey, MemberId};
use embed::FlatEmbed;
use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};
use std::fmt;
use zokrates_field::Field;

pub use self::folder::Folder;
use typed_absy::abi::{Abi, AbiInput};

pub use self::identifier::Identifier;

/// An identifier for a `TypedModule`. Typically a path or uri.
pub type TypedModuleId = PathBuf;

/// A collection of `TypedModule`s
pub type TypedModules<'ast, T> = HashMap<TypedModuleId, TypedModule<'ast, T>>;

/// A collection of `TypedFunctionSymbol`s
/// # Remarks
/// * It is the role of the semantic checker to make sure there are no duplicates for a given `FunctionKey`
///   in a given `TypedModule`, hence the use of a HashMap
pub type TypedFunctionSymbols<'ast, T> = HashMap<FunctionKey<'ast>, TypedFunctionSymbol<'ast, T>>;

/// A typed program as a collection of modules, one of them being the main
#[derive(PartialEq, Debug, Clone)]
pub struct TypedProgram<'ast, T> {
    pub modules: TypedModules<'ast, T>,
    pub main: TypedModuleId,
}

impl<'ast, T: Field> TypedProgram<'ast, T> {
    pub fn abi(&self) -> Abi {
        let main = self.modules[&self.main]
            .functions
            .iter()
            .find(|(id, _)| id.id == "main")
            .unwrap()
            .1;
        let main = match main {
            TypedFunctionSymbol::Here(main) => main,
            _ => unreachable!(),
        };

        Abi {
            inputs: main
                .arguments
                .clone()
                .into_iter()
                .map(|p| AbiInput {
                    public: !p.private,
                    name: p.id.id.to_string(),
                    ty: p.id._type,
                })
                .collect(),
            outputs: main.signature.outputs.clone(),
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for TypedProgram<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (module_id, module) in &self.modules {
            writeln!(
                f,
                "| {}: |{}",
                module_id.display(),
                if *module_id == self.main {
                    "<---- main"
                } else {
                    ""
                }
            )?;
            writeln!(f, "{}", "-".repeat(100))?;
            writeln!(f, "{}", module)?;
            writeln!(f, "{}", "-".repeat(100))?;
            writeln!(f, "")?;
        }
        write!(f, "")
    }
}

/// A typed program as a collection of functions. Types have been resolved during semantic checking.
#[derive(PartialEq, Clone)]
pub struct TypedModule<'ast, T> {
    /// Functions of the program
    pub functions: TypedFunctionSymbols<'ast, T>,
}

#[derive(Clone, PartialEq)]
pub enum TypedFunctionSymbol<'ast, T> {
    Here(TypedFunction<'ast, T>),
    There(FunctionKey<'ast>, TypedModuleId),
    Flat(FlatEmbed),
}

// this should be deriveable but it seems like the bounds are not infered correctly
impl<'ast, T: fmt::Debug> fmt::Debug for TypedFunctionSymbol<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TypedFunctionSymbol::Here(s) => write!(f, "Here({:?})", s),
            TypedFunctionSymbol::There(key, module) => write!(f, "There({:?}, {:?})", key, module),
            TypedFunctionSymbol::Flat(s) => write!(f, "Flat({:?})", s),
        }
    }
}

impl<'ast, T: Field> TypedFunctionSymbol<'ast, T> {
    pub fn signature<'a>(&'a self, modules: &'a TypedModules<'ast, T>) -> Signature {
        match self {
            TypedFunctionSymbol::Here(f) => f.signature.clone(),
            TypedFunctionSymbol::There(key, module_id) => modules
                .get(module_id)
                .unwrap()
                .functions
                .get(key)
                .unwrap()
                .signature(&modules)
                .clone(),
            TypedFunctionSymbol::Flat(flat_fun) => flat_fun.signature().try_into().unwrap(),
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for TypedModule<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let res = self
            .functions
            .iter()
            .map(|(key, symbol)| match symbol {
                TypedFunctionSymbol::Here(ref function) => format!("def {}{}", key.id, function),
                TypedFunctionSymbol::There(ref fun_key, ref module_id) => format!(
                    "import {} from \"{}\" as {} // with signature {}",
                    fun_key.id,
                    module_id.display(),
                    key.id,
                    key.signature
                ),
                TypedFunctionSymbol::Flat(ref flat_fun) => {
                    format!("def {}{}:\n\t// hidden", key.id, flat_fun.signature())
                }
            })
            .collect::<Vec<_>>();
        write!(f, "{}", res.join("\n"))
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for TypedModule<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "module(\n\tfunctions:\n\t\t{:?}\n)",
            self.functions
                .iter()
                .map(|x| format!("{:?}", x))
                .collect::<Vec<_>>()
                .join("\n\t\t")
        )
    }
}

/// A typed function
#[derive(Clone, PartialEq)]
pub struct TypedFunction<'ast, T> {
    /// Arguments of the function
    pub arguments: Vec<Parameter<'ast>>,
    /// Vector of statements that are executed when running the function
    pub statements: Vec<TypedStatement<'ast, T>>,
    /// function signature
    pub signature: Signature,
}

impl<'ast, T: fmt::Display> fmt::Display for TypedFunction<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "({})",
            self.arguments
                .iter()
                .map(|x| format!("{}", x))
                .collect::<Vec<_>>()
                .join(", "),
        )?;

        write!(
            f,
            "{}:",
            match self.signature.outputs.len() {
                0 => "".into(),
                1 => format!(" -> {}", self.signature.outputs[0]),
                _ => format!(
                    " -> ({})",
                    self.signature
                        .outputs
                        .iter()
                        .map(|x| format!("{}", x))
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
            }
        )?;

        writeln!(f, "")?;

        for s in &self.statements {
            s.fmt_indented(f, 1)?;
            writeln!(f, "")?;
        }

        Ok(())
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for TypedFunction<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "TypedFunction(arguments: {:?}, ...):\n{}",
            self.arguments,
            self.statements
                .iter()
                .map(|x| format!("\t{:?}", x))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

/// Something we can assign to.
#[derive(Clone, PartialEq, Hash, Eq)]
pub enum TypedAssignee<'ast, T> {
    Identifier(Variable<'ast>),
    Select(Box<TypedAssignee<'ast, T>>, Box<UExpression<'ast, T>>),
    Member(Box<TypedAssignee<'ast, T>>, MemberId),
}

impl<'ast, T: Clone> Typed<'ast, T> for TypedAssignee<'ast, T> {
    fn get_type(&self) -> Type {
        match *self {
            TypedAssignee::Identifier(ref v) => v.get_type(),
            TypedAssignee::Select(ref a, _) => {
                let a_type = a.get_type();
                match a_type {
                    Type::Array(t) => *t.ty,
                    _ => unreachable!("an array element should only be defined over arrays"),
                }
            }
            TypedAssignee::Member(ref s, ref m) => {
                let s_type = s.get_type();
                match s_type {
                    Type::Struct(members) => *members
                        .iter()
                        .find(|member| member.id == *m)
                        .unwrap()
                        .ty
                        .clone(),
                    _ => unreachable!("a struct access should only be defined over structs"),
                }
            }
        }
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for TypedAssignee<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedAssignee::Identifier(ref s) => write!(f, "{:?}", s.id),
            TypedAssignee::Select(ref a, ref e) => write!(f, "Select({:?}, {:?})", a, e),
            TypedAssignee::Member(ref s, ref m) => write!(f, "Member({:?}, {:?})", s, m),
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for TypedAssignee<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedAssignee::Identifier(ref s) => write!(f, "{}", s.id),
            TypedAssignee::Select(ref a, ref e) => write!(f, "{}[{}]", a, e),
            TypedAssignee::Member(ref s, ref m) => write!(f, "{}.{}", s, m),
        }
    }
}

/// A statement in a `TypedFunction`
#[derive(Clone, PartialEq, Hash, Eq)]
pub enum TypedStatement<'ast, T> {
    Return(Vec<TypedExpression<'ast, T>>),
    Definition(TypedAssignee<'ast, T>, TypedExpression<'ast, T>),
    Declaration(Variable<'ast>),
    Assertion(BooleanExpression<'ast, T>),
    For(
        Variable<'ast>,
        UExpression<'ast, T>,
        UExpression<'ast, T>,
        Vec<TypedStatement<'ast, T>>,
    ),
    MultipleDefinition(Vec<Variable<'ast>>, TypedExpressionList<'ast, T>),
}

impl<'ast, T: fmt::Debug> fmt::Debug for TypedStatement<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedStatement::Return(ref exprs) => {
                write!(f, "Return(")?;
                for (i, expr) in exprs.iter().enumerate() {
                    write!(f, "{:?}", expr)?;
                    if i < exprs.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            TypedStatement::Declaration(ref var) => write!(f, "({:?})", var),
            TypedStatement::Definition(ref lhs, ref rhs) => {
                write!(f, "Definition({:?}, {:?})", lhs, rhs)
            }
            TypedStatement::Assertion(ref e) => write!(f, "Assertion({:?})", e),
            TypedStatement::For(ref var, ref start, ref stop, ref list) => {
                write!(f, "for {:?} in {:?}..{:?} do\n", var, start, stop)?;
                for l in list {
                    write!(f, "\t\t{:?}\n", l)?;
                }
                write!(f, "\tendfor")
            }
            TypedStatement::MultipleDefinition(ref lhs, ref rhs) => {
                write!(f, "MultipleDefinition({:?}, {:?})", lhs, rhs)
            }
        }
    }
}

impl<'ast, T: fmt::Display> TypedStatement<'ast, T> {
    fn fmt_indented(&self, f: &mut fmt::Formatter, depth: usize) -> fmt::Result {
        match self {
            TypedStatement::For(variable, from, to, statements) => {
                write!(f, "{}", "\t".repeat(depth))?;
                writeln!(f, "for {} in {}..{} do", variable, from, to)?;
                for s in statements {
                    s.fmt_indented(f, depth + 1)?;
                    writeln!(f, "")?;
                }
                writeln!(f, "{}endfor", "\t".repeat(depth))
            }
            s => write!(f, "{}{}", "\t".repeat(depth), s),
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for TypedStatement<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedStatement::Return(ref exprs) => {
                write!(f, "return ")?;
                for (i, expr) in exprs.iter().enumerate() {
                    write!(f, "{}", expr)?;
                    if i < exprs.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "")
            }
            TypedStatement::Declaration(ref var) => write!(f, "{}", var),
            TypedStatement::Definition(ref lhs, ref rhs) => write!(f, "{} = {}", lhs, rhs),
            TypedStatement::Assertion(ref e) => write!(f, "assert({})", e),
            TypedStatement::For(ref var, ref start, ref stop, ref list) => {
                write!(f, "for {} in {}..{} do\n", var, start, stop)?;
                for l in list {
                    write!(f, "\t\t{}\n", l)?;
                }
                write!(f, "\tendfor")
            }
            TypedStatement::MultipleDefinition(ref ids, ref rhs) => {
                for (i, id) in ids.iter().enumerate() {
                    write!(f, "{}", id)?;
                    if i < ids.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, " = {}", rhs)
            }
        }
    }
}

pub trait Typed<'ast, T> {
    fn get_type(&self) -> Type;
}

/// A typed expression
#[derive(Clone, PartialEq, Hash, Eq)]
pub enum TypedExpression<'ast, T> {
    Boolean(BooleanExpression<'ast, T>),
    FieldElement(FieldElementExpression<'ast, T>),
    Uint(UExpression<'ast, T>),
    Array(ArrayExpression<'ast, T>),
    Struct(StructExpression<'ast, T>),
    Int(IntExpression<'ast, T>),
}

impl<'ast, T: Field> TypedExpression<'ast, T> {
    // return two TypedExpression, replacing IntExpression by FieldElement or Uint to try to align the two types.
    // Post condition is that (lhs, rhs) cannot be made equal by further removing IntExpressions
    pub fn align_without_integers(
        lhs: Self,
        rhs: Self,
    ) -> Result<(TypedExpression<'ast, T>, TypedExpression<'ast, T>), String> {
        use self::TypedExpression::*;
        match (lhs, rhs) {
            (Int(lhs), FieldElement(rhs)) => Ok((
                FieldElementExpression::try_from_int(lhs)?.into(),
                FieldElement(rhs),
            )),
            (FieldElement(lhs), Int(rhs)) => Ok((
                FieldElement(lhs),
                FieldElementExpression::try_from_int(rhs)?.into(),
            )),
            (Int(lhs), Uint(rhs)) => Ok((
                UExpression::try_from_int(lhs, rhs.bitwidth())?.into(),
                Uint(rhs),
            )),
            (Uint(lhs), Int(rhs)) => {
                let bitwidth = lhs.bitwidth();
                Ok((Uint(lhs), UExpression::try_from_int(rhs, bitwidth)?.into()))
            }
            (lhs, rhs) => Ok((lhs, rhs)),
        }
    }

    pub fn align_to_type(e: Self, ty: Type) -> Result<Self, String> {
        use self::TypedExpression::*;
        match (e, ty) {
            (Int(e), Type::FieldElement) => Ok(FieldElementExpression::try_from_int(e)?.into()),
            (Int(e), Type::Uint(bitwidth)) => Ok(UExpression::try_from_int(e, bitwidth)?.into()),
            (Array(a), Type::Array(array_ty)) => Ok(ArrayExpression::try_from_int(a, array_ty)
                .map_err(|_| String::from("align array to type"))?
                .into()),
            (e, _) => Ok(e),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum IntExpression<'ast, T> {
    Value(BigUint),
    Add(Box<IntExpression<'ast, T>>, Box<IntExpression<'ast, T>>),
    Sub(Box<IntExpression<'ast, T>>, Box<IntExpression<'ast, T>>),
    Mult(Box<IntExpression<'ast, T>>, Box<IntExpression<'ast, T>>),
    Div(Box<IntExpression<'ast, T>>, Box<IntExpression<'ast, T>>),
    Pow(Box<IntExpression<'ast, T>>, Box<IntExpression<'ast, T>>),
    IfElse(
        Box<BooleanExpression<'ast, T>>,
        Box<IntExpression<'ast, T>>,
        Box<IntExpression<'ast, T>>,
    ),
    Select(Box<ArrayExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    Xor(Box<IntExpression<'ast, T>>, Box<IntExpression<'ast, T>>),
    And(Box<IntExpression<'ast, T>>, Box<IntExpression<'ast, T>>),
    Or(Box<IntExpression<'ast, T>>, Box<IntExpression<'ast, T>>),
    Not(Box<IntExpression<'ast, T>>),
    LeftShift(
        Box<IntExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    RightShift(
        Box<IntExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
}

impl<'ast, T: fmt::Display> fmt::Display for IntExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            IntExpression::Value(ref v) => write!(f, "{}", v),
            IntExpression::Div(ref lhs, ref rhs) => write!(f, "({} / {})", lhs, rhs),
            IntExpression::Pow(ref lhs, ref rhs) => write!(f, "({} ** {})", lhs, rhs),
            IntExpression::Select(ref id, ref index) => write!(f, "{}[{}]", id, index),
            IntExpression::Add(ref lhs, ref rhs) => write!(f, "({} + {})", lhs, rhs),
            IntExpression::And(ref lhs, ref rhs) => write!(f, "({} & {})", lhs, rhs),
            IntExpression::Or(ref lhs, ref rhs) => write!(f, "({} | {})", lhs, rhs),
            IntExpression::Xor(ref lhs, ref rhs) => write!(f, "({} ^ {})", lhs, rhs),
            IntExpression::Sub(ref lhs, ref rhs) => write!(f, "({} - {})", lhs, rhs),
            IntExpression::Mult(ref lhs, ref rhs) => write!(f, "({} * {})", lhs, rhs),
            IntExpression::RightShift(ref e, ref by) => write!(f, "({} >> {})", e, by),
            IntExpression::LeftShift(ref e, ref by) => write!(f, "({} << {})", e, by),
            IntExpression::Not(ref e) => write!(f, "!{}", e),
            IntExpression::IfElse(ref condition, ref consequent, ref alternative) => write!(
                f,
                "if {} then {} else {} fi",
                condition, consequent, alternative
            ),
        }
    }
}

// impl<'ast, T: fmt::Debug> fmt::Debug for IntExpression<'ast, T> {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         unimplemented!()
//     }
// }

impl<'ast, T> From<BooleanExpression<'ast, T>> for TypedExpression<'ast, T> {
    fn from(e: BooleanExpression<'ast, T>) -> TypedExpression<T> {
        TypedExpression::Boolean(e)
    }
}

impl<'ast, T> From<FieldElementExpression<'ast, T>> for TypedExpression<'ast, T> {
    fn from(e: FieldElementExpression<'ast, T>) -> TypedExpression<T> {
        TypedExpression::FieldElement(e)
    }
}

impl<'ast, T> From<IntExpression<'ast, T>> for TypedExpression<'ast, T> {
    fn from(e: IntExpression<'ast, T>) -> TypedExpression<T> {
        TypedExpression::Int(e)
    }
}

impl<'ast, T> From<UExpression<'ast, T>> for TypedExpression<'ast, T> {
    fn from(e: UExpression<'ast, T>) -> TypedExpression<T> {
        TypedExpression::Uint(e)
    }
}

impl<'ast, T> From<ArrayExpression<'ast, T>> for TypedExpression<'ast, T> {
    fn from(e: ArrayExpression<'ast, T>) -> TypedExpression<T> {
        TypedExpression::Array(e)
    }
}

impl<'ast, T> From<StructExpression<'ast, T>> for TypedExpression<'ast, T> {
    fn from(e: StructExpression<'ast, T>) -> TypedExpression<T> {
        TypedExpression::Struct(e)
    }
}

impl<'ast, T: fmt::Display> fmt::Display for TypedExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedExpression::Boolean(ref e) => write!(f, "{}", e),
            TypedExpression::FieldElement(ref e) => write!(f, "{}", e),
            TypedExpression::Uint(ref e) => write!(f, "{}", e),
            TypedExpression::Array(ref e) => write!(f, "{}", e),
            TypedExpression::Struct(ref s) => write!(f, "{}", s),
            TypedExpression::Int(ref s) => write!(f, "{}", s),
        }
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for TypedExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedExpression::Boolean(ref e) => write!(f, "{:?}", e),
            TypedExpression::FieldElement(ref e) => write!(f, "{:?}", e),
            TypedExpression::Uint(ref e) => write!(f, "{:?}", e),
            TypedExpression::Array(ref e) => write!(f, "{:?}", e),
            TypedExpression::Struct(ref s) => write!(f, "{:?}", s),
            TypedExpression::Int(ref s) => write!(f, "{:?}", s),
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for ArrayExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.inner)
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for ArrayExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.inner)
    }
}

impl<'ast, T: fmt::Display> fmt::Display for StructExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.inner {
            StructExpressionInner::Identifier(ref var) => write!(f, "{}", var),
            StructExpressionInner::Value(ref values) => write!(
                f,
                "{{{}}}",
                self.ty
                    .iter()
                    .map(|member| member.id.clone())
                    .zip(values.iter())
                    .map(|(id, o)| format!("{}: {}", id, o))
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            StructExpressionInner::FunctionCall(ref key, ref p) => {
                write!(f, "{}(", key.id,)?;
                for (i, param) in p.iter().enumerate() {
                    write!(f, "{}", param)?;
                    if i < p.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            StructExpressionInner::IfElse(ref condition, ref consequent, ref alternative) => {
                write!(
                    f,
                    "if {} then {} else {} fi",
                    condition, consequent, alternative
                )
            }
            StructExpressionInner::Member(ref struc, ref id) => write!(f, "{}.{}", struc, id),
            StructExpressionInner::Select(ref id, ref index) => write!(f, "{}[{}]", id, index),
        }
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for StructExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.inner)
    }
}

impl<'ast, T: Clone> Typed<'ast, T> for TypedExpression<'ast, T> {
    fn get_type(&self) -> Type {
        match *self {
            TypedExpression::Boolean(ref e) => e.get_type(),
            TypedExpression::FieldElement(ref e) => e.get_type(),
            TypedExpression::Array(ref e) => e.get_type(),
            TypedExpression::Uint(ref e) => e.get_type(),
            TypedExpression::Struct(ref s) => s.get_type(),
            TypedExpression::Int(_) => Type::Int,
        }
    }
}

impl<'ast, T: Clone> Typed<'ast, T> for ArrayExpression<'ast, T> {
    fn get_type(&self) -> Type {
        Type::array(self.ty.clone(), self.size.clone())
    }
}

impl<'ast, T: Clone> Typed<'ast, T> for StructExpression<'ast, T> {
    fn get_type(&self) -> Type {
        Type::Struct(self.ty.clone())
    }
}

impl<'ast, T: Clone> Typed<'ast, T> for FieldElementExpression<'ast, T> {
    fn get_type(&self) -> Type {
        Type::FieldElement
    }
}

impl<'ast, T: Clone> Typed<'ast, T> for UExpression<'ast, T> {
    fn get_type(&self) -> Type {
        Type::Uint(self.bitwidth)
    }
}

impl<'ast, T: Clone> Typed<'ast, T> for BooleanExpression<'ast, T> {
    fn get_type(&self) -> Type {
        Type::Boolean
    }
}

pub trait MultiTyped<'ast, T> {
    fn get_types(&self) -> &Vec<Type>;
}

#[derive(Clone, PartialEq, Hash, Eq)]
pub enum TypedExpressionList<'ast, T> {
    FunctionCall(FunctionKey<'ast>, Vec<TypedExpression<'ast, T>>, Vec<Type>),
}

impl<'ast, T> MultiTyped<'ast, T> for TypedExpressionList<'ast, T> {
    fn get_types(&self) -> &Vec<Type> {
        match *self {
            TypedExpressionList::FunctionCall(_, _, ref types) => types,
        }
    }
}

/// An expression of type `field`
#[derive(Clone, PartialEq, Hash, Eq)]
pub enum FieldElementExpression<'ast, T> {
    Number(T),
    Identifier(Identifier<'ast>),
    Add(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    Sub(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    Mult(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    Div(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    Pow(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    IfElse(
        Box<BooleanExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    FunctionCall(FunctionKey<'ast>, Vec<TypedExpression<'ast, T>>),
    Member(Box<StructExpression<'ast, T>>, MemberId),
    Select(Box<ArrayExpression<'ast, T>>, Box<UExpression<'ast, T>>),
}

impl<'ast, T: Field> FieldElementExpression<'ast, T> {
    pub fn try_from_int(i: IntExpression<'ast, T>) -> Result<Self, String> {
        match i {
            IntExpression::Value(i) => {
                if i <= T::max_value().to_biguint() {
                    Ok(Self::Number(T::from(i)))
                } else {
                    Err(format!("Literal `{} is too large for type `field`", i))
                }
            }
            IntExpression::Add(box e1, box e2) => Ok(Self::Add(
                box Self::try_from_int(e1)?,
                box Self::try_from_int(e2)?,
            )),
            IntExpression::Sub(box e1, box e2) => Ok(Self::Sub(
                box Self::try_from_int(e1)?,
                box Self::try_from_int(e2)?,
            )),
            IntExpression::Mult(box e1, box e2) => Ok(Self::Mult(
                box Self::try_from_int(e1)?,
                box Self::try_from_int(e2)?,
            )),
            IntExpression::Pow(box e1, box e2) => Ok(Self::Pow(
                box Self::try_from_int(e1)?,
                box Self::try_from_int(e2)?,
            )),
            IntExpression::Div(box e1, box e2) => Ok(Self::Div(
                box Self::try_from_int(e1)?,
                box Self::try_from_int(e2)?,
            )),
            IntExpression::IfElse(box condition, box consequence, box alternative) => {
                Ok(Self::IfElse(
                    box condition,
                    box Self::try_from_int(consequence)?,
                    box Self::try_from_int(alternative)?,
                ))
            }
            IntExpression::Select(..) => unimplemented!(),
            i => Err(format!("Expected a `field` but found expression `{}`", i)),
        }
    }
}

/// An expression of type `bool`
#[derive(Clone, PartialEq, Hash, Eq)]
pub enum BooleanExpression<'ast, T> {
    Identifier(Identifier<'ast>),
    Value(bool),
    FieldLt(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    FieldLe(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    FieldGe(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    FieldGt(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    UintLt(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    UintLe(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    UintGe(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    UintGt(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    FieldEq(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    BoolEq(
        Box<BooleanExpression<'ast, T>>,
        Box<BooleanExpression<'ast, T>>,
    ),
    ArrayEq(Box<ArrayExpression<'ast, T>>, Box<ArrayExpression<'ast, T>>),
    StructEq(
        Box<StructExpression<'ast, T>>,
        Box<StructExpression<'ast, T>>,
    ),
    UintEq(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    Or(
        Box<BooleanExpression<'ast, T>>,
        Box<BooleanExpression<'ast, T>>,
    ),
    And(
        Box<BooleanExpression<'ast, T>>,
        Box<BooleanExpression<'ast, T>>,
    ),
    Not(Box<BooleanExpression<'ast, T>>),
    IfElse(
        Box<BooleanExpression<'ast, T>>,
        Box<BooleanExpression<'ast, T>>,
        Box<BooleanExpression<'ast, T>>,
    ),
    Member(Box<StructExpression<'ast, T>>, MemberId),
    FunctionCall(FunctionKey<'ast>, Vec<TypedExpression<'ast, T>>),
    Select(Box<ArrayExpression<'ast, T>>, Box<UExpression<'ast, T>>),
}

/// An expression of type `array`
/// # Remarks
/// * Contrary to basic types which are represented as enums, we wrap an enum `ArrayExpressionInner` in a struct in order to keep track of the type (content and size)
/// of the array. Only using an enum would require generics, which would propagate up to TypedExpression which we want to keep simple, hence this "runtime"
/// type checking
#[derive(Clone, PartialEq, Hash, Eq)]
pub struct ArrayExpression<'ast, T> {
    size: usize,
    ty: Type,
    inner: ArrayExpressionInner<'ast, T>,
}

#[derive(Clone, PartialEq, Hash, Eq)]
pub enum ArrayExpressionInner<'ast, T> {
    Identifier(Identifier<'ast>),
    Value(Vec<TypedExpression<'ast, T>>),
    FunctionCall(FunctionKey<'ast>, Vec<TypedExpression<'ast, T>>),
    IfElse(
        Box<BooleanExpression<'ast, T>>,
        Box<ArrayExpression<'ast, T>>,
        Box<ArrayExpression<'ast, T>>,
    ),
    Member(Box<StructExpression<'ast, T>>, MemberId),
    Select(Box<ArrayExpression<'ast, T>>, Box<UExpression<'ast, T>>),
}

impl<'ast, T> ArrayExpressionInner<'ast, T> {
    pub fn annotate<S: Into<usize>>(self, ty: Type, size: S) -> ArrayExpression<'ast, T> {
        ArrayExpression {
            size: size.into(),
            ty,
            inner: self,
        }
    }
}

impl<'ast, T: Clone> ArrayExpression<'ast, T> {
    pub fn inner_type(&self) -> &Type {
        &self.ty
    }

    pub fn size(&self) -> usize {
        self.size.clone()
    }

    pub fn as_inner(&self) -> &ArrayExpressionInner<'ast, T> {
        &self.inner
    }

    pub fn into_inner(self) -> ArrayExpressionInner<'ast, T> {
        self.inner
    }

    pub fn get_array_type(&self) -> ArrayType {
        ArrayType {
            size: self.size(),
            ty: box self.inner_type().clone(),
        }
    }
}

impl<'ast, T: Field> ArrayExpression<'ast, T> {
    // precondition: `array` is only made of inline arrays
    pub fn try_from_int(array: Self, target_array_ty: ArrayType) -> Result<Self, ()> {
        if array.get_array_type() == target_array_ty {
            return Ok(array);
        }

        let array_ty = array.get_array_type();

        // sizes must be equal
        match target_array_ty.size == array_ty.size {
            true =>
            // elements must fit in the target type
            {
                match array.into_inner() {
                    ArrayExpressionInner::Value(inline_array) => {
                        match *target_array_ty.ty {
                            Type::FieldElement => {
                                // try to convert all elements to field
                                let converted = inline_array
                                    .into_iter()
                                    .map(|e| {
                                        let int = IntExpression::try_from(e)?;
                                        let field = FieldElementExpression::try_from_int(int)
                                            .map_err(|_| ())?;
                                        Ok(field.into())
                                    })
                                    .collect::<Result<Vec<TypedExpression<'ast, T>>, ()>>()?;
                                Ok(ArrayExpressionInner::Value(converted)
                                    .annotate(*target_array_ty.ty, array_ty.size))
                            }
                            Type::Uint(bitwidth) => {
                                // try to convert all elements to field
                                let converted = inline_array
                                    .into_iter()
                                    .map(|e| {
                                        let int = IntExpression::try_from(e)?;
                                        let field = UExpression::try_from_int(int, bitwidth)
                                            .map_err(|_| ())?;
                                        Ok(field.into())
                                    })
                                    .collect::<Result<Vec<TypedExpression<'ast, T>>, ()>>()?;
                                Ok(ArrayExpressionInner::Value(converted)
                                    .annotate(*target_array_ty.ty, array_ty.size))
                            }
                            Type::Array(ref array_ty) => {
                                // try to convert all elements to field
                                let converted = inline_array
                                    .into_iter()
                                    .map(|e| {
                                        let array = ArrayExpression::try_from(e)?;
                                        let array =
                                            ArrayExpression::try_from_int(array, array_ty.clone())
                                                .map_err(|_| ())?;
                                        Ok(array.into())
                                    })
                                    .collect::<Result<Vec<TypedExpression<'ast, T>>, ()>>()?;
                                Ok(ArrayExpressionInner::Value(converted)
                                    .annotate(*target_array_ty.ty.clone(), array_ty.size.clone()))
                            }
                            _ => Err(()),
                        }
                    }
                    _ => unreachable!(""),
                }
            }
            false => Err(()),
        }
    }
}

#[derive(Clone, PartialEq, Hash, Eq)]
pub struct StructExpression<'ast, T> {
    ty: StructType,
    inner: StructExpressionInner<'ast, T>,
}

impl<'ast, T> StructExpression<'ast, T> {
    pub fn ty(&self) -> &StructType {
        &self.ty
    }

    pub fn as_inner(&self) -> &StructExpressionInner<'ast, T> {
        &self.inner
    }

    pub fn into_inner(self) -> StructExpressionInner<'ast, T> {
        self.inner
    }
}

#[derive(Clone, PartialEq, Hash, Eq)]
pub enum StructExpressionInner<'ast, T> {
    Identifier(Identifier<'ast>),
    Value(Vec<TypedExpression<'ast, T>>),
    FunctionCall(FunctionKey<'ast>, Vec<TypedExpression<'ast, T>>),
    IfElse(
        Box<BooleanExpression<'ast, T>>,
        Box<StructExpression<'ast, T>>,
        Box<StructExpression<'ast, T>>,
    ),
    Member(Box<StructExpression<'ast, T>>, MemberId),
    Select(Box<ArrayExpression<'ast, T>>, Box<UExpression<'ast, T>>),
}

impl<'ast, T> StructExpressionInner<'ast, T> {
    pub fn annotate(self, ty: StructType) -> StructExpression<'ast, T> {
        StructExpression { ty, inner: self }
    }
}

// Downcasts
// Due to the fact that we keep TypedExpression simple, we end up with ArrayExpressionInner::Value whose elements are any TypedExpression, but we enforce by
// construction that these elements are of the type declared in the corresponding ArrayExpression. As we know this by construction, we can downcast the TypedExpression to the correct type
// ArrayExpression { type: Type::FieldElement, size: 42, inner: [TypedExpression::FieldElement(FieldElementExpression), ...]} <- the fact that inner only contains field elements is not enforced by the rust type system
impl<'ast, T> TryFrom<TypedExpression<'ast, T>> for FieldElementExpression<'ast, T> {
    type Error = ();

    fn try_from(
        te: TypedExpression<'ast, T>,
    ) -> Result<FieldElementExpression<'ast, T>, Self::Error> {
        match te {
            TypedExpression::FieldElement(e) => Ok(e),
            _ => Err(()),
        }
    }
}

impl<'ast, T> TryFrom<TypedExpression<'ast, T>> for BooleanExpression<'ast, T> {
    type Error = ();

    fn try_from(te: TypedExpression<'ast, T>) -> Result<BooleanExpression<'ast, T>, Self::Error> {
        match te {
            TypedExpression::Boolean(e) => Ok(e),
            _ => Err(()),
        }
    }
}

impl<'ast, T> TryFrom<TypedExpression<'ast, T>> for UExpression<'ast, T> {
    type Error = ();

    fn try_from(te: TypedExpression<'ast, T>) -> Result<UExpression<'ast, T>, Self::Error> {
        match te {
            TypedExpression::Uint(e) => Ok(e),
            _ => Err(()),
        }
    }
}

impl<'ast, T> TryFrom<TypedExpression<'ast, T>> for ArrayExpression<'ast, T> {
    type Error = ();

    fn try_from(te: TypedExpression<'ast, T>) -> Result<ArrayExpression<'ast, T>, Self::Error> {
        match te {
            TypedExpression::Array(e) => Ok(e),
            _ => Err(()),
        }
    }
}

impl<'ast, T> TryFrom<TypedExpression<'ast, T>> for IntExpression<'ast, T> {
    type Error = ();

    fn try_from(te: TypedExpression<'ast, T>) -> Result<IntExpression<'ast, T>, Self::Error> {
        match te {
            TypedExpression::Int(e) => Ok(e),
            _ => Err(()),
        }
    }
}

impl<'ast, T> TryFrom<TypedExpression<'ast, T>> for StructExpression<'ast, T> {
    type Error = ();

    fn try_from(te: TypedExpression<'ast, T>) -> Result<StructExpression<'ast, T>, Self::Error> {
        match te {
            TypedExpression::Struct(e) => Ok(e),
            _ => Err(()),
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for FieldElementExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FieldElementExpression::Number(ref i) => write!(f, "{}f", i),
            FieldElementExpression::Identifier(ref var) => write!(f, "{}", var),
            FieldElementExpression::Add(ref lhs, ref rhs) => write!(f, "({} + {})", lhs, rhs),
            FieldElementExpression::Sub(ref lhs, ref rhs) => write!(f, "({} - {})", lhs, rhs),
            FieldElementExpression::Mult(ref lhs, ref rhs) => write!(f, "({} * {})", lhs, rhs),
            FieldElementExpression::Div(ref lhs, ref rhs) => write!(f, "({} / {})", lhs, rhs),
            FieldElementExpression::Pow(ref lhs, ref rhs) => write!(f, "{}**{}", lhs, rhs),
            FieldElementExpression::IfElse(ref condition, ref consequent, ref alternative) => {
                write!(
                    f,
                    "if {} then {} else {} fi",
                    condition, consequent, alternative
                )
            }
            FieldElementExpression::FunctionCall(ref k, ref p) => {
                write!(f, "{}(", k.id,)?;
                for (i, param) in p.iter().enumerate() {
                    write!(f, "{}", param)?;
                    if i < p.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            FieldElementExpression::Member(ref struc, ref id) => write!(f, "{}.{}", struc, id),
            FieldElementExpression::Select(ref id, ref index) => write!(f, "{}[{}]", id, index),
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for UExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.inner {
            UExpressionInner::Value(ref v) => write!(f, "{}u{}", v, self.bitwidth),
            UExpressionInner::Identifier(ref var) => write!(f, "{}", var),
            UExpressionInner::Add(ref lhs, ref rhs) => write!(f, "({} + {})", lhs, rhs),
            UExpressionInner::And(ref lhs, ref rhs) => write!(f, "({} & {})", lhs, rhs),
            UExpressionInner::Or(ref lhs, ref rhs) => write!(f, "({} | {})", lhs, rhs),
            UExpressionInner::Xor(ref lhs, ref rhs) => write!(f, "({} ^ {})", lhs, rhs),
            UExpressionInner::Sub(ref lhs, ref rhs) => write!(f, "({} - {})", lhs, rhs),
            UExpressionInner::Mult(ref lhs, ref rhs) => write!(f, "({} * {})", lhs, rhs),
            UExpressionInner::RightShift(ref e, ref by) => write!(f, "({} >> {})", e, by),
            UExpressionInner::LeftShift(ref e, ref by) => write!(f, "({} << {})", e, by),
            UExpressionInner::Not(ref e) => write!(f, "!{}", e),
            UExpressionInner::Select(ref id, ref index) => write!(f, "{}[{}]", id, index),
            UExpressionInner::FunctionCall(ref k, ref p) => {
                write!(f, "{}(", k.id,)?;
                for (i, param) in p.iter().enumerate() {
                    write!(f, "{}", param)?;
                    if i < p.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            UExpressionInner::IfElse(ref condition, ref consequent, ref alternative) => write!(
                f,
                "if {} then {} else {} fi",
                condition, consequent, alternative
            ),
            UExpressionInner::Member(ref struc, ref id) => write!(f, "{}.{}", struc, id),
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for BooleanExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            BooleanExpression::Identifier(ref var) => write!(f, "{}", var),
            BooleanExpression::FieldLt(ref lhs, ref rhs) => write!(f, "{} < {}", lhs, rhs),
            BooleanExpression::FieldLe(ref lhs, ref rhs) => write!(f, "{} <= {}", lhs, rhs),
            BooleanExpression::FieldGe(ref lhs, ref rhs) => write!(f, "{} >= {}", lhs, rhs),
            BooleanExpression::FieldGt(ref lhs, ref rhs) => write!(f, "{} > {}", lhs, rhs),
            BooleanExpression::UintLt(ref lhs, ref rhs) => write!(f, "{} < {}", lhs, rhs),
            BooleanExpression::UintLe(ref lhs, ref rhs) => write!(f, "{} <= {}", lhs, rhs),
            BooleanExpression::UintGe(ref lhs, ref rhs) => write!(f, "{} >= {}", lhs, rhs),
            BooleanExpression::UintGt(ref lhs, ref rhs) => write!(f, "{} > {}", lhs, rhs),
            BooleanExpression::FieldEq(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            BooleanExpression::BoolEq(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            BooleanExpression::ArrayEq(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            BooleanExpression::StructEq(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            BooleanExpression::UintEq(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            BooleanExpression::Or(ref lhs, ref rhs) => write!(f, "{} || {}", lhs, rhs),
            BooleanExpression::And(ref lhs, ref rhs) => write!(f, "{} && {}", lhs, rhs),
            BooleanExpression::Not(ref exp) => write!(f, "!{}", exp),
            BooleanExpression::Value(b) => write!(f, "{}", b),
            BooleanExpression::FunctionCall(ref k, ref p) => {
                write!(f, "{}(", k.id,)?;
                for (i, param) in p.iter().enumerate() {
                    write!(f, "{}", param)?;
                    if i < p.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            BooleanExpression::IfElse(ref condition, ref consequent, ref alternative) => write!(
                f,
                "if {} then {} else {} fi",
                condition, consequent, alternative
            ),
            BooleanExpression::Member(ref struc, ref id) => write!(f, "{}.{}", struc, id),
            BooleanExpression::Select(ref id, ref index) => write!(f, "{}[{}]", id, index),
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for ArrayExpressionInner<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ArrayExpressionInner::Identifier(ref var) => write!(f, "{}", var),
            ArrayExpressionInner::Value(ref values) => write!(
                f,
                "[{}]",
                values
                    .iter()
                    .map(|o| o.to_string())
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            ArrayExpressionInner::FunctionCall(ref key, ref p) => {
                write!(f, "{}(", key.id,)?;
                for (i, param) in p.iter().enumerate() {
                    write!(f, "{}", param)?;
                    if i < p.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            ArrayExpressionInner::IfElse(ref condition, ref consequent, ref alternative) => write!(
                f,
                "if {} then {} else {} fi",
                condition, consequent, alternative
            ),
            ArrayExpressionInner::Member(ref s, ref id) => write!(f, "{}.{}", s, id),
            ArrayExpressionInner::Select(ref id, ref index) => write!(f, "{}[{}]", id, index),
        }
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for BooleanExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            BooleanExpression::Identifier(ref var) => write!(f, "Ide({})", var),
            BooleanExpression::Value(b) => write!(f, "Value({})", b),
            BooleanExpression::IfElse(ref condition, ref consequent, ref alternative) => write!(
                f,
                "IfElse({:?}, {:?}, {:?})",
                condition, consequent, alternative
            ),
            BooleanExpression::FieldLt(ref lhs, ref rhs) => {
                write!(f, "FieldLt({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::FieldLe(ref lhs, ref rhs) => {
                write!(f, "FieldLe({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::FieldGe(ref lhs, ref rhs) => {
                write!(f, "FieldGe({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::FieldGt(ref lhs, ref rhs) => {
                write!(f, "FieldGt({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::UintLt(ref lhs, ref rhs) => {
                write!(f, "UintLt({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::UintLe(ref lhs, ref rhs) => {
                write!(f, "UintLe({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::UintGe(ref lhs, ref rhs) => {
                write!(f, "UintGe({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::UintGt(ref lhs, ref rhs) => {
                write!(f, "UintGt({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::FieldEq(ref lhs, ref rhs) => {
                write!(f, "FieldEq({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::BoolEq(ref lhs, ref rhs) => {
                write!(f, "BoolEq({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::ArrayEq(ref lhs, ref rhs) => {
                write!(f, "ArrayEq({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::StructEq(ref lhs, ref rhs) => {
                write!(f, "StructEq({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::UintEq(ref lhs, ref rhs) => {
                write!(f, "UintEq({:?}, {:?})", lhs, rhs)
            }
            BooleanExpression::And(ref lhs, ref rhs) => write!(f, "And({:?}, {:?})", lhs, rhs),
            BooleanExpression::Not(ref exp) => write!(f, "Not({:?})", exp),
            BooleanExpression::FunctionCall(ref i, ref p) => {
                write!(f, "FunctionCall({:?}, (", i)?;
                f.debug_list().entries(p.iter()).finish()?;
                write!(f, ")")
            }
            BooleanExpression::Select(ref array, ref index) => {
                write!(f, "Select({:?}, {:?})", array, index)
            }
            BooleanExpression::Member(ref struc, ref id) => {
                write!(f, "Access({:?}, {:?})", struc, id)
            }
            BooleanExpression::Or(ref lhs, ref rhs) => write!(f, "Or({:?}, {:?})", lhs, rhs),
        }
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for FieldElementExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FieldElementExpression::Number(ref i) => write!(f, "Num({:?})", i),
            FieldElementExpression::Identifier(ref var) => write!(f, "Ide({:?})", var),
            FieldElementExpression::Add(ref lhs, ref rhs) => write!(f, "Add({:?}, {:?})", lhs, rhs),
            FieldElementExpression::Sub(ref lhs, ref rhs) => write!(f, "Sub({:?}, {:?})", lhs, rhs),
            FieldElementExpression::Mult(ref lhs, ref rhs) => {
                write!(f, "Mult({:?}, {:?})", lhs, rhs)
            }
            FieldElementExpression::Div(ref lhs, ref rhs) => write!(f, "Div({:?}, {:?})", lhs, rhs),
            FieldElementExpression::Pow(ref lhs, ref rhs) => write!(f, "Pow({:?}, {:?})", lhs, rhs),
            FieldElementExpression::IfElse(ref condition, ref consequent, ref alternative) => {
                write!(
                    f,
                    "IfElse({:?}, {:?}, {:?})",
                    condition, consequent, alternative
                )
            }
            FieldElementExpression::FunctionCall(ref i, ref p) => {
                write!(f, "FunctionCall({:?}, (", i)?;
                f.debug_list().entries(p.iter()).finish()?;
                write!(f, ")")
            }
            FieldElementExpression::Member(ref struc, ref id) => {
                write!(f, "Member({:?}, {:?})", struc, id)
            }
            FieldElementExpression::Select(ref id, ref index) => {
                write!(f, "Select({:?}, {:?})", id, index)
            }
        }
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for ArrayExpressionInner<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ArrayExpressionInner::Identifier(ref var) => write!(f, "Identifier({:?})", var),
            ArrayExpressionInner::Value(ref values) => write!(f, "Value({:?})", values),
            ArrayExpressionInner::FunctionCall(ref i, ref p) => {
                write!(f, "FunctionCall({:?}, (", i)?;
                f.debug_list().entries(p.iter()).finish()?;
                write!(f, ")")
            }
            ArrayExpressionInner::IfElse(ref condition, ref consequent, ref alternative) => write!(
                f,
                "IfElse({:?}, {:?}, {:?})",
                condition, consequent, alternative
            ),
            ArrayExpressionInner::Member(ref struc, ref id) => {
                write!(f, "Member({:?}, {:?})", struc, id)
            }
            ArrayExpressionInner::Select(ref id, ref index) => {
                write!(f, "Select({:?}, {:?})", id, index)
            }
        }
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for StructExpressionInner<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            StructExpressionInner::Identifier(ref var) => write!(f, "{:?}", var),
            StructExpressionInner::Value(ref values) => write!(f, "{:?}", values),
            StructExpressionInner::FunctionCall(ref i, ref p) => {
                write!(f, "FunctionCall({:?}, (", i)?;
                f.debug_list().entries(p.iter()).finish()?;
                write!(f, ")")
            }
            StructExpressionInner::IfElse(ref condition, ref consequent, ref alternative) => {
                write!(
                    f,
                    "IfElse({:?}, {:?}, {:?})",
                    condition, consequent, alternative
                )
            }
            StructExpressionInner::Member(ref struc, ref id) => {
                write!(f, "Member({:?}, {:?})", struc, id)
            }
            StructExpressionInner::Select(ref id, ref index) => {
                write!(f, "Select({:?}, {:?})", id, index)
            }
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for TypedExpressionList<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedExpressionList::FunctionCall(ref key, ref p, _) => {
                write!(f, "{}(", key.id,)?;
                for (i, param) in p.iter().enumerate() {
                    write!(f, "{}", param)?;
                    if i < p.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
        }
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for TypedExpressionList<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedExpressionList::FunctionCall(ref i, ref p, _) => {
                write!(f, "FunctionCall({:?}, (", i)?;
                f.debug_list().entries(p.iter()).finish()?;
                write!(f, ")")
            }
        }
    }
}

// Common behaviour across expressions

pub trait IfElse<'ast, T> {
    fn if_else(condition: BooleanExpression<'ast, T>, consequence: Self, alternative: Self)
        -> Self;
}

impl<'ast, T> IfElse<'ast, T> for FieldElementExpression<'ast, T> {
    fn if_else(
        condition: BooleanExpression<'ast, T>,
        consequence: Self,
        alternative: Self,
    ) -> Self {
        FieldElementExpression::IfElse(box condition, box consequence, box alternative)
    }
}

impl<'ast, T> IfElse<'ast, T> for BooleanExpression<'ast, T> {
    fn if_else(
        condition: BooleanExpression<'ast, T>,
        consequence: Self,
        alternative: Self,
    ) -> Self {
        BooleanExpression::IfElse(box condition, box consequence, box alternative)
    }
}

impl<'ast, T> IfElse<'ast, T> for UExpression<'ast, T> {
    fn if_else(
        condition: BooleanExpression<'ast, T>,
        consequence: Self,
        alternative: Self,
    ) -> Self {
        let bitwidth = consequence.bitwidth;

        UExpressionInner::IfElse(box condition, box consequence, box alternative).annotate(bitwidth)
    }
}

impl<'ast, T: Clone> IfElse<'ast, T> for ArrayExpression<'ast, T> {
    fn if_else(
        condition: BooleanExpression<'ast, T>,
        consequence: Self,
        alternative: Self,
    ) -> Self {
        let ty = consequence.inner_type().clone();
        let size = consequence.size();
        ArrayExpressionInner::IfElse(box condition, box consequence, box alternative)
            .annotate(ty, size)
    }
}

impl<'ast, T: Clone> IfElse<'ast, T> for StructExpression<'ast, T> {
    fn if_else(
        condition: BooleanExpression<'ast, T>,
        consequence: Self,
        alternative: Self,
    ) -> Self {
        let ty = consequence.ty().clone();
        StructExpressionInner::IfElse(box condition, box consequence, box alternative).annotate(ty)
    }
}

pub trait Select<'ast, T> {
    fn select(array: ArrayExpression<'ast, T>, index: UExpression<'ast, T>) -> Self;
}

impl<'ast, T> Select<'ast, T> for FieldElementExpression<'ast, T> {
    fn select(array: ArrayExpression<'ast, T>, index: UExpression<'ast, T>) -> Self {
        FieldElementExpression::Select(box array, box index)
    }
}

impl<'ast, T> Select<'ast, T> for BooleanExpression<'ast, T> {
    fn select(array: ArrayExpression<'ast, T>, index: UExpression<'ast, T>) -> Self {
        BooleanExpression::Select(box array, box index)
    }
}

impl<'ast, T: Clone> Select<'ast, T> for UExpression<'ast, T> {
    fn select(array: ArrayExpression<'ast, T>, index: UExpression<'ast, T>) -> Self {
        let bitwidth = match array.inner_type().clone() {
            Type::Uint(bitwidth) => bitwidth,
            _ => unreachable!(),
        };

        UExpressionInner::Select(box array, box index).annotate(bitwidth)
    }
}

impl<'ast, T: Clone> Select<'ast, T> for ArrayExpression<'ast, T> {
    fn select(array: ArrayExpression<'ast, T>, index: UExpression<'ast, T>) -> Self {
        let (ty, size) = match array.inner_type() {
            Type::Array(array_type) => (array_type.ty.clone(), array_type.size.clone()),
            _ => unreachable!(),
        };

        ArrayExpressionInner::Select(box array, box index).annotate(*ty, size)
    }
}

impl<'ast, T: Clone> Select<'ast, T> for StructExpression<'ast, T> {
    fn select(array: ArrayExpression<'ast, T>, index: UExpression<'ast, T>) -> Self {
        let members = match array.inner_type().clone() {
            Type::Struct(members) => members,
            _ => unreachable!(),
        };

        StructExpressionInner::Select(box array, box index).annotate(members)
    }
}

pub trait Member<'ast, T> {
    fn member(s: StructExpression<'ast, T>, member_id: MemberId) -> Self;
}

impl<'ast, T> Member<'ast, T> for FieldElementExpression<'ast, T> {
    fn member(s: StructExpression<'ast, T>, member_id: MemberId) -> Self {
        FieldElementExpression::Member(box s, member_id)
    }
}

impl<'ast, T> Member<'ast, T> for BooleanExpression<'ast, T> {
    fn member(s: StructExpression<'ast, T>, member_id: MemberId) -> Self {
        BooleanExpression::Member(box s, member_id)
    }
}

impl<'ast, T: Clone> Member<'ast, T> for UExpression<'ast, T> {
    fn member(s: StructExpression<'ast, T>, member_id: MemberId) -> Self {
        let members = s.ty().clone();

        let ty = members
            .iter()
            .find(|member| *member.id == member_id)
            .unwrap()
            .ty
            .clone();

        let bitwidth = match *ty {
            Type::Uint(bitwidth) => bitwidth,
            _ => unreachable!(),
        };

        UExpressionInner::Member(box s, member_id).annotate(bitwidth)
    }
}

impl<'ast, T: Clone> Member<'ast, T> for ArrayExpression<'ast, T> {
    fn member(s: StructExpression<'ast, T>, member_id: MemberId) -> Self {
        let members = s.ty().clone();

        let ty = members
            .iter()
            .find(|member| *member.id == member_id)
            .unwrap()
            .ty
            .clone();

        let (ty, size) = match *ty {
            Type::Array(array_type) => (array_type.ty, array_type.size),
            _ => unreachable!(),
        };

        ArrayExpressionInner::Member(box s, member_id).annotate(*ty, size)
    }
}

impl<'ast, T: Clone> Member<'ast, T> for StructExpression<'ast, T> {
    fn member(s: StructExpression<'ast, T>, member_id: MemberId) -> Self {
        let members = s.ty().clone();

        let ty = members
            .iter()
            .find(|member| *member.id == member_id)
            .unwrap()
            .ty
            .clone();

        let members = match *ty {
            Type::Struct(members) => members,
            _ => unreachable!(),
        };

        StructExpressionInner::Member(box s, member_id).annotate(members)
    }
}
