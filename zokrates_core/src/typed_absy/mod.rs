//! Module containing structs and enums to represent a program.
//!
//! @file absy.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

pub mod folder;
mod parameter;
mod variable;

pub use crate::typed_absy::parameter::Parameter;
pub use crate::typed_absy::variable::Variable;
use crate::types::{FunctionKey, Signature, Type};
use embed::FlatEmbed;
use std::collections::HashMap;
use std::fmt;
use zokrates_field::field::Field;

pub use self::folder::Folder;

/// A identifier for a variable
#[derive(Debug, PartialEq, Clone, Hash, Eq)]
pub struct Identifier<'ast> {
    /// the id of the variable
    pub id: &'ast str,
    /// the version of the variable, used after SSA transformation
    pub version: usize,
    /// the call stack of the variable, used when inlining
    pub stack: Vec<(TypedModuleId, FunctionKey<'ast>, usize)>,
}

/// An identifier for a `TypedModule`. Typically a path or uri.
pub type TypedModuleId = String;

/// A collection of `TypedModule`s
pub type TypedModules<'ast, T> = HashMap<TypedModuleId, TypedModule<'ast, T>>;

/// A collection of `TypedFunctionSymbol`s
/// # Remarks
/// * It is the role of the semantic checker to make sure there are no duplicates for a given `FunctionKey`
///   in a given `TypedModule`, hence the use of a HashMap
pub type TypedFunctionSymbols<'ast, T> = HashMap<FunctionKey<'ast>, TypedFunctionSymbol<'ast, T>>;

/// A typed program as a collection of modules, one of them being the main
#[derive(PartialEq, Debug)]
pub struct TypedProgram<'ast, T: Field> {
    pub modules: TypedModules<'ast, T>,
    pub main: TypedModuleId,
}

impl<'ast, T: Field> fmt::Display for TypedProgram<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (module_id, module) in &self.modules {
            writeln!(
                f,
                "| {}: |{}",
                module_id,
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

/// A
#[derive(PartialEq, Clone)]
pub struct TypedModule<'ast, T: Field> {
    /// Functions of the program
    pub functions: TypedFunctionSymbols<'ast, T>,
}

impl<'ast> fmt::Display for Identifier<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}_{}_{}",
            self.stack
                .iter()
                .map(|(name, sig, count)| format!("{}_{}_{}", name, sig.to_slug(), count))
                .collect::<Vec<_>>()
                .join("_"),
            self.id,
            self.version
        )
    }
}

impl<'ast> From<&'ast str> for Identifier<'ast> {
    fn from(id: &'ast str) -> Identifier<'ast> {
        Identifier {
            id,
            version: 0,
            stack: vec![],
        }
    }
}

#[cfg(test)]
impl<'ast> Identifier<'ast> {
    pub fn version(mut self, version: usize) -> Self {
        self.version = version;
        self
    }

    pub fn stack(mut self, stack: Vec<(TypedModuleId, FunctionKey<'ast>, usize)>) -> Self {
        self.stack = stack;
        self
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypedFunctionSymbol<'ast, T: Field> {
    Here(TypedFunction<'ast, T>),
    There(FunctionKey<'ast>, TypedModuleId),
    Flat(FlatEmbed),
}

impl<'ast, T: Field> TypedFunctionSymbol<'ast, T> {
    pub fn signature<'a>(&'a self, modules: &'a TypedModules<T>) -> Signature {
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
            TypedFunctionSymbol::Flat(flat_fun) => flat_fun.signature::<T>(),
        }
    }
}

impl<'ast, T: Field> fmt::Display for TypedModule<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let res = self
            .functions
            .iter()
            .map(|(key, symbol)| match symbol {
                TypedFunctionSymbol::Here(ref function) => format!("def {}{}", key.id, function),
                TypedFunctionSymbol::There(ref fun_key, ref module_id) => format!(
                    "import {} from \"{}\" as {} // with signature {}",
                    fun_key.id, module_id, key.id, key.signature
                ),
                TypedFunctionSymbol::Flat(ref flat_fun) => {
                    format!("def {}{}:\n\t// hidden", key.id, flat_fun.signature::<T>())
                }
            })
            .collect::<Vec<_>>();
        write!(f, "{}", res.join("\n"))
    }
}

impl<'ast, T: Field> fmt::Debug for TypedModule<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "module(\n\tfunctions:\n\t\t{}\n)",
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
pub struct TypedFunction<'ast, T: Field> {
    /// Arguments of the function
    pub arguments: Vec<Parameter<'ast>>,
    /// Vector of statements that are executed when running the function
    pub statements: Vec<TypedStatement<'ast, T>>,
    /// function signature
    pub signature: Signature,
}

impl<'ast, T: Field> fmt::Display for TypedFunction<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "({}) -> ({}):\n{}",
            self.arguments
                .iter()
                .map(|x| format!("{}", x))
                .collect::<Vec<_>>()
                .join(", "),
            self.signature
                .outputs
                .iter()
                .map(|x| format!("{}", x))
                .collect::<Vec<_>>()
                .join(", "),
            self.statements
                .iter()
                .map(|x| format!("\t{}", x))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

impl<'ast, T: Field> fmt::Debug for TypedFunction<'ast, T> {
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
pub enum TypedAssignee<'ast, T: Field> {
    Identifier(Variable<'ast>),
    ArrayElement(
        Box<TypedAssignee<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
}

impl<'ast, T: Field> Typed for TypedAssignee<'ast, T> {
    fn get_type(&self) -> Type {
        match *self {
            TypedAssignee::Identifier(ref v) => v.get_type(),
            TypedAssignee::ArrayElement(ref a, _) => {
                let a_type = a.get_type();
                match a_type {
                    Type::FieldElementArray(_) => Type::FieldElement,
                    _ => panic!("array element has to take array"),
                }
            }
        }
    }
}

impl<'ast, T: Field> fmt::Debug for TypedAssignee<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedAssignee::Identifier(ref s) => write!(f, "{}", s.id),
            TypedAssignee::ArrayElement(ref a, ref e) => write!(f, "{}[{}]", a, e),
        }
    }
}

impl<'ast, T: Field> fmt::Display for TypedAssignee<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

/// A statement in a `TypedFunction`
#[derive(Clone, PartialEq)]
pub enum TypedStatement<'ast, T: Field> {
    Return(Vec<TypedExpression<'ast, T>>),
    Definition(TypedAssignee<'ast, T>, TypedExpression<'ast, T>),
    Declaration(Variable<'ast>),
    Condition(TypedExpression<'ast, T>, TypedExpression<'ast, T>),
    For(Variable<'ast>, T, T, Vec<TypedStatement<'ast, T>>),
    MultipleDefinition(Vec<Variable<'ast>>, TypedExpressionList<'ast, T>),
}

impl<'ast, T: Field> fmt::Debug for TypedStatement<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedStatement::Return(ref exprs) => {
                r#try!(write!(f, "Return("));
                for (i, expr) in exprs.iter().enumerate() {
                    r#try!(write!(f, "{}", expr));
                    if i < exprs.len() - 1 {
                        r#try!(write!(f, ", "));
                    }
                }
                write!(f, ")")
            }
            TypedStatement::Declaration(ref var) => write!(f, "Declaration({:?})", var),
            TypedStatement::Definition(ref lhs, ref rhs) => {
                write!(f, "Definition({:?}, {:?})", lhs, rhs)
            }
            TypedStatement::Condition(ref lhs, ref rhs) => {
                write!(f, "Condition({:?}, {:?})", lhs, rhs)
            }
            TypedStatement::For(ref var, ref start, ref stop, ref list) => {
                r#try!(write!(f, "for {:?} in {:?}..{:?} do\n", var, start, stop));
                for l in list {
                    r#try!(write!(f, "\t\t{:?}\n", l));
                }
                write!(f, "\tendfor")
            }
            TypedStatement::MultipleDefinition(ref lhs, ref rhs) => {
                write!(f, "MultipleDefinition({:?}, {:?})", lhs, rhs)
            }
        }
    }
}

impl<'ast, T: Field> fmt::Display for TypedStatement<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedStatement::Return(ref exprs) => {
                r#try!(write!(f, "return "));
                for (i, expr) in exprs.iter().enumerate() {
                    r#try!(write!(f, "{}", expr));
                    if i < exprs.len() - 1 {
                        r#try!(write!(f, ", "));
                    }
                }
                write!(f, "")
            }
            TypedStatement::Declaration(ref var) => write!(f, "{}", var),
            TypedStatement::Definition(ref lhs, ref rhs) => write!(f, "{} = {}", lhs, rhs),
            TypedStatement::Condition(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            TypedStatement::For(ref var, ref start, ref stop, ref list) => {
                r#try!(write!(f, "for {} in {}..{} do\n", var, start, stop));
                for l in list {
                    r#try!(write!(f, "\t\t{}\n", l));
                }
                write!(f, "\tendfor")
            }
            TypedStatement::MultipleDefinition(ref ids, ref rhs) => {
                for (i, id) in ids.iter().enumerate() {
                    r#try!(write!(f, "{}", id));
                    if i < ids.len() - 1 {
                        r#try!(write!(f, ", "));
                    }
                }
                write!(f, " = {}", rhs)
            }
        }
    }
}

pub trait Typed {
    fn get_type(&self) -> Type;
}

/// A typed expression
#[derive(Clone, PartialEq, Hash, Eq)]
pub enum TypedExpression<'ast, T: Field> {
    Boolean(BooleanExpression<'ast, T>),
    FieldElement(FieldElementExpression<'ast, T>),
    FieldElementArray(FieldElementArrayExpression<'ast, T>),
}

impl<'ast, T: Field> From<BooleanExpression<'ast, T>> for TypedExpression<'ast, T> {
    fn from(e: BooleanExpression<'ast, T>) -> TypedExpression<T> {
        TypedExpression::Boolean(e)
    }
}

impl<'ast, T: Field> From<FieldElementExpression<'ast, T>> for TypedExpression<'ast, T> {
    fn from(e: FieldElementExpression<'ast, T>) -> TypedExpression<T> {
        TypedExpression::FieldElement(e)
    }
}

impl<'ast, T: Field> From<FieldElementArrayExpression<'ast, T>> for TypedExpression<'ast, T> {
    fn from(e: FieldElementArrayExpression<'ast, T>) -> TypedExpression<T> {
        TypedExpression::FieldElementArray(e)
    }
}

impl<'ast, T: Field> fmt::Display for TypedExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedExpression::Boolean(ref e) => write!(f, "{}", e),
            TypedExpression::FieldElement(ref e) => write!(f, "{}", e),
            TypedExpression::FieldElementArray(ref e) => write!(f, "{}", e),
        }
    }
}

impl<'ast, T: Field> fmt::Debug for TypedExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedExpression::Boolean(ref e) => write!(f, "{:?}", e),
            TypedExpression::FieldElement(ref e) => write!(f, "{:?}", e),
            TypedExpression::FieldElementArray(ref e) => write!(f, "{:?}", e),
        }
    }
}

impl<'ast, T: Field> Typed for TypedExpression<'ast, T> {
    fn get_type(&self) -> Type {
        match *self {
            TypedExpression::Boolean(_) => Type::Boolean,
            TypedExpression::FieldElement(_) => Type::FieldElement,
            TypedExpression::FieldElementArray(ref e) => e.get_type(),
        }
    }
}

impl<'ast, T: Field> Typed for FieldElementArrayExpression<'ast, T> {
    fn get_type(&self) -> Type {
        match *self {
            FieldElementArrayExpression::Identifier(n, _) => Type::FieldElementArray(n),
            FieldElementArrayExpression::Value(n, _) => Type::FieldElementArray(n),
            FieldElementArrayExpression::FunctionCall(n, _, _) => Type::FieldElementArray(n),
            FieldElementArrayExpression::IfElse(_, ref consequence, _) => consequence.get_type(),
            FieldElementArrayExpression::Slice(_, from, to) => Type::FieldElementArray(to - from),
        }
    }
}

pub trait MultiTyped {
    fn get_types(&self) -> &Vec<Type>;
}

#[derive(Clone, PartialEq)]
pub enum TypedExpressionList<'ast, T: Field> {
    FunctionCall(FunctionKey<'ast>, Vec<TypedExpression<'ast, T>>, Vec<Type>),
}

impl<'ast, T: Field> MultiTyped for TypedExpressionList<'ast, T> {
    fn get_types(&self) -> &Vec<Type> {
        match *self {
            TypedExpressionList::FunctionCall(_, _, ref types) => types,
        }
    }
}

/// An expression of type `field`
#[derive(Clone, PartialEq, Hash, Eq)]
pub enum FieldElementExpression<'ast, T: Field> {
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
    Select(
        Box<FieldElementArrayExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
}

/// An expression of type `bool`
#[derive(Clone, PartialEq, Hash, Eq)]
pub enum BooleanExpression<'ast, T: Field> {
    Identifier(Identifier<'ast>),
    Value(bool),
    Lt(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    Le(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    Eq(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    Ge(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    Gt(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    Or(
        Box<BooleanExpression<'ast, T>>,
        Box<BooleanExpression<'ast, T>>,
    ),
    And(
        Box<BooleanExpression<'ast, T>>,
        Box<BooleanExpression<'ast, T>>,
    ),
    Not(Box<BooleanExpression<'ast, T>>),
}

/// An expression of type `field[n]
/// # Remarks
/// * for now we store the array size in the variants
#[derive(Clone, PartialEq, Hash, Eq)]
pub enum FieldElementArrayExpression<'ast, T: Field> {
    Identifier(usize, Identifier<'ast>),
    Value(usize, TypedArrayValue<'ast, T>),
    FunctionCall(usize, FunctionKey<'ast>, Vec<TypedExpression<'ast, T>>),
    IfElse(
        Box<BooleanExpression<'ast, T>>,
        Box<FieldElementArrayExpression<'ast, T>>,
        Box<FieldElementArrayExpression<'ast, T>>,
    ),
    Slice(Box<FieldElementArrayExpression<'ast, T>>, usize, usize),
}

#[derive(Clone, PartialEq, Hash, Eq)]
pub struct TypedArrayValue<'ast, T: Field>(pub Vec<TypedSpreadOrExpression<'ast, T>>);

impl<'ast, T: Field> fmt::Display for TypedArrayValue<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            self.0
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl<'ast, T: Field> fmt::Debug for TypedArrayValue<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{:?}",
            self.0
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl<'ast, T: Field> TypedArrayValue<'ast, T> {
    pub fn len(&self) -> usize {
        self.0
            .iter()
            .map(|v| match v {
                TypedSpreadOrExpression::Expression(_) => 1,
                TypedSpreadOrExpression::Spread(v) => v.size(),
            })
            .sum()
    }

    pub fn get(&self, index: usize) -> TypedExpression<'ast, T> {
        let mut i = 0;
        for v in &self.0 {
            match v {
                TypedSpreadOrExpression::Expression(e) => {
                    if index == i {
                        return e.clone();
                    } else {
                        i = i + 1;
                    }
                }
                TypedSpreadOrExpression::Spread(v) => {
                    let size = v.size();
                    if i + size <= index {
                        return FieldElementExpression::Select(
                            box v.clone(),
                            box FieldElementExpression::Number(T::from(index - i)),
                        )
                        .into();
                    } else {
                        i = i + size
                    }
                }
            };
        }
        unreachable!()
    }

    pub fn slice(self, from: usize, to: usize) -> Self {
        let mut i = 0;
        let mut res = vec![];
        for v in self.0 {
            match v {
                TypedSpreadOrExpression::Expression(e) => {
                    if i >= from && i < to {
                        res.push(TypedSpreadOrExpression::Expression(e))
                    };
                    i = i + 1;
                }
                TypedSpreadOrExpression::Spread(v) => {
                    // we're looking for the overlap between this spread and [from, to[
                    let size = v.size();
                    let (spread_from, spread_to) = (i, i + size);
                    let from = std::cmp::max(spread_from, from);
                    let to = std::cmp::min(spread_to, to);

                    if from < to {
                        res.push(TypedSpreadOrExpression::Spread(
                            FieldElementArrayExpression::Slice(box v, from, to),
                        ));
                    }

                    i = i + size;
                }
            };
        }

        let res = TypedArrayValue(res);
        assert_eq!(res.len(), to - from);
        println!("SLICE OUTPUT {}", res);
        res
    }
}

#[derive(Clone, PartialEq, Hash, Eq)]
pub enum TypedSpreadOrExpression<'ast, T: Field> {
    Spread(FieldElementArrayExpression<'ast, T>),
    Expression(TypedExpression<'ast, T>),
}

impl<'ast, T: Field> fmt::Display for TypedSpreadOrExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedSpreadOrExpression::Spread(ref a) => write!(f, "...{}", a),
            TypedSpreadOrExpression::Expression(ref e) => write!(f, "{}", e),
        }
    }
}

impl<'ast, T: Field> fmt::Debug for TypedSpreadOrExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedSpreadOrExpression::Spread(ref a) => write!(f, "{:?}", a),
            TypedSpreadOrExpression::Expression(ref e) => write!(f, "{:?}", e),
        }
    }
}

impl<'ast, T: Field> Typed for TypedSpreadOrExpression<'ast, T> {
    fn get_type(&self) -> Type {
        match *self {
            TypedSpreadOrExpression::Expression(ref e) => e.get_type(),
            TypedSpreadOrExpression::Spread(_) => Type::FieldElement,
        }
    }
}

impl<'ast, T: Field> FieldElementArrayExpression<'ast, T> {
    pub fn size(&self) -> usize {
        match *self {
            FieldElementArrayExpression::Identifier(s, _)
            | FieldElementArrayExpression::Value(s, _)
            | FieldElementArrayExpression::FunctionCall(s, ..) => s,
            FieldElementArrayExpression::IfElse(_, ref consequence, _) => consequence.size(),
            FieldElementArrayExpression::Slice(_, f, t) => t - f,
        }
    }
}

impl<'ast, T: Field> fmt::Display for FieldElementExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FieldElementExpression::Number(ref i) => write!(f, "{}", i),
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
                r#try!(write!(f, "{}(", k.id,));
                for (i, param) in p.iter().enumerate() {
                    r#try!(write!(f, "{}", param));
                    if i < p.len() - 1 {
                        r#try!(write!(f, ", "));
                    }
                }
                write!(f, ")")
            }
            FieldElementExpression::Select(ref id, ref index) => write!(f, "{}[{}]", id, index),
        }
    }
}

impl<'ast, T: Field> fmt::Display for BooleanExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            BooleanExpression::Identifier(ref var) => write!(f, "{}", var),
            BooleanExpression::Lt(ref lhs, ref rhs) => write!(f, "{} < {}", lhs, rhs),
            BooleanExpression::Le(ref lhs, ref rhs) => write!(f, "{} <= {}", lhs, rhs),
            BooleanExpression::Eq(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            BooleanExpression::Ge(ref lhs, ref rhs) => write!(f, "{} >= {}", lhs, rhs),
            BooleanExpression::Gt(ref lhs, ref rhs) => write!(f, "{} > {}", lhs, rhs),
            BooleanExpression::Or(ref lhs, ref rhs) => write!(f, "{} || {}", lhs, rhs),
            BooleanExpression::And(ref lhs, ref rhs) => write!(f, "{} && {}", lhs, rhs),
            BooleanExpression::Not(ref exp) => write!(f, "!{}", exp),
            BooleanExpression::Value(b) => write!(f, "{}", b),
        }
    }
}

impl<'ast, T: Field> fmt::Display for FieldElementArrayExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FieldElementArrayExpression::Identifier(_, ref var) => write!(f, "{}", var),
            FieldElementArrayExpression::Value(_, ref values) => write!(
                f,
                "[{}]",
                values
                    .0
                    .iter()
                    .map(|o| o.to_string())
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            FieldElementArrayExpression::FunctionCall(_, ref key, ref p) => {
                r#try!(write!(f, "{}(", key.id,));
                for (i, param) in p.iter().enumerate() {
                    r#try!(write!(f, "{}", param));
                    if i < p.len() - 1 {
                        r#try!(write!(f, ", "));
                    }
                }
                write!(f, ")")
            }
            FieldElementArrayExpression::IfElse(ref condition, ref consequent, ref alternative) => {
                write!(
                    f,
                    "if {} then {} else {} fi",
                    condition, consequent, alternative
                )
            }
            FieldElementArrayExpression::Slice(ref a, ref from, ref to) => {
                write!(f, "{}[{}..{}]", a, from, to)
            }
        }
    }
}

impl<'ast, T: Field> fmt::Debug for BooleanExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl<'ast, T: Field> fmt::Debug for FieldElementExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FieldElementExpression::Number(ref i) => write!(f, "Num({})", i),
            FieldElementExpression::Identifier(ref var) => write!(f, "Ide({})", var),
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
                r#try!(write!(f, "FunctionCall({:?}, (", i));
                r#try!(f.debug_list().entries(p.iter()).finish());
                write!(f, ")")
            }
            FieldElementExpression::Select(ref id, ref index) => {
                write!(f, "Select({:?}, {:?})", id, index)
            }
        }
    }
}

impl<'ast, T: Field> fmt::Debug for FieldElementArrayExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FieldElementArrayExpression::Identifier(_, ref var) => write!(f, "{:?}", var),
            FieldElementArrayExpression::Value(_, ref values) => write!(f, "{:?}", values),
            FieldElementArrayExpression::FunctionCall(_, ref i, ref p) => {
                r#try!(write!(f, "FunctionCall({:?}, (", i));
                r#try!(f.debug_list().entries(p.iter()).finish());
                write!(f, ")")
            }
            FieldElementArrayExpression::IfElse(ref condition, ref consequent, ref alternative) => {
                write!(
                    f,
                    "IfElse({:?}, {:?}, {:?})",
                    condition, consequent, alternative
                )
            }
            FieldElementArrayExpression::Slice(ref a, ref from, ref to) => {
                write!(f, "Slice({:?}, {:?}, {:?})", a, from, to)
            }
        }
    }
}

impl<'ast, T: Field> fmt::Display for TypedExpressionList<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedExpressionList::FunctionCall(ref key, ref p, _) => {
                r#try!(write!(f, "{}(", key.id,));
                for (i, param) in p.iter().enumerate() {
                    r#try!(write!(f, "{}", param));
                    if i < p.len() - 1 {
                        r#try!(write!(f, ", "));
                    }
                }
                write!(f, ")")
            }
        }
    }
}

impl<'ast, T: Field> fmt::Debug for TypedExpressionList<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedExpressionList::FunctionCall(ref i, ref p, _) => {
                r#try!(write!(f, "FunctionCall({:?}, (", i));
                r#try!(f.debug_list().entries(p.iter()).finish());
                write!(f, ")")
            }
        }
    }
}
