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
use crate::types::Signature;

use crate::flat_absy::*;
use crate::imports::Import;
use crate::types::Type;
use std::fmt;
use zokrates_field::field::Field;

pub use self::folder::Folder;

#[derive(Debug, PartialEq, Clone, Hash, Eq)]
pub struct Identifier<'ast> {
    pub id: &'ast str,
    pub version: usize,
    pub stack: Vec<(&'ast str, Signature, usize)>,
}

pub type FunctionIdentifier<'ast> = &'ast str;

impl<'ast> fmt::Display for Identifier<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.id,)
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
}

#[derive(Clone, PartialEq)]
pub struct TypedProg<'ast, T: Field> {
    /// Functions of the program
    pub functions: Vec<TypedFunction<'ast, T>>,
    pub imports: Vec<Import>,
    pub imported_functions: Vec<FlatFunction<T>>,
}

impl<'ast, T: Field> fmt::Display for TypedProg<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut res = vec![];
        res.extend(
            self.imports
                .iter()
                .map(|x| format!("{}", x))
                .collect::<Vec<_>>(),
        );
        res.extend(
            self.imported_functions
                .iter()
                .map(|x| format!("{}", x))
                .collect::<Vec<_>>(),
        );
        res.extend(
            self.functions
                .iter()
                .map(|x| format!("{}", x))
                .collect::<Vec<_>>(),
        );
        write!(f, "{}", res.join("\n"))
    }
}

impl<'ast, T: Field> fmt::Debug for TypedProg<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "program(\n\timports:\n\t\t{}\n\tfunctions:\n\t\t{}{}\n)",
            self.imports
                .iter()
                .map(|x| format!("{:?}", x))
                .collect::<Vec<_>>()
                .join("\n\t\t"),
            self.imported_functions
                .iter()
                .map(|x| format!("{}", x))
                .collect::<Vec<_>>()
                .join("\n\t\t"),
            self.functions
                .iter()
                .map(|x| format!("{:?}", x))
                .collect::<Vec<_>>()
                .join("\n\t\t")
        )
    }
}

#[derive(Clone, PartialEq)]
pub struct TypedFunction<'ast, T: Field> {
    /// Name of the program
    pub id: FunctionIdentifier<'ast>,
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
            "def {}({}) -> ({}):\n{}",
            self.id,
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
            "TypedFunction(id: {:?}, arguments: {:?}, ...):\n{}",
            self.id,
            self.arguments,
            self.statements
                .iter()
                .map(|x| format!("\t{:?}", x))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

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
        }
    }
}

pub trait MultiTyped {
    fn get_types(&self) -> &Vec<Type>;
}

#[derive(Clone, PartialEq)]
pub enum TypedExpressionList<'ast, T: Field> {
    FunctionCall(String, Vec<TypedExpression<'ast, T>>, Vec<Type>),
}

impl<'ast, T: Field> MultiTyped for TypedExpressionList<'ast, T> {
    fn get_types(&self) -> &Vec<Type> {
        match *self {
            TypedExpressionList::FunctionCall(_, _, ref types) => types,
        }
    }
}

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
    FunctionCall(String, Vec<TypedExpression<'ast, T>>),
    Select(
        Box<FieldElementArrayExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
}

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

// for now we store the array size in the variants
#[derive(Clone, PartialEq, Hash, Eq)]
pub enum FieldElementArrayExpression<'ast, T: Field> {
    Identifier(usize, Identifier<'ast>),
    Value(usize, Vec<FieldElementExpression<'ast, T>>),
    FunctionCall(usize, String, Vec<TypedExpression<'ast, T>>),
    IfElse(
        Box<BooleanExpression<'ast, T>>,
        Box<FieldElementArrayExpression<'ast, T>>,
        Box<FieldElementArrayExpression<'ast, T>>,
    ),
}

impl<'ast, T: Field> FieldElementArrayExpression<'ast, T> {
    pub fn size(&self) -> usize {
        match *self {
            FieldElementArrayExpression::Identifier(s, _)
            | FieldElementArrayExpression::Value(s, _)
            | FieldElementArrayExpression::FunctionCall(s, ..) => s,
            FieldElementArrayExpression::IfElse(_, ref consequence, _) => consequence.size(),
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
            FieldElementExpression::FunctionCall(ref i, ref p) => {
                r#try!(write!(f, "{}(", i,));
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
                    .iter()
                    .map(|o| o.to_string())
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            FieldElementArrayExpression::FunctionCall(_, ref i, ref p) => {
                r#try!(write!(f, "{}(", i,));
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
        }
    }
}

impl<'ast, T: Field> fmt::Display for TypedExpressionList<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedExpressionList::FunctionCall(ref i, ref p, _) => {
                r#try!(write!(f, "{}(", i,));
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

impl<'ast, T: Field> TypedFunction<'ast, T> {
    pub fn to_slug(&self) -> String {
        format!("{}_{}", self.id, self.signature.to_slug())
    }
}
