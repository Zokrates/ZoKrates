//! Module containing structs and enums to represent a program.
//!
//! @file absy.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

mod from_ast;
mod node;
pub mod parameter;
pub mod variable;

pub use crate::absy::node::{Node, NodeValue};
pub use crate::absy::parameter::{Parameter, ParameterNode};
pub use crate::absy::variable::{Variable, VariableNode};
use crate::types::Signature;

use crate::flat_absy::*;
use crate::imports::ImportNode;
use std::fmt;
use zokrates_field::field::Field;

pub type Identifier<'ast> = &'ast str;

#[derive(Clone, PartialEq)]
pub struct Prog<'ast, T: Field> {
    /// Functions of the program
    pub functions: Vec<FunctionNode<'ast, T>>,
    pub imports: Vec<ImportNode>,
    pub imported_functions: Vec<FlatFunction<T>>,
}

impl<'ast, T: Field> fmt::Display for Prog<'ast, T> {
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

impl<'ast, T: Field> fmt::Debug for Prog<'ast, T> {
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
pub struct Function<'ast, T: Field> {
    /// Name of the program
    pub id: Identifier<'ast>,
    /// Arguments of the function
    pub arguments: Vec<ParameterNode<'ast>>,
    /// Vector of statements that are executed when running the function
    pub statements: Vec<StatementNode<'ast, T>>,
    /// function signature
    pub signature: Signature,
}

pub type FunctionNode<'ast, T> = Node<Function<'ast, T>>;

impl<'ast, T: Field> fmt::Display for Function<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "def {}({}):\n{}",
            self.id,
            self.arguments
                .iter()
                .map(|x| format!("{}", x))
                .collect::<Vec<_>>()
                .join(","),
            self.statements
                .iter()
                .map(|x| format!("\t{}", x))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

impl<'ast, T: Field> fmt::Debug for Function<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Function(id: {:?}, arguments: {:?}, ...):\n{}",
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

#[derive(Clone, PartialEq)]
pub enum Assignee<'ast, T: Field> {
    Identifier(Identifier<'ast>),
    ArrayElement(Box<AssigneeNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
}

pub type AssigneeNode<'ast, T> = Node<Assignee<'ast, T>>;

impl<'ast, T: Field> fmt::Debug for Assignee<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Assignee::Identifier(ref s) => write!(f, "{}", s),
            Assignee::ArrayElement(ref a, ref e) => write!(f, "{}[{}]", a, e),
        }
    }
}

impl<'ast, T: Field> fmt::Display for Assignee<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Clone, PartialEq)]
pub enum Statement<'ast, T: Field> {
    Return(ExpressionListNode<'ast, T>),
    Declaration(VariableNode<'ast>),
    Definition(AssigneeNode<'ast, T>, ExpressionNode<'ast, T>),
    Condition(ExpressionNode<'ast, T>, ExpressionNode<'ast, T>),
    For(VariableNode<'ast>, T, T, Vec<StatementNode<'ast, T>>),
    MultipleDefinition(Vec<AssigneeNode<'ast, T>>, ExpressionNode<'ast, T>),
}

pub type StatementNode<'ast, T> = Node<Statement<'ast, T>>;

impl<'ast, T: Field> fmt::Display for Statement<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Statement::Return(ref expr) => write!(f, "return {}", expr),
            Statement::Declaration(ref var) => write!(f, "{}", var),
            Statement::Definition(ref lhs, ref rhs) => write!(f, "{} = {}", lhs, rhs),
            Statement::Condition(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            Statement::For(ref var, ref start, ref stop, ref list) => {
                r#try!(write!(f, "for {} in {}..{} do\n", var, start, stop));
                for l in list {
                    r#try!(write!(f, "\t\t{}\n", l));
                }
                write!(f, "\tendfor")
            }
            Statement::MultipleDefinition(ref ids, ref rhs) => {
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

impl<'ast, T: Field> fmt::Debug for Statement<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Statement::Return(ref expr) => write!(f, "Return({:?})", expr),
            Statement::Declaration(ref var) => write!(f, "Declaration({:?})", var),
            Statement::Definition(ref lhs, ref rhs) => {
                write!(f, "Definition({:?}, {:?})", lhs, rhs)
            }
            Statement::Condition(ref lhs, ref rhs) => write!(f, "Condition({:?}, {:?})", lhs, rhs),
            Statement::For(ref var, ref start, ref stop, ref list) => {
                r#try!(write!(f, "for {:?} in {:?}..{:?} do\n", var, start, stop));
                for l in list {
                    r#try!(write!(f, "\t\t{:?}\n", l));
                }
                write!(f, "\tendfor")
            }
            Statement::MultipleDefinition(ref lhs, ref rhs) => {
                write!(f, "MultipleDefinition({:?}, {:?})", lhs, rhs)
            }
        }
    }
}

#[derive(Clone, PartialEq)]
pub enum Expression<'ast, T: Field> {
    Number(T),
    Identifier(Identifier<'ast>),
    Add(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
    Sub(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
    Mult(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
    Div(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
    Pow(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
    IfElse(
        Box<ExpressionNode<'ast, T>>,
        Box<ExpressionNode<'ast, T>>,
        Box<ExpressionNode<'ast, T>>,
    ),
    FunctionCall(String, Vec<ExpressionNode<'ast, T>>),
    Lt(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
    Le(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
    Eq(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
    Ge(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
    Gt(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
    And(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
    Not(Box<ExpressionNode<'ast, T>>),
    InlineArray(Vec<ExpressionNode<'ast, T>>),
    Select(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
    Or(Box<ExpressionNode<'ast, T>>, Box<ExpressionNode<'ast, T>>),
}

pub type ExpressionNode<'ast, T> = Node<Expression<'ast, T>>;

impl<'ast, T: Field> fmt::Display for Expression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Expression::Number(ref i) => write!(f, "{}", i),
            Expression::Identifier(ref var) => write!(f, "{}", var),
            Expression::Add(ref lhs, ref rhs) => write!(f, "({} + {})", lhs, rhs),
            Expression::Sub(ref lhs, ref rhs) => write!(f, "({} - {})", lhs, rhs),
            Expression::Mult(ref lhs, ref rhs) => write!(f, "({} * {})", lhs, rhs),
            Expression::Div(ref lhs, ref rhs) => write!(f, "({} / {})", lhs, rhs),
            Expression::Pow(ref lhs, ref rhs) => write!(f, "{}**{}", lhs, rhs),
            Expression::IfElse(ref condition, ref consequent, ref alternative) => write!(
                f,
                "if {} then {} else {} fi",
                condition, consequent, alternative
            ),
            Expression::FunctionCall(ref i, ref p) => {
                r#try!(write!(f, "{}(", i,));
                for (i, param) in p.iter().enumerate() {
                    r#try!(write!(f, "{}", param));
                    if i < p.len() - 1 {
                        r#try!(write!(f, ", "));
                    }
                }
                write!(f, ")")
            }
            Expression::Lt(ref lhs, ref rhs) => write!(f, "{} < {}", lhs, rhs),
            Expression::Le(ref lhs, ref rhs) => write!(f, "{} <= {}", lhs, rhs),
            Expression::Eq(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            Expression::Ge(ref lhs, ref rhs) => write!(f, "{} >= {}", lhs, rhs),
            Expression::Gt(ref lhs, ref rhs) => write!(f, "{} > {}", lhs, rhs),
            Expression::And(ref lhs, ref rhs) => write!(f, "{} && {}", lhs, rhs),
            Expression::Not(ref exp) => write!(f, "!{}", exp),
            Expression::InlineArray(ref exprs) => {
                r#try!(write!(f, "["));
                for (i, e) in exprs.iter().enumerate() {
                    r#try!(write!(f, "{}", e));
                    if i < exprs.len() - 1 {
                        r#try!(write!(f, ", "));
                    }
                }
                write!(f, "]")
            }
            Expression::Select(ref array, ref index) => write!(f, "{}[{}]", array, index),
            Expression::Or(ref lhs, ref rhs) => write!(f, "{} || {}", lhs, rhs),
        }
    }
}

impl<'ast, T: Field> fmt::Debug for Expression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Expression::Number(ref i) => write!(f, "Num({})", i),
            Expression::Identifier(ref var) => write!(f, "Ide({})", var),
            Expression::Add(ref lhs, ref rhs) => write!(f, "Add({:?}, {:?})", lhs, rhs),
            Expression::Sub(ref lhs, ref rhs) => write!(f, "Sub({:?}, {:?})", lhs, rhs),
            Expression::Mult(ref lhs, ref rhs) => write!(f, "Mult({:?}, {:?})", lhs, rhs),
            Expression::Div(ref lhs, ref rhs) => write!(f, "Div({:?}, {:?})", lhs, rhs),
            Expression::Pow(ref lhs, ref rhs) => write!(f, "Pow({:?}, {:?})", lhs, rhs),
            Expression::IfElse(ref condition, ref consequent, ref alternative) => write!(
                f,
                "IfElse({:?}, {:?}, {:?})",
                condition, consequent, alternative
            ),
            Expression::FunctionCall(ref i, ref p) => {
                r#try!(write!(f, "FunctionCall({:?}, (", i));
                r#try!(f.debug_list().entries(p.iter()).finish());
                write!(f, ")")
            }
            Expression::Lt(ref lhs, ref rhs) => write!(f, "{} < {}", lhs, rhs),
            Expression::Le(ref lhs, ref rhs) => write!(f, "{} <= {}", lhs, rhs),
            Expression::Eq(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            Expression::Ge(ref lhs, ref rhs) => write!(f, "{} >= {}", lhs, rhs),
            Expression::Gt(ref lhs, ref rhs) => write!(f, "{} > {}", lhs, rhs),
            Expression::And(ref lhs, ref rhs) => write!(f, "{} && {}", lhs, rhs),
            Expression::Not(ref exp) => write!(f, "!{}", exp),
            Expression::InlineArray(ref exprs) => {
                r#try!(write!(f, "InlineArray(["));
                r#try!(f.debug_list().entries(exprs.iter()).finish());
                write!(f, "]")
            }
            Expression::Select(ref array, ref index) => write!(f, "{}[{}]", array, index),
            Expression::Or(ref lhs, ref rhs) => write!(f, "{} || {}", lhs, rhs),
        }
    }
}

#[derive(Clone, PartialEq)]
pub struct ExpressionList<'ast, T: Field> {
    pub expressions: Vec<ExpressionNode<'ast, T>>,
}

pub type ExpressionListNode<'ast, T> = Node<ExpressionList<'ast, T>>;

impl<'ast, T: Field> ExpressionList<'ast, T> {
    pub fn new() -> ExpressionList<'ast, T> {
        ExpressionList {
            expressions: vec![],
        }
    }
}

impl<'ast, T: Field> fmt::Display for ExpressionList<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, param) in self.expressions.iter().enumerate() {
            r#try!(write!(f, "{}", param));
            if i < self.expressions.len() - 1 {
                r#try!(write!(f, ", "));
            }
        }
        write!(f, "")
    }
}

impl<'ast, T: Field> fmt::Debug for ExpressionList<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ExpressionList({:?})", self.expressions)
    }
}
