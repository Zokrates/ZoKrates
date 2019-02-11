//! Module containing structs and enums to represent a program.
//!
//! @file absy.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

mod node;
pub mod parameter;
pub mod variable;

pub use absy::node::{Node, NodeValue};
pub use absy::parameter::{Parameter, ParameterNode};
pub use absy::variable::{Variable, VariableNode};
use types::Signature;

use flat_absy::*;
use imports::ImportNode;
use std::fmt;
use zokrates_field::field::Field;

#[derive(Clone, PartialEq)]
pub struct Prog<T: Field> {
    /// Functions of the program
    pub functions: Vec<FunctionNode<T>>,
    pub imports: Vec<ImportNode>,
    pub imported_functions: Vec<FlatFunction<T>>,
}

impl<T: Field> fmt::Display for Prog<T> {
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

impl<T: Field> fmt::Debug for Prog<T> {
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
pub struct Function<T: Field> {
    /// Name of the program
    pub id: String,
    /// Arguments of the function
    pub arguments: Vec<ParameterNode>,
    /// Vector of statements that are executed when running the function
    pub statements: Vec<StatementNode<T>>,
    /// function signature
    pub signature: Signature,
}

pub type FunctionNode<T> = Node<Function<T>>;

impl<T: Field> fmt::Display for Function<T> {
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

impl<T: Field> fmt::Debug for Function<T> {
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
pub enum Assignee<T: Field> {
    Identifier(String),
    ArrayElement(Box<AssigneeNode<T>>, Box<ExpressionNode<T>>),
}

pub type AssigneeNode<T> = Node<Assignee<T>>;

impl<T: Field> fmt::Debug for Assignee<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Assignee::Identifier(ref s) => write!(f, "{}", s),
            Assignee::ArrayElement(ref a, ref e) => write!(f, "{}[{}]", a, e),
        }
    }
}

impl<T: Field> fmt::Display for Assignee<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl<T: Field> From<ExpressionNode<T>> for AssigneeNode<T> {
    fn from(e: ExpressionNode<T>) -> Self {
        match e.value {
            Expression::Select(box e1, box e2) => match e1 {
                ExpressionNode {
                    value: Expression::Identifier(id),
                    start,
                    end,
                } => Node::new(
                    e.start,
                    e.end,
                    Assignee::ArrayElement(
                        box Node::new(start, end, Assignee::Identifier(id)),
                        box e2,
                    ),
                ),
                _ => panic!("only use expression to assignee for elements like foo[bar]"),
            },
            _ => panic!("only use expression to assignee for elements like foo[bar]"),
        }
    }
}

#[derive(Clone, PartialEq)]
pub enum Statement<T: Field> {
    Return(ExpressionListNode<T>),
    Declaration(VariableNode),
    Definition(AssigneeNode<T>, ExpressionNode<T>),
    Condition(ExpressionNode<T>, ExpressionNode<T>),
    For(VariableNode, T, T, Vec<StatementNode<T>>),
    MultipleDefinition(Vec<AssigneeNode<T>>, ExpressionNode<T>),
}

pub type StatementNode<T> = Node<Statement<T>>;

impl<T: Field> fmt::Display for Statement<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Statement::Return(ref expr) => write!(f, "return {}", expr),
            Statement::Declaration(ref var) => write!(f, "{}", var),
            Statement::Definition(ref lhs, ref rhs) => write!(f, "{} = {}", lhs, rhs),
            Statement::Condition(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            Statement::For(ref var, ref start, ref stop, ref list) => {
                try!(write!(f, "for {} in {}..{} do\n", var, start, stop));
                for l in list {
                    try!(write!(f, "\t\t{}\n", l));
                }
                write!(f, "\tendfor")
            }
            Statement::MultipleDefinition(ref ids, ref rhs) => {
                for (i, id) in ids.iter().enumerate() {
                    try!(write!(f, "{}", id));
                    if i < ids.len() - 1 {
                        try!(write!(f, ", "));
                    }
                }
                write!(f, " = {}", rhs)
            }
        }
    }
}

impl<T: Field> fmt::Debug for Statement<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Statement::Return(ref expr) => write!(f, "Return({:?})", expr),
            Statement::Declaration(ref var) => write!(f, "Declaration({:?})", var),
            Statement::Definition(ref lhs, ref rhs) => {
                write!(f, "Definition({:?}, {:?})", lhs, rhs)
            }
            Statement::Condition(ref lhs, ref rhs) => write!(f, "Condition({:?}, {:?})", lhs, rhs),
            Statement::For(ref var, ref start, ref stop, ref list) => {
                try!(write!(f, "for {:?} in {:?}..{:?} do\n", var, start, stop));
                for l in list {
                    try!(write!(f, "\t\t{:?}\n", l));
                }
                write!(f, "\tendfor")
            }
            Statement::MultipleDefinition(ref lhs, ref rhs) => {
                write!(f, "MultipleDefinition({:?}, {:?})", lhs, rhs)
            }
        }
    }
}

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub enum Expression<T: Field> {
    Number(T),
    Identifier(String),
    Add(Box<ExpressionNode<T>>, Box<ExpressionNode<T>>),
    Sub(Box<ExpressionNode<T>>, Box<ExpressionNode<T>>),
    Mult(Box<ExpressionNode<T>>, Box<ExpressionNode<T>>),
    Div(Box<ExpressionNode<T>>, Box<ExpressionNode<T>>),
    Pow(Box<ExpressionNode<T>>, Box<ExpressionNode<T>>),
    IfElse(
        Box<ExpressionNode<T>>,
        Box<ExpressionNode<T>>,
        Box<ExpressionNode<T>>,
    ),
    FunctionCall(String, Vec<ExpressionNode<T>>),
    Lt(Box<ExpressionNode<T>>, Box<ExpressionNode<T>>),
    Le(Box<ExpressionNode<T>>, Box<ExpressionNode<T>>),
    Eq(Box<ExpressionNode<T>>, Box<ExpressionNode<T>>),
    Ge(Box<ExpressionNode<T>>, Box<ExpressionNode<T>>),
    Gt(Box<ExpressionNode<T>>, Box<ExpressionNode<T>>),
    And(Box<ExpressionNode<T>>, Box<ExpressionNode<T>>),
    Not(Box<ExpressionNode<T>>),
    InlineArray(Vec<ExpressionNode<T>>),
    Select(Box<ExpressionNode<T>>, Box<ExpressionNode<T>>),
    Or(Box<ExpressionNode<T>>, Box<ExpressionNode<T>>),
}

pub type ExpressionNode<T> = Node<Expression<T>>;

impl<T: Field> fmt::Display for Expression<T> {
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
                try!(write!(f, "{}(", i,));
                for (i, param) in p.iter().enumerate() {
                    try!(write!(f, "{}", param));
                    if i < p.len() - 1 {
                        try!(write!(f, ", "));
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
                try!(write!(f, "["));
                for (i, e) in exprs.iter().enumerate() {
                    try!(write!(f, "{}", e));
                    if i < exprs.len() - 1 {
                        try!(write!(f, ", "));
                    }
                }
                write!(f, "]")
            }
            Expression::Select(ref array, ref index) => write!(f, "{}[{}]", array, index),
            Expression::Or(ref lhs, ref rhs) => write!(f, "{} || {}", lhs, rhs),
        }
    }
}

impl<T: Field> fmt::Debug for Expression<T> {
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
                try!(write!(f, "FunctionCall({:?}, (", i));
                try!(f.debug_list().entries(p.iter()).finish());
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
                try!(write!(f, "InlineArray(["));
                try!(f.debug_list().entries(exprs.iter()).finish());
                write!(f, "]")
            }
            Expression::Select(ref array, ref index) => write!(f, "{}[{}]", array, index),
            Expression::Or(ref lhs, ref rhs) => write!(f, "{} || {}", lhs, rhs),
        }
    }
}

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub struct ExpressionList<T: Field> {
    pub expressions: Vec<ExpressionNode<T>>,
}

pub type ExpressionListNode<T> = Node<ExpressionList<T>>;

impl<T: Field> ExpressionList<T> {
    pub fn new() -> ExpressionList<T> {
        ExpressionList {
            expressions: vec![],
        }
    }
}

impl<T: Field> fmt::Display for ExpressionList<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, param) in self.expressions.iter().enumerate() {
            try!(write!(f, "{}", param));
            if i < self.expressions.len() - 1 {
                try!(write!(f, ", "));
            }
        }
        write!(f, "")
    }
}

impl<T: Field> fmt::Debug for ExpressionList<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ExpressionList({:?})", self.expressions)
    }
}
