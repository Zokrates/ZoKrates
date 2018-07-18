//! Module containing structs and enums to represent a program.
//!
//! @file absy.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

pub mod parameter;
pub mod variable;

use types::signature::Signature;
use absy::parameter::Parameter;
use absy::variable::Variable;

use std::fmt;
use substitution::Substitution;
use field::Field;
use imports::Import;
use flat_absy::*;
use types::field_element::*;
use types::Type;

#[derive(Serialize, Deserialize, Clone, PartialEq)]
pub struct Prog<T: Field> {
    /// Functions of the program
    pub functions: Vec<Function<T>>,
    pub imports: Vec<Import>,
    pub imported_functions: Vec<FlatFunction<T>>
}

impl<T: Field> fmt::Display for Prog<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut res = vec![];
        res.extend(self.imports
                .iter()
                .map(|x| format!("{}", x))
                .collect::<Vec<_>>());
        res.extend(self.imported_functions
                .iter()
                .map(|x| format!("{}", x))
                .collect::<Vec<_>>());
        res.extend(self.functions
                .iter()
                .map(|x| format!("{}", x))
                .collect::<Vec<_>>());
        write!(
            f,
            "{}",
            res.join("\n")
        )
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

#[derive(Serialize, Deserialize, Clone, PartialEq)]
pub struct Function<T: Field> {
    /// Name of the program
    pub id: String,
    /// Arguments of the function
    pub arguments: Vec<Parameter>,
    /// Vector of statements that are executed when running the function
    pub statements: Vec<Statement<T>>,
    /// function signature
    pub signature: Signature,
}

impl<T: Field> Function<T> {
    pub fn return_count(&self) -> usize {
        self.signature.outputs.len()
    }
}

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

// TODO impl debug

#[derive(Clone, Serialize, Deserialize, PartialEq)]
pub enum Statement<T: Field> {
    Return(ExpressionList<T>),
    Definition(Variable, Expression<T>),
    Condition(Expression<T>, Expression<T>),
    For(Variable, T, T, Vec<Statement<T>>),
    MultipleDefinition(Vec<Variable>, Expression<T>),
}

impl<T: Field> fmt::Display for Statement<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Statement::Return(ref expr) => write!(f, "return {}", expr),
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
            },
        }
    }
}

impl<T: Field> fmt::Debug for Statement<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Statement::Return(ref expr) => write!(f, "Return({:?})", expr),
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
            },
        }
    }
}

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub enum Expression<T: Field> {
    Number(T),
    Identifier(String),
    Add(Box<Expression<T>>, Box<Expression<T>>),
    Sub(Box<Expression<T>>, Box<Expression<T>>),
    Mult(Box<Expression<T>>, Box<Expression<T>>),
    Div(Box<Expression<T>>, Box<Expression<T>>),
    Pow(Box<Expression<T>>, Box<Expression<T>>),
    IfElse(Box<Condition<T>>, Box<Expression<T>>, Box<Expression<T>>),
    FunctionCall(String, Vec<Expression<T>>),
}

impl<T: Field> Expression<T> {
    pub fn apply_substitution(&self, substitution: &Substitution) -> Expression<T> {
        match *self {
            ref e @ Expression::Number(_) => e.clone(),
            Expression::Identifier(ref id) => {
                let mut new_name = id.clone();
                loop {
                    match substitution.get(&new_name) {
                        Some(x) => new_name = x.to_string(),
                        None => return Expression::Identifier(new_name),
                    }
                }
            }
            Expression::Add(ref e1, ref e2) => Expression::Add(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            Expression::Sub(ref e1, ref e2) => Expression::Sub(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            Expression::Mult(ref e1, ref e2) => Expression::Mult(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            Expression::Div(ref e1, ref e2) => Expression::Div(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            Expression::Pow(ref e1, ref e2) => Expression::Pow(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            Expression::IfElse(ref c, ref e1, ref e2) => Expression::IfElse(
                box c.apply_substitution(substitution),
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            Expression::FunctionCall(ref i, ref p) => {
                for param in p {
                    param.apply_substitution(substitution);
                }
                Expression::FunctionCall(i.clone(), p.clone())
            },
        }
    }

    pub fn is_linear(&self) -> bool {
        match *self {
            Expression::Number(_) | Expression::Identifier(_) => true,
            Expression::Add(ref x, ref y) | Expression::Sub(ref x, ref y) => {
                x.is_linear() && y.is_linear()
            },
            Expression::Mult(ref x, ref y) | Expression::Div(ref x, ref y) => {
                match (x, y) {
                    (box Expression::Number(_), box Expression::Number(_)) |
                    (box Expression::Number(_), box Expression::Identifier(_)) |
                    (box Expression::Identifier(_), box Expression::Number(_)) => true,
                    _ => false,
                }
            },
            _ => false,
        }
    }
}

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
                condition,
                consequent,
                alternative
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
            },
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
                condition,
                consequent,
                alternative
            ),
            Expression::FunctionCall(ref i, ref p) => {
                try!(write!(f, "FunctionCall({:?}, (", i));
                try!(f.debug_list().entries(p.iter()).finish());
                write!(f, ")")
            },
        }
    }
}

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub struct ExpressionList<T: Field> {
    pub expressions: Vec<Expression<T>>
}

impl<T: Field> ExpressionList<T> {
    pub fn new() -> ExpressionList<T> {
        ExpressionList {
            expressions: vec![]
        }
    }

    pub fn apply_substitution(&self, substitution: &Substitution) -> ExpressionList<T> {
        let expressions: Vec<Expression<T>> = self.expressions.iter().map(|e| e.apply_substitution(substitution)).collect();
        ExpressionList {
            expressions: expressions
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

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub enum Condition<T: Field> {
    Lt(Expression<T>, Expression<T>),
    Le(Expression<T>, Expression<T>),
    Eq(Expression<T>, Expression<T>),
    Ge(Expression<T>, Expression<T>),
    Gt(Expression<T>, Expression<T>),
}

impl<T: Field> Condition<T> {
    fn apply_substitution(&self, substitution: &Substitution) -> Condition<T> {
        match *self {
            Condition::Lt(ref lhs, ref rhs) => Condition::Lt(
                lhs.apply_substitution(substitution),
                rhs.apply_substitution(substitution),
            ),
            Condition::Le(ref lhs, ref rhs) => Condition::Le(
                lhs.apply_substitution(substitution),
                rhs.apply_substitution(substitution),
            ),
            Condition::Eq(ref lhs, ref rhs) => Condition::Eq(
                lhs.apply_substitution(substitution),
                rhs.apply_substitution(substitution),
            ),
            Condition::Ge(ref lhs, ref rhs) => Condition::Ge(
                lhs.apply_substitution(substitution),
                rhs.apply_substitution(substitution),
            ),
            Condition::Gt(ref lhs, ref rhs) => Condition::Gt(
                lhs.apply_substitution(substitution),
                rhs.apply_substitution(substitution),
            ),
        }
    }
}

impl<T: Field> fmt::Display for Condition<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Condition::Lt(ref lhs, ref rhs) => write!(f, "{} < {}", lhs, rhs),
            Condition::Le(ref lhs, ref rhs) => write!(f, "{} <= {}", lhs, rhs),
            Condition::Eq(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            Condition::Ge(ref lhs, ref rhs) => write!(f, "{} >= {}", lhs, rhs),
            Condition::Gt(ref lhs, ref rhs) => write!(f, "{} > {}", lhs, rhs),
        }
    }
}

impl<T: Field> fmt::Debug for Condition<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}
