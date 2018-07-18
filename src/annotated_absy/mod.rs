//! Module containing structs and enums to represent a program.
//!
//! @file absy.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

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
pub struct AnnotatedProg<T: Field> {
    /// Functions of the program
    pub functions: Vec<AnnotatedFunction<T>>,
    pub imports: Vec<Import>,
    pub imported_functions: Vec<FlatFunction<T>>
}

impl<T: Field> fmt::Display for AnnotatedProg<T> {
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

impl<T: Field> fmt::Debug for AnnotatedProg<T> {
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
pub struct AnnotatedFunction<T: Field> {
    /// Name of the program
    pub id: String,
    /// Arguments of the function
    pub arguments: Vec<Parameter>,
    /// Vector of statements that are executed when running the function
    pub statements: Vec<AnnotatedStatement<T>>,
    /// function signature
    pub signature: Signature,
}

impl<T: Field> AnnotatedFunction<T> {
    pub fn return_count(&self) -> usize {
        self.signature.outputs.len()
    }
}

impl<T: Field> fmt::Display for AnnotatedFunction<T> {
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

impl<T: Field> fmt::Debug for AnnotatedFunction<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "AnnotatedFunction(id: {:?}, arguments: {:?}, ...):\n{}",
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
pub enum AnnotatedStatement<T: Field> {
    Return(AnnotatedExpressionList<T>),
    Definition(Variable, AnnotatedExpression<T>),
    Condition(AnnotatedExpression<T>, AnnotatedExpression<T>),
    For(Variable, T, T, Vec<AnnotatedStatement<T>>),
    MultipleDefinition(Vec<Variable>, AnnotatedExpression<T>),
}

impl<T: Field> fmt::Display for AnnotatedStatement<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            AnnotatedStatement::Return(ref expr) => write!(f, "return {}", expr),
            AnnotatedStatement::Definition(ref lhs, ref rhs) => write!(f, "{} = {}", lhs, rhs),
            AnnotatedStatement::Condition(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            AnnotatedStatement::For(ref var, ref start, ref stop, ref list) => {
                try!(write!(f, "for {} in {}..{} do\n", var, start, stop));
                for l in list {
                    try!(write!(f, "\t\t{}\n", l));
                }
                write!(f, "\tendfor")
            }
            AnnotatedStatement::MultipleDefinition(ref ids, ref rhs) => {
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

impl<T: Field> fmt::Debug for AnnotatedStatement<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            AnnotatedStatement::Return(ref expr) => write!(f, "Return({:?})", expr),
            AnnotatedStatement::Definition(ref lhs, ref rhs) => {
                write!(f, "Definition({:?}, {:?})", lhs, rhs)
            }
            AnnotatedStatement::Condition(ref lhs, ref rhs) => write!(f, "Condition({:?}, {:?})", lhs, rhs),
            AnnotatedStatement::For(ref var, ref start, ref stop, ref list) => {
                try!(write!(f, "for {:?} in {:?}..{:?} do\n", var, start, stop));
                for l in list {
                    try!(write!(f, "\t\t{:?}\n", l));
                }
                write!(f, "\tendfor")
            }
            AnnotatedStatement::MultipleDefinition(ref lhs, ref rhs) => {
                write!(f, "MultipleDefinition({:?}, {:?})", lhs, rhs)
            },
        }
    }
}

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub struct AnnotatedExpression<T: Field> {
    expression: ExpressionRec<T>,
    annotations: Vec<Type>
}

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub enum ExpressionRec<T: Field> {
    Number(T),
    Identifier(String),
    Add(Box<AnnotatedExpression<T>>, Box<AnnotatedExpression<T>>),
    Sub(Box<AnnotatedExpression<T>>, Box<AnnotatedExpression<T>>),
    Mult(Box<AnnotatedExpression<T>>, Box<AnnotatedExpression<T>>),
    Div(Box<AnnotatedExpression<T>>, Box<AnnotatedExpression<T>>),
    Pow(Box<AnnotatedExpression<T>>, Box<AnnotatedExpression<T>>),
    IfElse(Box<AnnotatedCondition<T>>, Box<AnnotatedExpression<T>>, Box<AnnotatedExpression<T>>),
    FunctionCall(String, Vec<AnnotatedExpression<T>>),
}

impl<T: Field> ExpressionRec<T> {
    pub fn apply_substitution(&self, substitution: &Substitution) -> ExpressionRec<T> {
        match *self {
            ref e @ ExpressionRec::Number(_) => e.clone(),
            ExpressionRec::Identifier(ref id) => {
                let mut new_name = id.clone();
                loop {
                    match substitution.get(&new_name) {
                        Some(x) => new_name = x.to_string(),
                        None => return ExpressionRec::Identifier(new_name),
                    }
                }
            }
            ExpressionRec::Add(ref e1, ref e2) => ExpressionRec::Add(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            ExpressionRec::Sub(ref e1, ref e2) => ExpressionRec::Sub(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            ExpressionRec::Mult(ref e1, ref e2) => ExpressionRec::Mult(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            ExpressionRec::Div(ref e1, ref e2) => ExpressionRec::Div(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            ExpressionRec::Pow(ref e1, ref e2) => ExpressionRec::Pow(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            ExpressionRec::IfElse(ref c, ref e1, ref e2) => ExpressionRec::IfElse(
                box c.apply_substitution(substitution),
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            ExpressionRec::FunctionCall(ref i, ref p) => {
                for param in p {
                    param.apply_substitution(substitution);
                }
                ExpressionRec::FunctionCall(i.clone(), p.clone())
            },
        }
    }

    pub fn is_linear(&self) -> bool {
        match *self {
            ExpressionRec::Number(_) | ExpressionRec::Identifier(_) => true,
            ExpressionRec::Add(ref x, ref y) | ExpressionRec::Sub(ref x, ref y) => {
                x.is_linear() && y.is_linear()
            }
            ExpressionRec::Mult(ref x, ref y) | ExpressionRec::Div(ref x, ref y) => {
                match (&x.expression, &y.expression) {
                    (&ExpressionRec::Number(_), &ExpressionRec::Number(_)) |
                    (&ExpressionRec::Number(_), &ExpressionRec::Identifier(_)) |
                    (&ExpressionRec::Identifier(_), &ExpressionRec::Number(_)) => true,
                    _ => false,
                }
            }
            _ => false,
        }
    }

    pub fn with_annotation(&self, t: Type) -> AnnotatedExpression<T> {
        AnnotatedExpression {
            expression: self.clone(), 
            annotations: vec![t]
        }
    }

    pub fn with_annotations(&self, ts: Vec<Type>) -> AnnotatedExpression<T> {
        AnnotatedExpression {
            expression: self.clone(), 
            annotations: ts
        }
    }
}

impl<T: Field> fmt::Display for ExpressionRec<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ExpressionRec::Number(ref i) => write!(f, "{}", i),
            ExpressionRec::Identifier(ref var) => write!(f, "{}", var),
            ExpressionRec::Add(ref lhs, ref rhs) => write!(f, "({} + {})", lhs, rhs),
            ExpressionRec::Sub(ref lhs, ref rhs) => write!(f, "({} - {})", lhs, rhs),
            ExpressionRec::Mult(ref lhs, ref rhs) => write!(f, "({} * {})", lhs, rhs),
            ExpressionRec::Div(ref lhs, ref rhs) => write!(f, "({} / {})", lhs, rhs),
            ExpressionRec::Pow(ref lhs, ref rhs) => write!(f, "{}**{}", lhs, rhs),
            ExpressionRec::IfElse(ref condition, ref consequent, ref alternative) => write!(
                f,
                "if {} then {} else {} fi",
                condition,
                consequent,
                alternative
            ),
            ExpressionRec::FunctionCall(ref i, ref p) => {
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

impl<T: Field> fmt::Debug for ExpressionRec<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ExpressionRec::Number(ref i) => write!(f, "Num({})", i),
            ExpressionRec::Identifier(ref var) => write!(f, "Ide({})", var),
            ExpressionRec::Add(ref lhs, ref rhs) => write!(f, "Add({:?}, {:?})", lhs, rhs),
            ExpressionRec::Sub(ref lhs, ref rhs) => write!(f, "Sub({:?}, {:?})", lhs, rhs),
            ExpressionRec::Mult(ref lhs, ref rhs) => write!(f, "Mult({:?}, {:?})", lhs, rhs),
            ExpressionRec::Div(ref lhs, ref rhs) => write!(f, "Div({:?}, {:?})", lhs, rhs),
            ExpressionRec::Pow(ref lhs, ref rhs) => write!(f, "Pow({:?}, {:?})", lhs, rhs),
            ExpressionRec::IfElse(ref condition, ref consequent, ref alternative) => write!(
                f,
                "IfElse({:?}, {:?}, {:?})",
                condition,
                consequent,
                alternative
            ),
            ExpressionRec::FunctionCall(ref i, ref p) => {
                try!(write!(f, "FunctionCall({:?}, (", i));
                try!(f.debug_list().entries(p.iter()).finish());
                write!(f, ")")
            },
        }
    }
}


impl<T: Field> AnnotatedExpression<T> {
    pub fn apply_substitution(&self, substitution: &Substitution) -> AnnotatedExpression<T> {
        self.expression.apply_substitution(substitution).with_annotations(self.annotations.clone())
    }

    pub fn is_linear(&self) -> bool {
        self.expression.is_linear()
    }

    pub fn is_single_annotation(&self) -> Result<Type, ()> {
        match self.annotations.len() {
            1 => Ok(self.annotations[0].clone()),
            _ => Err(()),
        }
    }

    pub fn get_annotations(&self) -> Vec<Type> {
        self.annotations.clone()
    }

    pub fn get_expression(&self) -> ExpressionRec<T> {
        self.expression.clone()
    }
}

impl<T: Field> fmt::Display for AnnotatedExpression<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.expression)
    }
}

impl<T: Field> fmt::Debug for AnnotatedExpression<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.expression)
    }
}

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub struct AnnotatedExpressionList<T: Field> {
    pub expressions: Vec<AnnotatedExpression<T>>
}

impl<T: Field> AnnotatedExpressionList<T> {
    pub fn new() -> AnnotatedExpressionList<T> {
        AnnotatedExpressionList {
            expressions: vec![]
        }
    }

    pub fn apply_substitution(&self, substitution: &Substitution) -> AnnotatedExpressionList<T> {
        let expressions: Vec<AnnotatedExpression<T>> = self.expressions.iter().map(|e| e.apply_substitution(substitution)).collect();
        AnnotatedExpressionList {
            expressions: expressions
        }
    }
}

impl<T: Field> fmt::Display for AnnotatedExpressionList<T> {
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

impl<T: Field> fmt::Debug for AnnotatedExpressionList<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "AnnotatedExpressionList({:?})", self.expressions)
    }
}

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub enum AnnotatedCondition<T: Field> {
    Lt(AnnotatedExpression<T>, AnnotatedExpression<T>),
    Le(AnnotatedExpression<T>, AnnotatedExpression<T>),
    Eq(AnnotatedExpression<T>, AnnotatedExpression<T>),
    Ge(AnnotatedExpression<T>, AnnotatedExpression<T>),
    Gt(AnnotatedExpression<T>, AnnotatedExpression<T>),
}

impl<T: Field> AnnotatedCondition<T> {
    fn apply_substitution(&self, substitution: &Substitution) -> AnnotatedCondition<T> {
        match *self {
            AnnotatedCondition::Lt(ref lhs, ref rhs) => AnnotatedCondition::Lt(
                lhs.apply_substitution(substitution),
                rhs.apply_substitution(substitution),
            ),
            AnnotatedCondition::Le(ref lhs, ref rhs) => AnnotatedCondition::Le(
                lhs.apply_substitution(substitution),
                rhs.apply_substitution(substitution),
            ),
            AnnotatedCondition::Eq(ref lhs, ref rhs) => AnnotatedCondition::Eq(
                lhs.apply_substitution(substitution),
                rhs.apply_substitution(substitution),
            ),
            AnnotatedCondition::Ge(ref lhs, ref rhs) => AnnotatedCondition::Ge(
                lhs.apply_substitution(substitution),
                rhs.apply_substitution(substitution),
            ),
            AnnotatedCondition::Gt(ref lhs, ref rhs) => AnnotatedCondition::Gt(
                lhs.apply_substitution(substitution),
                rhs.apply_substitution(substitution),
            ),
        }
    }
}

impl<T: Field> fmt::Display for AnnotatedCondition<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            AnnotatedCondition::Lt(ref lhs, ref rhs) => write!(f, "{} < {}", lhs, rhs),
            AnnotatedCondition::Le(ref lhs, ref rhs) => write!(f, "{} <= {}", lhs, rhs),
            AnnotatedCondition::Eq(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            AnnotatedCondition::Ge(ref lhs, ref rhs) => write!(f, "{} >= {}", lhs, rhs),
            AnnotatedCondition::Gt(ref lhs, ref rhs) => write!(f, "{} > {}", lhs, rhs),
        }
    }
}

impl<T: Field> fmt::Debug for AnnotatedCondition<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}
