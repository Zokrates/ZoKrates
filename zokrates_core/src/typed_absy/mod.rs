//! Module containing structs and enums to represent a program.
//!
//! @file absy.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

use types::Signature;
use absy::parameter::Parameter;
use absy::variable::Variable;

use std::fmt;
use substitution::Substitution;
use field::Field;
use imports::Import;
use flat_absy::*;
use types::Type;

#[derive(Serialize, Deserialize, Clone, PartialEq)]
pub struct TypedProg<T: Field> {
    /// Functions of the program
    pub functions: Vec<TypedFunction<T>>,
    pub imports: Vec<Import>,
    pub imported_functions: Vec<FlatFunction<T>>
}

impl<T: Field> fmt::Display for TypedProg<T> {
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

impl<T: Field> fmt::Debug for TypedProg<T> {
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
pub struct TypedFunction<T: Field> {
    /// Name of the program
    pub id: String,
    /// Arguments of the function
    pub arguments: Vec<Parameter>,
    /// Vector of statements that are executed when running the function
    pub statements: Vec<TypedStatement<T>>,
    /// function signature
    pub signature: Signature,
}

impl<T: Field> fmt::Display for TypedFunction<T> {
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

impl<T: Field> fmt::Debug for TypedFunction<T> {
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

#[derive(Clone, Serialize, Deserialize, PartialEq)]
pub enum TypedStatement<T: Field> {
    Return(Vec<TypedExpression<T>>),
    Definition(Variable, TypedExpression<T>),
    Declaration(Variable),
    Condition(TypedExpression<T>, TypedExpression<T>),
    For(Variable, T, T, Vec<TypedStatement<T>>),
    MultipleDefinition(Vec<Variable>, TypedExpressionList<T>),
}

impl<T: Field> fmt::Debug for TypedStatement<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedStatement::Return(ref exprs) => {
                try!(write!(f, "Return("));
                for (i, expr) in exprs.iter().enumerate() {
                    try!(write!(f, "{}", expr));
                    if i < exprs.len() - 1 {
                        try!(write!(f, ", "));
                    }
                }
                write!(f, ")")
            },
            TypedStatement::Declaration(ref var) => {
                write!(f, "Declaration({:?})", var)
            }
            TypedStatement::Definition(ref lhs, ref rhs) => {
                write!(f, "Definition({:?}, {:?})", lhs, rhs)
            }
            TypedStatement::Condition(ref lhs, ref rhs) => write!(f, "Condition({:?}, {:?})", lhs, rhs),
            TypedStatement::For(ref var, ref start, ref stop, ref list) => {
                try!(write!(f, "for {:?} in {:?}..{:?} do\n", var, start, stop));
                for l in list {
                    try!(write!(f, "\t\t{:?}\n", l));
                }
                write!(f, "\tendfor")
            }
            TypedStatement::MultipleDefinition(ref lhs, ref rhs) => {
                write!(f, "MultipleDefinition({:?}, {:?})", lhs, rhs)
            },
        }
    }
}


impl<T: Field> fmt::Display for TypedStatement<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedStatement::Return(ref exprs) => {
                try!(write!(f, "return "));
                for (i, expr) in exprs.iter().enumerate() {
                    try!(write!(f, "{}", expr));
                    if i < exprs.len() - 1 {
                        try!(write!(f, ", "));
                    }
                }
                write!(f, "")
            },
            TypedStatement::Declaration(ref var) => write!(f, "{}", var),
            TypedStatement::Definition(ref lhs, ref rhs) => write!(f, "{} = {}", lhs, rhs),
            TypedStatement::Condition(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            TypedStatement::For(ref var, ref start, ref stop, ref list) => {
                try!(write!(f, "for {} in {}..{} do\n", var, start, stop));
                for l in list {
                    try!(write!(f, "\t\t{}\n", l));
                }
                write!(f, "\tendfor")
            }
            TypedStatement::MultipleDefinition(ref ids, ref rhs) => {
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

pub trait Typed
{
    fn get_type(&self) -> Type;
}

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub enum TypedExpression<T: Field> {
    Boolean(BooleanExpression<T>),
    FieldElement(FieldElementExpression<T>),
}

impl<T: Field> From<BooleanExpression<T>> for TypedExpression<T> {
    fn from(e: BooleanExpression<T>) -> TypedExpression<T> {
        TypedExpression::Boolean(e)
    }
}

impl<T: Field> From<FieldElementExpression<T>> for TypedExpression<T> {
    fn from(e: FieldElementExpression<T>) -> TypedExpression<T> {
        TypedExpression::FieldElement(e)
    }
}

impl<T: Field> fmt::Display for TypedExpression<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedExpression::Boolean(ref e) => {
                write!(f, "{}", e)
            },
            TypedExpression::FieldElement(ref e) => {
                write!(f, "{}", e)
            }
        }
    }
}

impl<T: Field> fmt::Debug for TypedExpression<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedExpression::Boolean(ref e) => {
                write!(f, "{:?}", e)
            },
            TypedExpression::FieldElement(ref e) => {
                write!(f, "{:?}", e)
            }
        }
    }
}

impl<T: Field> Typed for TypedExpression<T> {
    fn get_type(&self) -> Type {
        match self {
            TypedExpression::Boolean(_) => Type::Boolean,
            TypedExpression::FieldElement(_) => Type::FieldElement
        }
    }
}

pub trait MultiTyped
{
    fn get_types(&self) -> &Vec<Type>;
}

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub enum TypedExpressionList<T: Field> {
    FunctionCall(String, Vec<TypedExpression<T>>, Vec<Type>)
}

impl<T: Field> MultiTyped for TypedExpressionList<T> {
    fn get_types(&self) -> &Vec<Type> {
        match *self {
            TypedExpressionList::FunctionCall(_, _, ref types) => types
        }
    }
}

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub enum FieldElementExpression<T: Field> {
    Number(T),
    Identifier(String),
    Add(Box<FieldElementExpression<T>>, Box<FieldElementExpression<T>>),
    Sub(Box<FieldElementExpression<T>>, Box<FieldElementExpression<T>>),
    Mult(Box<FieldElementExpression<T>>, Box<FieldElementExpression<T>>),
    Div(Box<FieldElementExpression<T>>, Box<FieldElementExpression<T>>),
    Pow(Box<FieldElementExpression<T>>, Box<FieldElementExpression<T>>),
    IfElse(Box<BooleanExpression<T>>, Box<FieldElementExpression<T>>, Box<FieldElementExpression<T>>),
    FunctionCall(String, Vec<TypedExpression<T>>),
}

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub enum BooleanExpression<T: Field> {
    Identifier(String),
    Value(bool),
    Lt(Box<FieldElementExpression<T>>, Box<FieldElementExpression<T>>),
    Le(Box<FieldElementExpression<T>>, Box<FieldElementExpression<T>>),
    Eq(Box<FieldElementExpression<T>>, Box<FieldElementExpression<T>>),
    Ge(Box<FieldElementExpression<T>>, Box<FieldElementExpression<T>>),
    Gt(Box<FieldElementExpression<T>>, Box<FieldElementExpression<T>>),
    AndAnd(Box<BooleanExpression<T>>, Box<BooleanExpression<T>>),
    Or(Box<BooleanExpression<T>>, Box<BooleanExpression<T>>),
}

impl<T: Field> BooleanExpression<T> {
    pub fn apply_substitution(self, substitution: &Substitution) -> BooleanExpression<T> {
        match self {
            BooleanExpression::Identifier(id) => {
                let mut new_name = id;
                loop {
                    match substitution.get(&new_name) {
                        Some(x) => new_name = x.to_string(),
                        None => return BooleanExpression::Identifier(new_name),
                    }
                }
            },
            BooleanExpression::Lt(lhs, rhs) => BooleanExpression::Lt(
                box lhs.apply_substitution(substitution),
                box rhs.apply_substitution(substitution),
            ),
            BooleanExpression::Le(lhs, rhs) => BooleanExpression::Le(
                box lhs.apply_substitution(substitution),
                box rhs.apply_substitution(substitution),
            ),
            BooleanExpression::Eq(lhs, rhs) => BooleanExpression::Eq(
                box lhs.apply_substitution(substitution),
                box rhs.apply_substitution(substitution),
            ),
            BooleanExpression::Ge(lhs, rhs) => BooleanExpression::Ge(
                box lhs.apply_substitution(substitution),
                box rhs.apply_substitution(substitution),
            ),
            BooleanExpression::Gt(lhs, rhs) => BooleanExpression::Gt(
                box lhs.apply_substitution(substitution),
                box rhs.apply_substitution(substitution),
            ),
            BooleanExpression::AndAnd(lhs, rhs) => BooleanExpression::AndAnd(
                box lhs.apply_substitution(substitution),
                box rhs.apply_substitution(substitution),
            ),
            BooleanExpression::Or(lhs, rhs) => BooleanExpression::Or(
                box lhs.apply_substitution(substitution),
                box rhs.apply_substitution(substitution),
            ),
                BooleanExpression::Value(b) => BooleanExpression::Value(b),
        }
    }


    pub fn is_linear(&self) -> bool {
        false
    }
}

impl<T: Field> FieldElementExpression<T> {
    pub fn apply_substitution(self, substitution: &Substitution) -> FieldElementExpression<T> {
        match self {
            e @ FieldElementExpression::Number(_) => e,
            FieldElementExpression::Identifier(id) => {
                let mut new_name = id.clone();
                loop {
                    match substitution.get(&new_name) {
                        Some(x) => new_name = x.to_string(),
                        None => return FieldElementExpression::Identifier(new_name),
                    }
                }
            }
            FieldElementExpression::Add(e1, e2) => FieldElementExpression::Add(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            FieldElementExpression::Sub(e1, e2) => FieldElementExpression::Sub(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            FieldElementExpression::Mult(e1, e2) => FieldElementExpression::Mult(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            FieldElementExpression::Div(e1, e2) => FieldElementExpression::Div(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            FieldElementExpression::Pow(e1, e2) => FieldElementExpression::Pow(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            FieldElementExpression::IfElse(c, e1, e2) => FieldElementExpression::IfElse(
                box c.apply_substitution(substitution),
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            FieldElementExpression::FunctionCall(i, p) => {
                FieldElementExpression::FunctionCall(i, p.into_iter().map(|param| param.apply_substitution(substitution)).collect())
            },
        }
    }

    pub fn is_linear(&self) -> bool {
        match *self {
            FieldElementExpression::Number(_) | FieldElementExpression::Identifier(_) => true,
            FieldElementExpression::Add(ref x, ref y) | FieldElementExpression::Sub(ref x, ref y) => {
                x.is_linear() && y.is_linear()
            }
            FieldElementExpression::Mult(ref x, ref y) | FieldElementExpression::Div(ref x, ref y) => {
                match (x, y) {
                    (box FieldElementExpression::Number(_), box FieldElementExpression::Number(_)) |
                    (box FieldElementExpression::Number(_), box FieldElementExpression::Identifier(_)) |
                    (box FieldElementExpression::Identifier(_), box FieldElementExpression::Number(_)) => true,
                    _ => false,
                }
            }
            _ => false,
        }
    }
}

impl<T: Field> fmt::Display for FieldElementExpression<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FieldElementExpression::Number(ref i) => write!(f, "{}", i),
            FieldElementExpression::Identifier(ref var) => write!(f, "{}", var),
            FieldElementExpression::Add(ref lhs, ref rhs) => write!(f, "({} + {})", lhs, rhs),
            FieldElementExpression::Sub(ref lhs, ref rhs) => write!(f, "({} - {})", lhs, rhs),
            FieldElementExpression::Mult(ref lhs, ref rhs) => write!(f, "({} * {})", lhs, rhs),
            FieldElementExpression::Div(ref lhs, ref rhs) => write!(f, "({} / {})", lhs, rhs),
            FieldElementExpression::Pow(ref lhs, ref rhs) => write!(f, "{}**{}", lhs, rhs),
            FieldElementExpression::IfElse(ref condition, ref consequent, ref alternative) => write!(
                f,
                "if {} then {} else {} fi",
                condition,
                consequent,
                alternative
            ),
            FieldElementExpression::FunctionCall(ref i, ref p) => {
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

impl<T: Field> fmt::Display for BooleanExpression<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            BooleanExpression::Identifier(ref var) => write!(f, "{}", var),
            BooleanExpression::Lt(ref lhs, ref rhs) => write!(f, "{} < {}", lhs, rhs),
            BooleanExpression::Le(ref lhs, ref rhs) => write!(f, "{} <= {}", lhs, rhs),
            BooleanExpression::Eq(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            BooleanExpression::Ge(ref lhs, ref rhs) => write!(f, "{} >= {}", lhs, rhs),
            BooleanExpression::Gt(ref lhs, ref rhs) => write!(f, "{} > {}", lhs, rhs),
            BooleanExpression::AndAnd(ref lhs, ref rhs) => write!(f, "{} && {}", lhs, rhs),
            BooleanExpression::Or(ref lhs, ref rhs) => write!(f, "{} || {}", lhs, rhs),
            BooleanExpression::Value(b) => write!(f, "{}", b),
        }
    }
}

impl<T: Field> fmt::Debug for BooleanExpression<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl<T: Field> fmt::Debug for FieldElementExpression<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FieldElementExpression::Number(ref i) => write!(f, "Num({})", i),
            FieldElementExpression::Identifier(ref var) => write!(f, "Ide({})", var),
            FieldElementExpression::Add(ref lhs, ref rhs) => write!(f, "Add({:?}, {:?})", lhs, rhs),
            FieldElementExpression::Sub(ref lhs, ref rhs) => write!(f, "Sub({:?}, {:?})", lhs, rhs),
            FieldElementExpression::Mult(ref lhs, ref rhs) => write!(f, "Mult({:?}, {:?})", lhs, rhs),
            FieldElementExpression::Div(ref lhs, ref rhs) => write!(f, "Div({:?}, {:?})", lhs, rhs),
            FieldElementExpression::Pow(ref lhs, ref rhs) => write!(f, "Pow({:?}, {:?})", lhs, rhs),
            FieldElementExpression::IfElse(ref condition, ref consequent, ref alternative) => write!(
                f,
                "IfElse({:?}, {:?}, {:?})",
                condition,
                consequent,
                alternative
            ),
            FieldElementExpression::FunctionCall(ref i, ref p) => {
                try!(write!(f, "FunctionCall({:?}, (", i));
                try!(f.debug_list().entries(p.iter()).finish());
                write!(f, ")")
            },
        }
    }
}


impl<T: Field> TypedExpression<T> {
    pub fn apply_substitution(self, substitution: &Substitution) -> TypedExpression<T> {
        match self {
            TypedExpression::Boolean(e) => e.apply_substitution(substitution).into(),
            TypedExpression::FieldElement(e) => e.apply_substitution(substitution).into(),
        }
    }
}

impl<T: Field> TypedExpressionList<T> {
    pub fn apply_substitution(self, substitution: &Substitution) -> TypedExpressionList<T> {
        match self {
            TypedExpressionList::FunctionCall(id, inputs, types) => {
                TypedExpressionList::FunctionCall(id, inputs.into_iter().map(|i| i.apply_substitution(substitution)).collect(), types)
            }
        }
    }
}

impl<T: Field> fmt::Display for TypedExpressionList<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedExpressionList::FunctionCall(ref i, ref p, _) => {
                try!(write!(f, "{}(", i,));
                for (i, param) in p.iter().enumerate() {
                    try!(write!(f, "{}", param));
                    if i < p.len() - 1 {
                        try!(write!(f, ", "));
                    }
                }
                write!(f, ")")
            }
        }
    }
}

impl<T: Field> fmt::Debug for TypedExpressionList<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypedExpressionList::FunctionCall(ref i, ref p, _) => {
                try!(write!(f, "FunctionCall({:?}, (", i));
                try!(f.debug_list().entries(p.iter()).finish());
                write!(f, ")")
            }
        }
    }
}
