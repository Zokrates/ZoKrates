//! Module containing structs and enums to represent a program.
//!
//! @file absy.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

pub mod folder;
pub mod utils;

use crate::common;
pub use crate::common::flat::Parameter;
pub use crate::common::flat::Variable;
use crate::common::statements::DirectiveStatement;
use crate::common::FormatString;
use crate::common::ModuleMap;
pub use crate::common::RuntimeError;
use crate::common::{
    expressions::{BinaryExpression, IdentifierExpression, ValueExpression},
    operators::*,
};
use crate::common::{Span, WithSpan};

use derivative::Derivative;
pub use utils::{
    flat_expression_from_bits, flat_expression_from_expression_summands,
    flat_expression_from_variable_summands,
};

use crate::common::Solver;
use crate::typed::ConcreteType;
use std::collections::HashMap;
use std::fmt;
use zokrates_field::Field;

pub type FlatProg<T> = FlatFunction<T>;

pub type FlatFunction<T> = FlatFunctionIterator<T, Vec<FlatStatement<T>>>;

pub type FlatProgIterator<T, I> = FlatFunctionIterator<T, I>;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct FlatFunctionIterator<T, I: IntoIterator<Item = FlatStatement<T>>> {
    /// The map of the modules for sourcemaps
    pub module_map: ModuleMap,
    /// Arguments of the function
    pub arguments: Vec<Parameter>,
    /// Vector of statements that are executed when running the function
    pub statements: I,
    /// Number of outputs
    pub return_count: usize,
}

impl<T, I: IntoIterator<Item = FlatStatement<T>>> FlatFunctionIterator<T, I> {
    pub fn collect(self) -> FlatFunction<T> {
        FlatFunction {
            statements: self.statements.into_iter().collect(),
            arguments: self.arguments,
            return_count: self.return_count,
            module_map: self.module_map,
        }
    }
}

impl<T: Field> fmt::Display for FlatFunction<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "def main({}) -> {}:\n{}",
            self.arguments
                .iter()
                .map(|x| format!("{}", x))
                .collect::<Vec<_>>()
                .join(","),
            self.return_count,
            self.statements
                .iter()
                .map(|x| format!("\t{}", x))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

pub type DefinitionStatement<T> =
    common::expressions::DefinitionStatement<Variable, FlatExpression<T>>;
pub type LogStatement<T> = common::statements::LogStatement<(ConcreteType, Vec<FlatExpression<T>>)>;
pub type FlatDirective<T> = common::statements::DirectiveStatement<FlatExpression<T>, Variable>;

#[derive(Derivative)]
#[derivative(PartialEq, Hash)]
#[derive(Clone, Debug)]
pub struct AssertionStatement<T> {
    #[derivative(PartialEq = "ignore", Hash = "ignore")]
    pub span: Option<Span>,
    pub quad: FlatExpression<T>,
    pub lin: FlatExpression<T>,
    pub error: RuntimeError,
}

impl<T> AssertionStatement<T> {
    pub fn new(lin: FlatExpression<T>, quad: FlatExpression<T>, error: RuntimeError) -> Self {
        AssertionStatement {
            span: None,
            quad,
            lin,
            error,
        }
    }
}

impl<T> WithSpan for AssertionStatement<T> {
    fn span(self, span: Option<Span>) -> Self {
        Self { span, ..self }
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

#[derive(Derivative)]
#[derivative(PartialEq, Hash)]
#[derive(Clone, Debug)]
pub enum FlatStatement<T> {
    Condition(AssertionStatement<T>),
    Definition(DefinitionStatement<T>),
    Directive(FlatDirective<T>),
    Log(LogStatement<T>),
}

impl<T> FlatStatement<T> {
    pub fn definition(assignee: Variable, rhs: FlatExpression<T>) -> Self {
        Self::Definition(DefinitionStatement::new(assignee, rhs))
    }

    pub fn condition(lin: FlatExpression<T>, quad: FlatExpression<T>, error: RuntimeError) -> Self {
        Self::Condition(AssertionStatement::new(lin, quad, error))
    }

    pub fn log(
        format_string: FormatString,
        expressions: Vec<(ConcreteType, Vec<FlatExpression<T>>)>,
    ) -> Self {
        Self::Log(LogStatement::new(format_string, expressions))
    }

    pub fn directive(
        outputs: Vec<Variable>,
        solver: Solver,
        inputs: Vec<FlatExpression<T>>,
    ) -> Self {
        Self::Directive(DirectiveStatement::new(outputs, solver, inputs))
    }
}

impl<T> WithSpan for FlatStatement<T> {
    fn span(self, span: Option<Span>) -> Self {
        use FlatStatement::*;

        match self {
            Condition(e) => Condition(e.span(span)),
            Definition(e) => Definition(e.span(span)),
            Directive(e) => Directive(e.span(span)),
            Log(e) => Log(e.span(span)),
        }
    }

    fn get_span(&self) -> Option<Span> {
        use FlatStatement::*;

        match self {
            Condition(e) => e.get_span(),
            Definition(e) => e.get_span(),
            Directive(e) => e.get_span(),
            Log(e) => e.get_span(),
        }
    }
}

impl<T: Field> fmt::Display for FlatStatement<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FlatStatement::Definition(ref e) => write!(f, "{}", e),
            FlatStatement::Condition(ref s) => {
                write!(f, "{} == {} // {}", s.quad, s.lin, s.error)
            }
            FlatStatement::Directive(ref d) => write!(f, "{}", d),
            FlatStatement::Log(ref s) => write!(
                f,
                "log(\"{}\"), {})",
                s.format_string,
                s.expressions
                    .iter()
                    .map(|(_, e)| format!(
                        "[{}]",
                        e.iter()
                            .map(|e| e.to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    ))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

impl<T: Field> FlatStatement<T> {
    pub fn apply_substitution(
        self,
        substitution: &HashMap<Variable, Variable>,
    ) -> FlatStatement<T> {
        match self {
            FlatStatement::Definition(s) => FlatStatement::definition(
                *s.assignee.apply_substitution(substitution),
                s.rhs.apply_substitution(substitution),
            ),
            FlatStatement::Condition(s) => FlatStatement::condition(
                s.quad.apply_substitution(substitution),
                s.lin.apply_substitution(substitution),
                s.error,
            ),
            FlatStatement::Directive(d) => {
                let outputs = d
                    .outputs
                    .into_iter()
                    .map(|o| *o.apply_substitution(substitution))
                    .collect();
                let inputs = d
                    .inputs
                    .into_iter()
                    .map(|i| i.apply_substitution(substitution))
                    .collect();

                FlatStatement::Directive(FlatDirective {
                    inputs,
                    outputs,
                    ..d
                })
            }
            FlatStatement::Log(s) => FlatStatement::Log(LogStatement::new(
                s.format_string,
                s.expressions
                    .into_iter()
                    .map(|(t, e)| {
                        (
                            t,
                            e.into_iter()
                                .map(|e| e.apply_substitution(substitution))
                                .collect(),
                        )
                    })
                    .collect(),
            )),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum FlatExpression<T> {
    Number(ValueExpression<T>),
    Identifier(IdentifierExpression<Variable, Self>),
    Add(BinaryExpression<OpAdd, Self, Self, Self>),
    Sub(BinaryExpression<OpSub, Self, Self, Self>),
    Mult(BinaryExpression<OpMul, Self, Self, Self>),
}

impl<T> std::ops::Add for FlatExpression<T> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        FlatExpression::Add(BinaryExpression::new(self, other))
    }
}

impl<T> std::ops::Sub for FlatExpression<T> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        FlatExpression::Sub(BinaryExpression::new(self, other))
    }
}

impl<T> std::ops::Mul for FlatExpression<T> {
    type Output = Self;

    fn mul(self, other: Self) -> Self::Output {
        FlatExpression::Mult(BinaryExpression::new(self, other))
    }
}

impl<T> From<T> for FlatExpression<T> {
    fn from(other: T) -> Self {
        Self::from_value(other)
    }
}

impl<T, Op> BinaryExpression<Op, FlatExpression<T>, FlatExpression<T>, FlatExpression<T>> {
    fn apply_substitution(self, substitution: &HashMap<Variable, Variable>) -> Self {
        let left = self.left.apply_substitution(substitution);
        let right = self.right.apply_substitution(substitution);

        Self::new(left, right).span(self.span)
    }
}

impl<T> IdentifierExpression<Variable, FlatExpression<T>> {
    fn apply_substitution(self, substitution: &HashMap<Variable, Variable>) -> Self {
        let id = *self.id.apply_substitution(substitution);

        IdentifierExpression { id, ..self }
    }
}

impl<T> FlatExpression<T> {
    pub fn identifier(v: Variable) -> Self {
        Self::Identifier(IdentifierExpression::new(v))
    }

    pub fn from_value(t: T) -> Self {
        Self::Number(ValueExpression::new(t))
    }

    pub fn apply_substitution(self, substitution: &HashMap<Variable, Variable>) -> Self {
        match self {
            e @ FlatExpression::Number(_) => e,
            FlatExpression::Identifier(id) => {
                FlatExpression::Identifier(id.apply_substitution(substitution))
            }
            FlatExpression::Add(e) => FlatExpression::Add(e.apply_substitution(substitution)),
            FlatExpression::Sub(e) => FlatExpression::Sub(e.apply_substitution(substitution)),
            FlatExpression::Mult(e) => FlatExpression::Mult(e.apply_substitution(substitution)),
        }
    }

    pub fn is_linear(&self) -> bool {
        match *self {
            FlatExpression::Number(_) | FlatExpression::Identifier(_) => true,
            FlatExpression::Add(ref e) => e.left.is_linear() && e.right.is_linear(),
            FlatExpression::Sub(ref e) => e.left.is_linear() && e.right.is_linear(),
            FlatExpression::Mult(ref e) => matches!(
                (&e.left, &e.right),
                (box FlatExpression::Number(_), box FlatExpression::Number(_))
                    | (
                        box FlatExpression::Number(_),
                        box FlatExpression::Identifier(_)
                    )
                    | (
                        box FlatExpression::Identifier(_),
                        box FlatExpression::Number(_)
                    )
            ),
        }
    }
}

impl<T: Field> fmt::Display for FlatExpression<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FlatExpression::Number(ref i) => write!(f, "{}", i),
            FlatExpression::Identifier(ref var) => write!(f, "{}", var),
            FlatExpression::Add(ref e) => write!(f, "{}", e),
            FlatExpression::Sub(ref e) => write!(f, "{}", e),
            FlatExpression::Mult(ref e) => write!(f, "{}", e),
        }
    }
}

impl<T: Field> From<Variable> for FlatExpression<T> {
    fn from(v: Variable) -> FlatExpression<T> {
        FlatExpression::identifier(v)
    }
}

#[derive(PartialEq, Eq, Debug)]
pub struct Error {
    message: String,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl<T> WithSpan for FlatExpression<T> {
    fn span(self, span: Option<Span>) -> Self {
        use FlatExpression::*;
        match self {
            Add(e) => Add(e.span(span)),
            Sub(e) => Sub(e.span(span)),
            Mult(e) => Mult(e.span(span)),
            Number(e) => Number(e.span(span)),
            Identifier(e) => Identifier(e.span(span)),
        }
    }

    fn get_span(&self) -> Option<Span> {
        use FlatExpression::*;
        match self {
            Add(e) => e.get_span(),
            Sub(e) => e.get_span(),
            Mult(e) => e.get_span(),
            Number(e) => e.get_span(),
            Identifier(e) => e.get_span(),
        }
    }
}
