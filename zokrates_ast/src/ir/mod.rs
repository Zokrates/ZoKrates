use crate::common::{FormatString, ModuleMap, Span, WithSpan};
use crate::typed::ConcreteType;
use derivative::Derivative;
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::fmt;
use zokrates_field::Field;

mod check;
mod clean;
mod expression;
pub mod folder;
pub mod from_flat;
mod serialize;
pub mod smtlib2;
mod solver_indexer;
pub mod visitor;
mod witness;

pub use self::expression::QuadComb;
pub use self::expression::{CanonicalLinComb, LinComb};
pub use self::serialize::{ProgEnum, ProgHeader};
pub use crate::common::flat::Parameter;
pub use crate::common::flat::Variable;
pub use crate::common::RuntimeError;
pub use crate::common::Solver;

pub use self::witness::Witness;

pub type LogStatement<T> = crate::common::statements::LogStatement<(ConcreteType, Vec<LinComb<T>>)>;
pub type DirectiveStatement<'ast, T> =
    crate::common::statements::DirectiveStatement<QuadComb<T>, Variable, Solver<'ast, T>>;

#[derive(Derivative, Clone, Debug, Serialize, Deserialize)]
#[derivative(Hash, PartialEq, Eq)]
pub struct ConstraintStatement<T> {
    #[derivative(Hash = "ignore", PartialEq = "ignore")]
    pub span: Option<Span>,
    pub quad: QuadComb<T>,
    pub lin: LinComb<T>,
    #[derivative(Hash = "ignore", PartialEq = "ignore")]
    pub error: Option<RuntimeError>,
}

impl<T> ConstraintStatement<T> {
    pub fn new(quad: QuadComb<T>, lin: LinComb<T>, error: Option<RuntimeError>) -> Self {
        Self {
            span: None,
            quad,
            lin,
            error,
        }
    }
}

impl<T> WithSpan for ConstraintStatement<T> {
    fn span(mut self, span: Option<Span>) -> Self {
        self.span = span;
        self
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

impl<T: Field> fmt::Display for ConstraintStatement<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{} == {}{}",
            self.quad,
            self.lin,
            self.error
                .as_ref()
                .map(|e| format!(" // {}", e))
                .unwrap_or_else(|| "".to_string())
        )
    }
}

#[derive(Derivative, Clone, Debug, Serialize, Deserialize)]
#[derivative(Hash, PartialEq, Eq)]
pub struct BlockStatement<'ast, T> {
    #[derivative(Hash = "ignore", PartialEq = "ignore")]
    pub span: Option<Span>,
    #[serde(borrow)]
    pub inner: Vec<Statement<'ast, T>>,
}

impl<'ast, T> BlockStatement<'ast, T> {
    pub fn new(inner: Vec<Statement<'ast, T>>) -> Self {
        Self { span: None, inner }
    }
}

impl<'ast, T> WithSpan for BlockStatement<'ast, T> {
    fn span(mut self, span: Option<Span>) -> Self {
        self.span = span;
        self
    }

    fn get_span(&self) -> Option<Span> {
        self.span
    }
}

impl<'ast, T: Field> fmt::Display for BlockStatement<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "{{")?;
        for s in &self.inner {
            writeln!(f, "{}", s)?;
        }
        write!(f, "}}")
    }
}

#[allow(clippy::large_enum_variant)]
#[derive(Debug, Serialize, Deserialize, Clone, Derivative)]
#[derivative(Hash, PartialEq, Eq)]
pub enum Statement<'ast, T> {
    #[serde(skip)]
    Block(BlockStatement<'ast, T>),
    Constraint(ConstraintStatement<T>),
    #[serde(borrow)]
    Directive(DirectiveStatement<'ast, T>),
    Log(LogStatement<T>),
}

pub type PublicInputs = BTreeSet<Variable>;

impl<'ast, T> WithSpan for Statement<'ast, T> {
    fn span(self, span: Option<Span>) -> Self {
        match self {
            Statement::Constraint(c) => Statement::Constraint(c.span(span)),
            Statement::Directive(c) => Statement::Directive(c.span(span)),
            Statement::Log(c) => Statement::Log(c.span(span)),
            Statement::Block(c) => Statement::Block(c.span(span)),
        }
    }

    fn get_span(&self) -> Option<Span> {
        match self {
            Statement::Constraint(c) => c.get_span(),
            Statement::Directive(c) => c.get_span(),
            Statement::Log(c) => c.get_span(),
            Statement::Block(c) => c.get_span(),
        }
    }
}

impl<'ast, T: Field> Statement<'ast, T> {
    pub fn definition<U: Into<QuadComb<T>>>(v: Variable, e: U) -> Self {
        Statement::constraint(e, v, None)
    }

    pub fn constraint<U: Into<QuadComb<T>>, V: Into<LinComb<T>>>(
        quad: U,
        lin: V,
        error: Option<RuntimeError>,
    ) -> Self {
        Statement::Constraint(ConstraintStatement::new(quad.into(), lin.into(), error))
    }

    pub fn log(
        format_string: FormatString,
        expressions: Vec<(ConcreteType, Vec<LinComb<T>>)>,
    ) -> Self {
        Statement::Log(LogStatement::new(format_string, expressions))
    }

    pub fn block(inner: Vec<Statement<'ast, T>>) -> Self {
        Statement::Block(BlockStatement::new(inner))
    }

    pub fn directive(
        outputs: Vec<Variable>,
        solver: Solver<'ast, T>,
        inputs: Vec<QuadComb<T>>,
    ) -> Self {
        Statement::Directive(DirectiveStatement::new(outputs, solver, inputs))
    }
}

impl<'ast, T: Field> fmt::Display for Statement<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Statement::Constraint(ref s) => write!(f, "{}", s),
            Statement::Block(ref s) => write!(f, "{}", s),
            Statement::Directive(ref s) => write!(f, "{}", s),
            Statement::Log(ref s) => write!(
                f,
                "log(\"{}\", {})",
                s.format_string,
                s.expressions
                    .iter()
                    .map(|(_, l)| format!(
                        "[{}]",
                        l.iter()
                            .map(|l| l.to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    ))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        }
    }
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq)]
pub struct ProgIterator<'ast, T, I: IntoIterator<Item = Statement<'ast, T>>> {
    pub module_map: ModuleMap,
    pub arguments: Vec<Parameter>,
    pub return_count: usize,
    pub statements: I,
    #[serde(borrow)]
    pub solvers: Vec<Solver<'ast, T>>,
}

pub type Prog<'ast, T> = ProgIterator<'ast, T, Vec<Statement<'ast, T>>>;

impl<'ast, T> Default for Prog<'ast, T> {
    fn default() -> Self {
        Self {
            module_map: Default::default(),
            arguments: Default::default(),
            return_count: Default::default(),
            statements: Default::default(),
            solvers: Default::default(),
        }
    }
}

impl<'ast, T, I: IntoIterator<Item = Statement<'ast, T>>> ProgIterator<'ast, T, I> {
    pub fn new(
        arguments: Vec<Parameter>,
        statements: I,
        return_count: usize,
        module_map: ModuleMap,
        solvers: Vec<Solver<'ast, T>>,
    ) -> Self {
        Self {
            arguments,
            return_count,
            statements,
            module_map,
            solvers,
        }
    }

    pub fn collect(self) -> Prog<'ast, T> {
        ProgIterator {
            statements: self.statements.into_iter().collect(),
            arguments: self.arguments,
            return_count: self.return_count,
            module_map: self.module_map,
            solvers: self.solvers,
        }
    }

    pub fn returns(&self) -> Vec<Variable> {
        (0..self.return_count).map(Variable::public).collect()
    }

    pub fn public_count(&self) -> usize {
        self.arguments.iter().filter(|a| !a.private).count() + self.return_count
    }

    pub fn public_inputs(&self) -> PublicInputs {
        self.arguments
            .iter()
            .filter(|a| !a.private)
            .map(|a| a.id)
            .collect()
    }

    pub fn public_inputs_values(&self, witness: &Witness<T>) -> Vec<T>
    where
        T: Field,
    {
        self.arguments
            .iter()
            .filter(|p| !p.private)
            .map(|p| *witness.0.get(&p.id).unwrap())
            .chain(witness.return_values())
            .collect()
    }
}

impl<'ast, T> Prog<'ast, T> {
    pub fn constraint_count(&self) -> usize {
        self.statements
            .iter()
            .filter(|s| matches!(s, Statement::Constraint(..)))
            .count()
    }
}

impl<'ast, T: Field> fmt::Display for Prog<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let returns = (0..self.return_count)
            .map(Variable::public)
            .map(|e| format!("{}", e))
            .collect::<Vec<_>>()
            .join(", ");

        writeln!(
            f,
            "def main({}) -> ({}) {{",
            self.arguments
                .iter()
                .map(|v| format!("{}", v))
                .collect::<Vec<_>>()
                .join(", "),
            returns,
        )?;
        for s in &self.statements {
            writeln!(f, "\t{}", s)?;
        }

        writeln!(f, "\treturn {}", returns)?;
        writeln!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::Bn128Field;

    mod statement {
        use super::*;

        #[test]
        fn print_constraint() {
            let c: Statement<Bn128Field> = Statement::constraint(
                QuadComb::new(Variable::new(42).into(), Variable::new(42).into()),
                Variable::new(42),
                None,
            );
            assert_eq!(format!("{}", c), "(1 * _42) * (1 * _42) == 1 * _42")
        }
    }
}
