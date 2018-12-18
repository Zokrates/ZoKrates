//! Module containing structs and enums to represent a program.
//!
//! @file absy.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

pub mod flat_parameter;
pub mod flat_variable;

pub use self::flat_parameter::FlatParameter;
pub use self::flat_variable::FlatVariable;

use field::Field;
use helpers::DirectiveStatement;
#[cfg(feature = "libsnark")]
use standard;
use std::collections::HashMap;
use std::fmt;
use types::Signature;

#[derive(Clone)]
pub struct FlatProg<T: Field> {
    /// FlatFunctions of the program
    pub functions: Vec<FlatFunction<T>>,
}

impl<T: Field> fmt::Display for FlatProg<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            self.functions
                .iter()
                .map(|x| format!("{}", x))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

impl<T: Field> fmt::Debug for FlatProg<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "flat_program(functions: {}\t)",
            self.functions
                .iter()
                .map(|x| format!("\t{:?}", x))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

#[cfg(feature = "libsnark")]
impl<T: Field> From<standard::DirectiveR1CS> for FlatProg<T> {
    fn from(dr1cs: standard::DirectiveR1CS) -> Self {
        FlatProg {
            functions: vec![dr1cs.into()],
        }
    }
}

#[derive(Clone, PartialEq)]
pub struct FlatFunction<T: Field> {
    /// Name of the program
    pub id: String,
    /// Arguments of the function
    pub arguments: Vec<FlatParameter>,
    /// Vector of statements that are executed when running the function
    pub statements: Vec<FlatStatement<T>>,
    /// Typed signature
    pub signature: Signature,
}

impl<T: Field> fmt::Display for FlatFunction<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "def {}({}):\n{}",
            self.id,
            self.arguments
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

impl<T: Field> fmt::Debug for FlatFunction<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "FlatFunction(id: {:?}, arguments: {:?}, signature: {:?}):\n{}",
            self.id,
            self.arguments,
            self.signature,
            self.statements
                .iter()
                .map(|x| format!("\t{:?}", x))
                .collect::<Vec<_>>()
                .join("\n"),
        )
    }
}

#[derive(Clone, PartialEq)]
pub enum FlatStatement<T: Field> {
    Return(FlatExpressionList<T>),
    Condition(FlatExpression<T>, FlatExpression<T>),
    Definition(FlatVariable, FlatExpression<T>),
    Directive(DirectiveStatement<T>),
}

impl<T: Field> fmt::Display for FlatStatement<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FlatStatement::Definition(ref lhs, ref rhs) => write!(f, "{} = {}", lhs, rhs),
            FlatStatement::Return(ref expr) => write!(f, "return {}", expr),
            FlatStatement::Condition(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            FlatStatement::Directive(ref d) => write!(f, "{}", d),
        }
    }
}

impl<T: Field> fmt::Debug for FlatStatement<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FlatStatement::Definition(ref lhs, ref rhs) => write!(f, "{} = {}", lhs, rhs),
            FlatStatement::Return(ref expr) => write!(f, "FlatReturn({:?})", expr),
            FlatStatement::Condition(ref lhs, ref rhs) => {
                write!(f, "FlatCondition({:?}, {:?})", lhs, rhs)
            }
            FlatStatement::Directive(ref d) => write!(f, "{:?}", d),
        }
    }
}

impl<T: Field> FlatStatement<T> {
    pub fn apply_recursive_substitution(
        self,
        substitution: &HashMap<FlatVariable, FlatVariable>,
    ) -> FlatStatement<T> {
        self.apply_substitution(substitution, true)
    }

    pub fn apply_direct_substitution(
        self,
        substitution: &HashMap<FlatVariable, FlatVariable>,
    ) -> FlatStatement<T> {
        self.apply_substitution(substitution, false)
    }

    fn apply_substitution(
        self,
        substitution: &HashMap<FlatVariable, FlatVariable>,
        should_fallback: bool,
    ) -> FlatStatement<T> {
        match self {
            FlatStatement::Definition(id, x) => FlatStatement::Definition(
                id.apply_substitution(substitution, should_fallback),
                x.apply_substitution(substitution, should_fallback),
            ),
            FlatStatement::Return(x) => {
                FlatStatement::Return(x.apply_substitution(substitution, should_fallback))
            }
            FlatStatement::Condition(x, y) => FlatStatement::Condition(
                x.apply_substitution(substitution, should_fallback),
                y.apply_substitution(substitution, should_fallback),
            ),
            FlatStatement::Directive(d) => {
                let outputs = d
                    .outputs
                    .into_iter()
                    .map(|o| o.apply_substitution(substitution, should_fallback))
                    .collect();
                let inputs = d
                    .inputs
                    .into_iter()
                    .map(|i| i.apply_substitution(substitution, should_fallback))
                    .collect();

                FlatStatement::Directive(DirectiveStatement {
                    outputs,
                    inputs,
                    ..d
                })
            }
        }
    }
}

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub enum FlatExpression<T: Field> {
    Number(T),
    Identifier(FlatVariable),
    Add(Box<FlatExpression<T>>, Box<FlatExpression<T>>),
    Sub(Box<FlatExpression<T>>, Box<FlatExpression<T>>),
    Mult(Box<FlatExpression<T>>, Box<FlatExpression<T>>),
}

impl<T: Field> FlatExpression<T> {
    pub fn apply_recursive_substitution(
        self,
        substitution: &HashMap<FlatVariable, FlatVariable>,
    ) -> FlatExpression<T> {
        self.apply_substitution(substitution, true)
    }

    pub fn apply_direct_substitution(
        self,
        substitution: &HashMap<FlatVariable, FlatVariable>,
    ) -> FlatExpression<T> {
        self.apply_substitution(substitution, false)
    }

    fn apply_substitution(
        self,
        substitution: &HashMap<FlatVariable, FlatVariable>,
        should_fallback: bool,
    ) -> FlatExpression<T> {
        match self {
            e @ FlatExpression::Number(_) => e,
            FlatExpression::Identifier(id) => {
                FlatExpression::Identifier(id.apply_substitution(substitution, should_fallback))
            }
            FlatExpression::Add(e1, e2) => FlatExpression::Add(
                box e1.apply_substitution(substitution, should_fallback),
                box e2.apply_substitution(substitution, should_fallback),
            ),
            FlatExpression::Sub(e1, e2) => FlatExpression::Sub(
                box e1.apply_substitution(substitution, should_fallback),
                box e2.apply_substitution(substitution, should_fallback),
            ),
            FlatExpression::Mult(e1, e2) => FlatExpression::Mult(
                box e1.apply_substitution(substitution, should_fallback),
                box e2.apply_substitution(substitution, should_fallback),
            ),
        }
    }

    pub fn is_linear(&self) -> bool {
        match *self {
            FlatExpression::Number(_) | FlatExpression::Identifier(_) => true,
            FlatExpression::Add(ref x, ref y) | FlatExpression::Sub(ref x, ref y) => {
                x.is_linear() && y.is_linear()
            }
            FlatExpression::Mult(ref x, ref y) => match (x, y) {
                (box FlatExpression::Number(_), box FlatExpression::Number(_))
                | (box FlatExpression::Number(_), box FlatExpression::Identifier(_))
                | (box FlatExpression::Identifier(_), box FlatExpression::Number(_)) => true,
                _ => false,
            },
        }
    }
}

impl<T: Field> fmt::Display for FlatExpression<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FlatExpression::Number(ref i) => write!(f, "{}", i),
            FlatExpression::Identifier(ref var) => write!(f, "{}", var),
            FlatExpression::Add(ref lhs, ref rhs) => write!(f, "({} + {})", lhs, rhs),
            FlatExpression::Sub(ref lhs, ref rhs) => write!(f, "({} - {})", lhs, rhs),
            FlatExpression::Mult(ref lhs, ref rhs) => write!(f, "({} * {})", lhs, rhs),
        }
    }
}

impl<T: Field> fmt::Debug for FlatExpression<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FlatExpression::Number(ref i) => write!(f, "Num({})", i),
            FlatExpression::Identifier(ref var) => write!(f, "Ide({})", var),
            FlatExpression::Add(ref lhs, ref rhs) => write!(f, "Add({:?}, {:?})", lhs, rhs),
            FlatExpression::Sub(ref lhs, ref rhs) => write!(f, "Sub({:?}, {:?})", lhs, rhs),
            FlatExpression::Mult(ref lhs, ref rhs) => write!(f, "Mult({:?}, {:?})", lhs, rhs),
        }
    }
}

impl<T: Field> From<FlatVariable> for FlatExpression<T> {
    fn from(v: FlatVariable) -> FlatExpression<T> {
        FlatExpression::Identifier(v)
    }
}

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub struct FlatExpressionList<T: Field> {
    pub expressions: Vec<FlatExpression<T>>,
}

impl<T: Field> fmt::Display for FlatExpressionList<T> {
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

impl<T: Field> FlatExpressionList<T> {
    fn apply_substitution(
        self,
        substitution: &HashMap<FlatVariable, FlatVariable>,
        should_fallback: bool,
    ) -> FlatExpressionList<T> {
        FlatExpressionList {
            expressions: self
                .expressions
                .into_iter()
                .map(|e| e.apply_substitution(substitution, should_fallback))
                .collect(),
        }
    }

    pub fn apply_recursive_substitution(
        self,
        substitution: &HashMap<FlatVariable, FlatVariable>,
    ) -> FlatExpressionList<T> {
        self.apply_substitution(substitution, true)
    }

    pub fn apply_direct_substitution(
        self,
        substitution: &HashMap<FlatVariable, FlatVariable>,
    ) -> FlatExpressionList<T> {
        self.apply_substitution(substitution, false)
    }
}

impl<T: Field> fmt::Debug for FlatExpressionList<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ExpressionList({:?})", self.expressions)
    }
}

#[derive(PartialEq, Debug)]
pub struct Error {
    message: String,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use field::FieldPrime;

    #[test]
    fn is_linear() {
        let five = FlatExpression::Number(FieldPrime::from(5));
        let x = FlatExpression::Identifier(FlatVariable::new(42));
        let y = FlatExpression::Identifier(FlatVariable::new(21));
        // 5
        assert!(five.clone().is_linear());
        // x
        assert!(x.clone().is_linear());
        // x * 5
        assert!(FlatExpression::Mult(box x.clone(), box five.clone()).is_linear());
        // x * y not linear
        assert!(!FlatExpression::Mult(box x.clone(), box y.clone()).is_linear());
        // 5 * y
        assert!(FlatExpression::Mult(box five.clone(), box y.clone()).is_linear());
        // x - y
        assert!(FlatExpression::Sub(box x.clone(), box y.clone()).is_linear());
        // 5 * 5
        assert!(FlatExpression::Mult(box five.clone(), box five.clone()).is_linear());
    }

    #[should_panic]
    #[test]
    fn apply_substitution() {
        let h0 = vec![(42, 43), (21, 22)]
            .into_iter()
            .map(|(x, y)| (FlatVariable::new(x), FlatVariable::new(y)))
            .collect();

        let h1 = vec![(42, 43)]
            .into_iter()
            .map(|(x, y)| (FlatVariable::new(x), FlatVariable::new(y)))
            .collect();

        // 5*(_42 + _21)
        let e = FlatExpression::Mult(
            box FlatExpression::Number(FieldPrime::from(5)),
            box FlatExpression::Add(
                box FlatExpression::Identifier(FlatVariable::new(42)),
                box FlatExpression::Identifier(FlatVariable::new(21)),
            ),
        );

        // 5*(_43 + _22)
        let expected_direct = FlatExpression::Mult(
            box FlatExpression::Number(FieldPrime::from(5)),
            box FlatExpression::Add(
                box FlatExpression::Identifier(FlatVariable::new(43)),
                box FlatExpression::Identifier(FlatVariable::new(22)),
            ),
        );

        // 5*(_43 + _21)
        let expected_rec = FlatExpression::Mult(
            box FlatExpression::Number(FieldPrime::from(5)),
            box FlatExpression::Add(
                box FlatExpression::Identifier(FlatVariable::new(43)),
                box FlatExpression::Identifier(FlatVariable::new(21)),
            ),
        );

        assert_eq!(e.clone().apply_direct_substitution(&h0), expected_direct);
        assert_eq!(e.clone().apply_recursive_substitution(&h1), expected_rec);
        // direct substitution on h1 should panic as _21 is not a key
        e.apply_direct_substitution(&h1);
    }
}
