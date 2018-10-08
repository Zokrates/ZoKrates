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

use types::Signature;
use std::fmt;
use std::collections::{BTreeMap};
use field::Field;
use substitution::Substitution;
#[cfg(feature = "libsnark")]
use standard;
use helpers::{DirectiveStatement, Executable};

#[derive(Serialize, Deserialize, Clone)]
pub struct FlatProg<T: Field> {
    /// FlatFunctions of the program
    pub functions: Vec<FlatFunction<T>>,
}


impl<T: Field> FlatProg<T> {
    // only main flattened function is relevant here, as all other functions are unrolled into it
    #[allow(dead_code)] // I don't want to remove this
    pub fn get_witness(&self, inputs: Vec<T>) -> Result<BTreeMap<FlatVariable, T>, Error> {
        let main = self.functions.iter().find(|x| x.id == "main").unwrap();
        main.get_witness(inputs)
    }
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
            functions: vec![dr1cs.into()]
        }
    }
}


#[derive(Serialize, Deserialize, Clone, PartialEq)]
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

impl<T: Field> FlatFunction<T> {
    pub fn get_witness(&self, inputs: Vec<T>) -> Result<BTreeMap<FlatVariable, T>, Error> {
        assert!(self.arguments.len() == inputs.len());
        assert!(self.id == "main");
        let mut witness = BTreeMap::new();
        witness.insert(FlatVariable::one(), T::one());
        for (i, arg) in self.arguments.iter().enumerate() {
            witness.insert(arg.id, inputs[i].clone());
        }
        for statement in &self.statements {
            match *statement {
                FlatStatement::Return(ref list) => {
                    for (i, val) in list.expressions.iter().enumerate() {
                        let s = val.solve(&mut witness);
                        witness.insert(FlatVariable::public(i), s);
                    }
                }
                FlatStatement::Definition(ref id, ref expr) => {
                    let s = expr.solve(&mut witness);
                    witness.insert(id.clone(), s);
                },
                FlatStatement::Condition(ref lhs, ref rhs) => {
                    if lhs.solve(&mut witness) != rhs.solve(&mut witness) {
                        return Err(Error {
                            message: format!("Condition not satisfied: {} should equal {}", lhs, rhs)
                        });
                    }
                },
                FlatStatement::Directive(ref d) => {
                    let input_values: Vec<T> = d.inputs.iter().map(|i| witness.get(i).unwrap().clone()).collect();
                    match d.helper.execute(&input_values) {
                        Ok(res) => {
                            for (i, o) in d.outputs.iter().enumerate() {
                                witness.insert(o.clone(), res[i].clone());
                            }
                            continue;
                        },
                        Err(message) => {
                            return Err(Error {
                                message: message
                            })
                        }
                    };
                }
            }
        }
        Ok(witness)
    }
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
                .join(","),
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

/// Calculates a flattened function based on a R1CS (A, B, C) and returns that flattened function:
/// * The Rank 1 Constraint System (R1CS) is defined as:
/// * `<A,x>*<B,x> = <C,x>` for a witness `x`
/// * Since the matrices in R1CS are usually sparse, the following encoding is used:
/// * For each constraint (i.e., row in the R1CS), only non-zero values are supplied and encoded as a tuple (index, value).
///
/// # Arguments
///
/// * r1cs - R1CS in standard JSON data format

#[derive(Clone, Serialize, Deserialize, PartialEq)]
pub enum FlatStatement<T: Field> {
    Return(FlatExpressionList<T>),
    Condition(FlatExpression<T>, FlatExpression<T>),
    Definition(FlatVariable, FlatExpression<T>),
    Directive(DirectiveStatement)
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
            FlatStatement::Condition(ref lhs, ref rhs) => write!(f, "FlatCondition({:?}, {:?})", lhs, rhs),
            FlatStatement::Directive(ref d) => write!(f, "{:?}", d),
        }
    }
}

impl<T: Field> FlatStatement<T> {
    pub fn apply_recursive_substitution(self, substitution: &Substitution) -> FlatStatement<T> {
        self.apply_substitution(substitution, true)
    }

    pub fn apply_direct_substitution(self, substitution: &Substitution) -> FlatStatement<T> {
        self.apply_substitution(substitution, false)
    }

    fn apply_substitution(self, substitution: &Substitution, should_fallback: bool) -> FlatStatement<T> {
        match self {
            FlatStatement::Definition(id, x) => FlatStatement::Definition(
                id.apply_substitution(substitution, should_fallback), 
                x.apply_substitution(substitution, should_fallback)
            ),
            FlatStatement::Return(x) => FlatStatement::Return(
                x.apply_substitution(substitution, should_fallback)
            ),
            FlatStatement::Condition(x, y) => {
                FlatStatement::Condition(
                    x.apply_substitution(substitution, should_fallback),
                    y.apply_substitution(substitution, should_fallback)
                )
            },
            FlatStatement::Directive(d) => {
                let outputs = d.outputs.into_iter().map(|o| substitution.get(&o).unwrap_or(o)).collect();
                let inputs = d.inputs.into_iter().map(|i| substitution.get(&i).unwrap()).collect();

                FlatStatement::Directive(
                    DirectiveStatement {
                        outputs,
                        inputs,
                        ..d
                    }
                )
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
    Div(Box<FlatExpression<T>>, Box<FlatExpression<T>>),
    Mult(Box<FlatExpression<T>>, Box<FlatExpression<T>>)
}

impl<T: Field> FlatExpression<T> {
    pub fn apply_recursive_substitution(self, substitution: &Substitution) -> FlatExpression<T> {
        self.apply_substitution(substitution, true)
    }

    pub fn apply_direct_substitution(self, substitution: &Substitution) -> FlatExpression<T> {
        self.apply_substitution(substitution, false)
    }

    fn apply_substitution(self, substitution: &Substitution, should_fallback: bool) -> FlatExpression<T> {
        match self {
            e @ FlatExpression::Number(_) => e,
            FlatExpression::Identifier(id) => FlatExpression::Identifier(id.apply_substitution(substitution, should_fallback)),
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
            FlatExpression::Div(e1, e2) => FlatExpression::Div(
                box e1.apply_substitution(substitution, should_fallback),
                box e2.apply_substitution(substitution, should_fallback),
            )
        }
    }

    fn solve(&self, inputs: &mut BTreeMap<FlatVariable, T>) -> T {
        match *self {
            FlatExpression::Number(ref x) => x.clone(),
            FlatExpression::Identifier(ref var) => {
                match inputs.get(var) {
                    Some(v) => v.clone(),
                    None => 
                        panic!(
                            "Variable {:?} is undeclared in witness: {:?}",
                            var,
                            inputs
                        )
                }
            }
            FlatExpression::Add(ref x, ref y) => x.solve(inputs) + y.solve(inputs),
            FlatExpression::Sub(ref x, ref y) => x.solve(inputs) - y.solve(inputs),
            FlatExpression::Mult(ref x, ref y) => x.solve(inputs) * y.solve(inputs),
            FlatExpression::Div(ref x, ref y) => x.solve(inputs) / y.solve(inputs),
        }
    }

    pub fn is_linear(&self) -> bool {
        match *self {
            FlatExpression::Number(_) | FlatExpression::Identifier(_) => true,
            FlatExpression::Add(ref x, ref y) | FlatExpression::Sub(ref x, ref y) => {
                x.is_linear() && y.is_linear()
            }
            FlatExpression::Mult(ref x, ref y) | FlatExpression::Div(ref x, ref y) => {
                match (x.clone(), y.clone()) {
                    (box FlatExpression::Number(_), box FlatExpression::Number(_)) |
                    (box FlatExpression::Number(_), box FlatExpression::Identifier(_)) |
                    (box FlatExpression::Identifier(_), box FlatExpression::Number(_)) => true,
                    _ => false,
                }
            }
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
            FlatExpression::Div(ref lhs, ref rhs) => write!(f, "({} / {})", lhs, rhs),
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
            FlatExpression::Div(ref lhs, ref rhs) => write!(f, "Div({:?}, {:?})", lhs, rhs),
        }
    }
}

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub struct FlatExpressionList<T: Field> {
    pub expressions: Vec<FlatExpression<T>>
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
    fn apply_substitution(self, substitution: &Substitution, should_fallback: bool) -> FlatExpressionList<T> {
        FlatExpressionList {
            expressions: self.expressions.into_iter().map(|e| e.apply_substitution(substitution, should_fallback)).collect()
        }
    }

    pub fn apply_recursive_substitution(self, substitution: &Substitution) -> FlatExpressionList<T> {
        self.apply_substitution(substitution, true)
    }

    pub fn apply_direct_substitution(self, substitution: &Substitution) -> FlatExpressionList<T> {
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
    message: String
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}
