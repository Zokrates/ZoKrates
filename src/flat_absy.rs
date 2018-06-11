//! Module containing structs and enums to represent a program.
//!
//! @file absy.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

const BINARY_SEPARATOR: &str = "_b";

use absy::Expression;
use std::fmt;
use std::collections::{BTreeMap};
use field::Field;
use parameter::Parameter;
use substitution::Substitution;
use executable::{Executable, Sha256Libsnark};
use standard;

#[derive(Serialize, Deserialize, Clone)]
pub struct FlatProg<T: Field> {
    /// FlatFunctions of the program
    pub functions: Vec<FlatFunction<T>>,
}


impl<T: Field> FlatProg<T> {
    // only main flattened function is relevant here, as all other functions are unrolled into it
    #[allow(dead_code)] // I don't want to remove this
    pub fn get_witness(&self, inputs: Vec<T>) -> Result<BTreeMap<String, T>, Error> {
        let main = self.functions.iter().find(|x| x.id == "main").unwrap();
        main.get_witness(inputs).unwrap()
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

impl<T: Field> From<standard::R1CS> for FlatProg<T> {
    fn from(r1cs: standard::R1CS) -> Self {
        FlatProg {
            functions: vec![r1cs.into()]
        }
    }
}


#[derive(Serialize, Deserialize, Clone, PartialEq)]
pub struct FlatFunction<T: Field> {
    /// Name of the program
    pub id: String,
    /// Arguments of the function
    pub arguments: Vec<Parameter>,
    /// Vector of statements that are executed when running the function
    pub statements: Vec<FlatStatement<T>>,
    /// number of returns
    pub return_count: usize,
}

impl<T: Field> FlatFunction<T> {
    pub fn get_witness(&self, inputs: Vec<T>) -> Result<BTreeMap<String, T>, Error> {
        assert!(self.arguments.len() == inputs.len());
        let mut witness = BTreeMap::new();
        witness.insert("~one".to_string(), T::one());
        for (i, arg) in self.arguments.iter().enumerate() {
            witness.insert(arg.id.to_string(), inputs[i].clone());
        }
        for statement in &self.statements {
            match *statement {
                FlatStatement::Return(ref list) => {
                    for (i, val) in list.expressions.iter().enumerate() {
                        let s = val.solve(&mut witness);
                        witness.insert(format!("~out_{}", i).to_string(), s);
                    }
                }
                FlatStatement::Definition(ref id, ref expr) => {
                    let s = expr.solve(&mut witness);
                    witness.insert(id.to_string(), s);
                },
                FlatStatement::Compiler(ref id, ref expr) => {
                    let s = expr.solve(&mut witness);
                    witness.insert(id.to_string(), s);
                },
                FlatStatement::Condition(ref lhs, ref rhs) => {
                    if lhs.solve(&mut witness) != rhs.solve(&mut witness) {
                        return Err(Error {
                            message: format!("Condition not satisfied: {} should equal {}", lhs, rhs)
                        });
                    }
                },
                FlatStatement::Directive(ref outputs, ref inputs, ref exe) => {
                    let input_values: Vec<T> = inputs.into_iter().map(|i| witness.get(i).unwrap().clone()).collect();
                    match exe.execute(&input_values) {
                        Ok(res) => {
                            for (i, o) in outputs.iter().enumerate() {
                                witness.insert(o.to_string(), res[i].clone());
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
            "FlatFunction(id: {:?}, arguments: {:?}, ...):\n{}",
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
    Compiler(String, Expression<T>),
    Definition(String, FlatExpression<T>),
    Directive(Vec<String>, Vec<String>, Sha256Libsnark)
}

impl<T: Field> fmt::Display for FlatStatement<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FlatStatement::Definition(ref lhs, ref rhs) => write!(f, "{} = {}", lhs, rhs),
            FlatStatement::Return(ref expr) => write!(f, "return {}", expr),
            FlatStatement::Condition(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            FlatStatement::Compiler(ref lhs, ref rhs) => write!(f, "# {} = {}", lhs, rhs),
            FlatStatement::Directive(ref outputs, ref inputs, _) => write!(f, "# {} = Sha256Libsnark({})", outputs.join(", "), inputs.join(", ")),
        }
    }
}

impl<T: Field> fmt::Debug for FlatStatement<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FlatStatement::Definition(ref lhs, ref rhs) => write!(f, "{} = {}", lhs, rhs),
            FlatStatement::Return(ref expr) => write!(f, "FlatReturn({:?})", expr),
            FlatStatement::Condition(ref lhs, ref rhs) => write!(f, "FlatCondition({:?}, {:?})", lhs, rhs),
            FlatStatement::Compiler(ref lhs, ref rhs) => write!(f, "Compiler({:?}, {:?})", lhs, rhs),
            FlatStatement::Directive(ref outputs, ref inputs, _) => write!(f, "Sha256Libsnark({:?}, {:?})", outputs, inputs),
        }
    }
}

impl<T: Field> FlatStatement<T> {
    pub fn apply_substitution(&self, substitution: &Substitution) -> FlatStatement<T> {
        match *self {
            FlatStatement::Definition(ref id, ref x) => FlatStatement::Definition(
                match substitution.get(id) { 
                    Some(z) => z.clone(), 
                    None => id.clone() 
                }, 
                x.apply_substitution(substitution)
            ),
            FlatStatement::Return(ref x) => FlatStatement::Return(x.apply_substitution(substitution)),
            FlatStatement::Compiler(ref lhs, ref rhs) => FlatStatement::Compiler(match substitution.get(lhs) { 
                    Some(z) => z.clone(), 
                    None => lhs.clone() 
                }, rhs.clone().apply_substitution(substitution)),
            FlatStatement::Condition(ref x, ref y) => {
                FlatStatement::Condition(x.apply_substitution(substitution), y.apply_substitution(substitution))
            },
            FlatStatement::Directive(ref outputs, ref inputs, ref exe) => {
                let new_outputs = outputs.iter().map(|o| match substitution.get(o) {
                    Some(z) => z.clone(),
                    None => o.clone()
                }).collect();
                let new_inputs = inputs.iter().map(|i| substitution.get(i).unwrap()).collect();
                FlatStatement::Directive(new_outputs, new_inputs, exe.clone())
            }
        }
    }
}

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub enum FlatExpression<T: Field> {
    Number(T),
    Identifier(String),
    Add(Box<FlatExpression<T>>, Box<FlatExpression<T>>),
    Sub(Box<FlatExpression<T>>, Box<FlatExpression<T>>),
    Div(Box<FlatExpression<T>>, Box<FlatExpression<T>>),
    Mult(Box<FlatExpression<T>>, Box<FlatExpression<T>>)
}

impl<T: Field> FlatExpression<T> {
    pub fn apply_substitution(&self, substitution: &Substitution) -> FlatExpression<T> {
        match *self {
            ref e @ FlatExpression::Number(_) => e.clone(),
            FlatExpression::Identifier(ref v) => {
                let mut new_name = v.to_string();
                loop {
                    match substitution.get(&new_name) {
                        Some(x) => new_name = x.to_string(),
                        None => return FlatExpression::Identifier(new_name),
                    }
                }
            }
            FlatExpression::Add(ref e1, ref e2) => FlatExpression::Add(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            FlatExpression::Sub(ref e1, ref e2) => FlatExpression::Sub(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            FlatExpression::Mult(ref e1, ref e2) => FlatExpression::Mult(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            FlatExpression::Div(ref e1, ref e2) => FlatExpression::Div(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            )

        }
    }

    fn solve(&self, inputs: &mut BTreeMap<String, T>) -> T {
        match *self {
            FlatExpression::Number(ref x) => x.clone(),
            FlatExpression::Identifier(ref var) => {
                if let None = inputs.get(var) {
                    if var.contains(BINARY_SEPARATOR) {
                        let var_name = var.split(BINARY_SEPARATOR).collect::<Vec<_>>()[0];
                        let mut num = inputs[var_name].clone();
                        let bits = T::get_required_bits();
                        for i in (0..bits).rev() {
                            if T::from(2).pow(i) <= num {
                                num = num - T::from(2).pow(i);
                                inputs.insert(format!("{}{}{}", &var_name, BINARY_SEPARATOR, i), T::one());
                            } else {
                                inputs.insert(format!("{}{}{}", &var_name, BINARY_SEPARATOR, i), T::zero());
                            }
                        }
                        assert_eq!(num, T::zero());
                    } else {
                        panic!(
                            "Variable {:?} is undeclared in inputs: {:?}",
                            var,
                            inputs
                        );
                    }
                }
                inputs[var].clone()
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
    pub fn apply_substitution(&self, substitution: &Substitution) -> FlatExpressionList<T> {
        let expressions: Vec<FlatExpression<T>> = self.expressions.iter().map(|e| e.apply_substitution(substitution)).collect();
        FlatExpressionList {
            expressions: expressions
        }
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
