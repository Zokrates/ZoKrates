use std::fmt;
use std::collections::HashMap;

pub struct Prog {
    pub id: String,
    pub args: Vec<Parameter>,
    pub defs: Vec<Definition>,
}
impl Prog {
    pub fn get_witness(&self, inputs: Vec<i32>) -> HashMap<String, i32> {
        assert!(self.args.len() == inputs.len());
        let mut witness = HashMap::new();
        witness.insert("~one".to_string(), 1);
        for i in 0..self.args.len() {
            witness.insert(self.args[i].id.to_string(), inputs[i]);
        }
        for def in &self.defs {
            match *def {
                Definition::Return(ref expr) => {
                    let s = expr.solve(&witness);
                    witness.insert("~out".to_string(), s);
                },
                Definition::Definition(ref id, ref expr) => {
                    let s = expr.solve(&witness);
                    witness.insert(id.to_string(), s);
                },
            }
        }
        witness
    }
}
impl fmt::Display for Prog {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}({}):\n{}", self.id, self.args.iter().map(|x| format!("{}", x)).collect::<Vec<_>>().join(","), self.defs.iter().map(|x| format!("\t{}", x)).collect::<Vec<_>>().join("\n"))
    }
}

pub enum Definition {
  Return(Expression),
  Definition(String, Expression),
}
impl fmt::Display for Definition {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Definition::Return(ref expr) => write!(f, "return {}", expr),
            Definition::Definition(ref lhs, ref rhs) => write!(f, "{} = {}", lhs, rhs),
        }
    }
}
impl fmt::Debug for Definition {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

pub struct Parameter { pub id: String }
impl fmt::Display for Parameter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.id)
    }
}

#[derive(Clone)]
pub enum Expression {
    Add(Box<Expression>, Box<Expression>),
    Sub(Box<Expression>, Box<Expression>),
    Mult(Box<Expression>, Box<Expression>),
    Div(Box<Expression>, Box<Expression>),
    Pow(Box<Expression>, Box<Expression>),
    IfElse(Box<Condition>, Box<Expression>, Box<Expression>),
    NumberLiteral(i32),
    VariableReference(String),
}
impl Expression {
    fn solve(&self, inputs: &HashMap<String, i32>) -> i32 {
        match *self {
            Expression::Add(ref x, ref y) => x.solve(inputs) + y.solve(inputs),
            Expression::Sub(ref x, ref y) => x.solve(inputs) - y.solve(inputs),
            Expression::Mult(ref x, ref y) => x.solve(inputs) * y.solve(inputs),
            Expression::Div(ref x, ref y) => x.solve(inputs) / y.solve(inputs),
            Expression::Pow(ref x, ref y) => x.solve(inputs).pow(y.solve(inputs) as u32),
            Expression::NumberLiteral(x) => x,
            Expression::VariableReference(ref var) => inputs[var],
            Expression::IfElse(_, _, _) => unimplemented!(),
        }
    }
}
impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Expression::Add(ref lhs, ref rhs) => write!(f, "{} + {}", lhs, rhs),
            Expression::Sub(ref lhs, ref rhs) => write!(f, "{} - {}", lhs, rhs),
            Expression::Mult(ref lhs, ref rhs) => write!(f, "{} * {}", lhs, rhs),
            Expression::Div(ref lhs, ref rhs) => write!(f, "{} / {}", lhs, rhs),
            Expression::Pow(ref lhs, ref rhs) => write!(f, "{}**{}", lhs, rhs),
            Expression::IfElse(ref condition, ref consequent, ref alternative) => write!(f, "{} ? {} : {}", condition, consequent, alternative),
            Expression::NumberLiteral(ref i) => write!(f, "{}", i),
            Expression::VariableReference(ref var) => write!(f, "{}", var),
        }
    }
}

#[derive(Clone)]
pub enum Condition {
    Lt(Expression, Expression),
}
impl fmt::Display for Condition {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Condition::Lt(ref lhs, ref rhs) => write!(f, "{} < {}", lhs, rhs),
        }
    }
}
impl fmt::Debug for Condition {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}
