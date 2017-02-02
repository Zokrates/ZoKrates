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
                    let s = expr.solve(&mut witness);
                    witness.insert("~out".to_string(), s);
                },
                Definition::Definition(ref id, ref expr) => {
                    let s = expr.solve(&mut witness);
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
    NumberLiteral(i32),
    VariableReference(String),
    Add(Box<Expression>, Box<Expression>),
    Sub(Box<Expression>, Box<Expression>),
    Mult(Box<Expression>, Box<Expression>),
    Div(Box<Expression>, Box<Expression>),
    Pow(Box<Expression>, Box<Expression>),
    IfElse(Box<Condition>, Box<Expression>, Box<Expression>),
}
impl Expression {
    fn solve(&self, inputs: &mut HashMap<String, i32>) -> i32 {
        match *self {
            Expression::NumberLiteral(x) => x,
            Expression::VariableReference(ref var) => {
                if let None = inputs.get(var) {
                    if var.contains("_b") {
                        let var_name = var.split("_b").collect::<Vec<_>>()[0];
                        let mut num = inputs[var_name];
                        assert!(num >= 0, format!("num < 0: {}", num));
                        // TODO support negative numbers with two's complement!?
                        for i in (0..8).rev() {
                            if 2i32.pow(i) <= num {
                                num -= 2i32.pow(i);
                                inputs.insert(format!("{}_b{}", &var_name, i), 1);
                            } else {
                                inputs.insert(format!("{}_b{}", &var_name, i), 0);
                            }
                        }
                        assert_eq!(num, 0);
                    } else {
                        panic!("Variable not found in inputs: {}", var);
                    }
                }
                inputs[var]
            },
            Expression::Add(ref x, ref y) => x.solve(inputs) + y.solve(inputs),
            Expression::Sub(ref x, ref y) => x.solve(inputs) - y.solve(inputs),
            Expression::Mult(ref x, ref y) => x.solve(inputs) * y.solve(inputs),
            Expression::Div(ref x, ref y) => x.solve(inputs) / y.solve(inputs),
            Expression::Pow(ref x, ref y) => x.solve(inputs).pow(y.solve(inputs) as u32),
            Expression::IfElse(ref condition, ref consequent, ref alternative)
                => if condition.solve(inputs) { consequent.solve(inputs) } else { alternative.solve(inputs) },
        }
    }

    pub fn is_linear(&self) -> bool {
        match *self {
            Expression::NumberLiteral(_) |
            Expression::VariableReference(_) => true,
            Expression::Add(ref x, ref y) |
            Expression::Sub(ref x, ref y) => x.is_linear() && y.is_linear(),
            Expression::Mult(ref x, ref y) |
            Expression::Div(ref x, ref y) => match (x.clone(), y.clone()) {
                (box Expression::NumberLiteral(_), box Expression::NumberLiteral(_)) |
                (box Expression::NumberLiteral(_), box Expression::VariableReference(_)) |
                (box Expression::VariableReference(_), box Expression::NumberLiteral(_)) => true,
                _ => false,
            },
            _ => false,
        }
    }

    pub fn is_flattened(&self) -> bool {
        match *self {
            Expression::NumberLiteral(_) |
            Expression::VariableReference(_) => true,
            Expression::Add(ref x, ref y) |
            Expression::Sub(ref x, ref y) => x.is_linear() && y.is_linear(),
            Expression::Mult(ref x, ref y) |
            Expression::Div(ref x, ref y) => x.is_linear() && y.is_linear(),
            _ => false,
        }
    }
}
impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Expression::NumberLiteral(ref i) => write!(f, "{}", i),
            Expression::VariableReference(ref var) => write!(f, "{}", var),
            Expression::Add(ref lhs, ref rhs) => write!(f, "({} + {})", lhs, rhs),
            Expression::Sub(ref lhs, ref rhs) => write!(f, "({} - {})", lhs, rhs),
            Expression::Mult(ref lhs, ref rhs) => write!(f, "({} * {})", lhs, rhs),
            Expression::Div(ref lhs, ref rhs) => write!(f, "({} / {})", lhs, rhs),
            Expression::Pow(ref lhs, ref rhs) => write!(f, "{}**{}", lhs, rhs),
            Expression::IfElse(ref condition, ref consequent, ref alternative) => write!(f, "{} ? {} : {}", condition, consequent, alternative),
        }
    }
}

#[derive(Clone)]
pub enum Condition {
    Lt(Expression, Expression),
}
impl Condition {
    fn solve(&self, inputs: &mut HashMap<String, i32>) -> bool {
        match *self {
            Condition::Lt(ref lhs, ref rhs) => lhs.solve(inputs) < rhs.solve(inputs),
        }
    }
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
