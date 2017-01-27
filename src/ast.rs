use std::fmt;

pub struct Prog {
    pub id: String,
    pub args: Vec<Parameter>,
    pub defs: Vec<Definition>,
}
impl fmt::Display for Prog {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}({}):\n{}", self.id, self.args.iter().map(|x| format!("{}", x)).collect::<Vec<_>>().join(","), self.defs.iter().map(|x| format!("\t{}", x)).collect::<Vec<_>>().join("\n"))
    }
}

pub enum Definition {
  Return(Expression),
  Definition(String, Expression),
  #[allow(dead_code)]
  IfElse(Expression, Expression, Option<Expression>),
}
impl fmt::Display for Definition {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Definition::Return(ref expr) => write!(f, "return {}", expr),
            Definition::Definition(ref lhs, ref rhs) => write!(f, "{} = {}", lhs, rhs),
            Definition::IfElse(_, _, _) => write!(f, "IfElse not implemented yet!"),
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
    #[allow(dead_code)]
    IfElse(Box<Expression>, Box<Expression>, Option<Box<Expression>>),
    NumberLiteral(i32),
    VariableReference(String),
}
impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Expression::Add(ref lhs, ref rhs) => write!(f, "{} + {}", lhs, rhs),
            Expression::Sub(ref lhs, ref rhs) => write!(f, "{} - {}", lhs, rhs),
            Expression::Mult(ref lhs, ref rhs) => write!(f, "{} * {}", lhs, rhs),
            Expression::Div(ref lhs, ref rhs) => write!(f, "{} / {}", lhs, rhs),
            Expression::Pow(ref lhs, ref rhs) => write!(f, "{}**{}", lhs, rhs),
            Expression::IfElse(_, _, _) => write!(f, "ifelse"),
            Expression::NumberLiteral(ref i) => write!(f, "{}", i),
            Expression::VariableReference(ref var) => write!(f, "{}", var),
        }
    }
}
