pub mod folder;
mod from_typed;
mod identifier;
mod parameter;
pub mod result_folder;
pub mod types;
mod uint;
mod variable;

pub use self::parameter::Parameter;
pub use self::types::Type;
pub use self::variable::Variable;
use crate::common::{FlatEmbed, FormatString};
use crate::typed::ConcreteType;
pub use crate::zir::uint::{ShouldReduce, UExpression, UExpressionInner, UMetadata};

use crate::zir::types::Signature;
use std::convert::TryFrom;
use std::fmt;
use zokrates_field::Field;

pub use self::folder::Folder;
pub use self::identifier::{Identifier, SourceIdentifier};

/// A typed program as a collection of modules, one of them being the main
#[derive(PartialEq, Eq, Debug)]
pub struct ZirProgram<'ast, T> {
    pub main: ZirFunction<'ast, T>,
}

impl<'ast, T: fmt::Display> fmt::Display for ZirProgram<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.main)
    }
}
/// A typed function
#[derive(Clone, PartialEq, Eq)]
pub struct ZirFunction<'ast, T> {
    /// Arguments of the function
    pub arguments: Vec<Parameter<'ast>>,
    /// Vector of statements that are executed when running the function
    pub statements: Vec<ZirStatement<'ast, T>>,
    /// function signature
    pub signature: Signature,
}

impl<'ast, T: fmt::Display> fmt::Display for ZirFunction<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(
            f,
            "({}) -> ({}) {{",
            self.arguments
                .iter()
                .map(|x| format!("{}", x))
                .collect::<Vec<_>>()
                .join(", "),
            self.signature
                .outputs
                .iter()
                .map(|x| format!("{}", x))
                .collect::<Vec<_>>()
                .join(", ")
        )?;

        for s in &self.statements {
            s.fmt_indented(f, 1)?;
            writeln!(f)?;
        }

        writeln!(f, "}}")
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for ZirFunction<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "ZirFunction(arguments: {:?}, ...):\n{}",
            self.arguments,
            self.statements
                .iter()
                .map(|x| format!("\t{:?}", x))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

pub type ZirAssignee<'ast> = Variable<'ast>;

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub enum RuntimeError {
    SourceAssertion(String),
    SelectRangeCheck,
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeError::SourceAssertion(message) => write!(f, "{}", message),
            RuntimeError::SelectRangeCheck => write!(f, "Range check on array access"),
        }
    }
}

impl RuntimeError {
    pub fn mock() -> Self {
        RuntimeError::SourceAssertion(String::default())
    }
}

/// A statement in a `ZirFunction`
#[derive(Clone, PartialEq, Hash, Eq, Debug)]
pub enum ZirStatement<'ast, T> {
    Return(Vec<ZirExpression<'ast, T>>),
    Definition(ZirAssignee<'ast>, ZirExpression<'ast, T>),
    IfElse(
        BooleanExpression<'ast, T>,
        Vec<ZirStatement<'ast, T>>,
        Vec<ZirStatement<'ast, T>>,
    ),
    Assertion(BooleanExpression<'ast, T>, RuntimeError),
    MultipleDefinition(Vec<ZirAssignee<'ast>>, ZirExpressionList<'ast, T>),
    Log(
        FormatString,
        Vec<(ConcreteType, Vec<ZirExpression<'ast, T>>)>,
    ),
}

impl<'ast, T: fmt::Display> fmt::Display for ZirStatement<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.fmt_indented(f, 0)
    }
}

impl<'ast, T: fmt::Display> ZirStatement<'ast, T> {
    fn fmt_indented(&self, f: &mut fmt::Formatter, depth: usize) -> fmt::Result {
        write!(f, "{}", "\t".repeat(depth))?;
        match self {
            ZirStatement::Return(ref exprs) => {
                write!(f, "return ")?;
                for (i, expr) in exprs.iter().enumerate() {
                    write!(f, "{}", expr)?;
                    if i < exprs.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ";")
            }
            ZirStatement::Definition(ref lhs, ref rhs) => {
                write!(f, "{} = {};", lhs, rhs)
            }
            ZirStatement::IfElse(ref condition, ref consequence, ref alternative) => {
                writeln!(f, "if {} {{", condition)?;
                for s in consequence {
                    s.fmt_indented(f, depth + 1)?;
                    writeln!(f)?;
                }
                writeln!(f, "{}}} else {{", "\t".repeat(depth))?;
                for s in alternative {
                    s.fmt_indented(f, depth + 1)?;
                    writeln!(f)?;
                }
                write!(f, "{}}};", "\t".repeat(depth))
            }
            ZirStatement::Assertion(ref e, ref error) => {
                write!(f, "assert({}", e)?;
                match error {
                    RuntimeError::SourceAssertion(message) => write!(f, ", \"{}\");", message),
                    error => write!(f, "); // {}", error),
                }
            }
            ZirStatement::MultipleDefinition(ref ids, ref rhs) => {
                for (i, id) in ids.iter().enumerate() {
                    write!(f, "{}", id)?;
                    if i < ids.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, " = {};", rhs)
            }
            ZirStatement::Log(ref l, ref expressions) => write!(
                f,
                "log(\"{}\"), {})",
                l,
                expressions
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

pub trait Typed {
    fn get_type(&self) -> Type;
}

/// A typed expression
#[derive(Clone, PartialEq, Hash, Eq)]
pub enum ZirExpression<'ast, T> {
    Boolean(BooleanExpression<'ast, T>),
    FieldElement(FieldElementExpression<'ast, T>),
    Uint(UExpression<'ast, T>),
}

impl<'ast, T: Field> From<BooleanExpression<'ast, T>> for ZirExpression<'ast, T> {
    fn from(e: BooleanExpression<'ast, T>) -> ZirExpression<T> {
        ZirExpression::Boolean(e)
    }
}

impl<'ast, T: Field> From<FieldElementExpression<'ast, T>> for ZirExpression<'ast, T> {
    fn from(e: FieldElementExpression<'ast, T>) -> ZirExpression<T> {
        ZirExpression::FieldElement(e)
    }
}

impl<'ast, T: Field> From<UExpression<'ast, T>> for ZirExpression<'ast, T> {
    fn from(e: UExpression<'ast, T>) -> ZirExpression<T> {
        ZirExpression::Uint(e)
    }
}

impl<'ast, T: fmt::Display> fmt::Display for ZirExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ZirExpression::Boolean(ref e) => write!(f, "{}", e),
            ZirExpression::FieldElement(ref e) => write!(f, "{}", e),
            ZirExpression::Uint(ref e) => write!(f, "{}", e),
        }
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for ZirExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ZirExpression::Boolean(ref e) => write!(f, "{:?}", e),
            ZirExpression::FieldElement(ref e) => write!(f, "{:?}", e),
            ZirExpression::Uint(ref e) => write!(f, "{:?}", e),
        }
    }
}

impl<'ast, T: Field> Typed for ZirExpression<'ast, T> {
    fn get_type(&self) -> Type {
        match *self {
            ZirExpression::Boolean(ref e) => e.get_type(),
            ZirExpression::FieldElement(ref e) => e.get_type(),
            ZirExpression::Uint(ref e) => e.get_type(),
        }
    }
}

impl<'ast, T: Field> Typed for FieldElementExpression<'ast, T> {
    fn get_type(&self) -> Type {
        Type::FieldElement
    }
}

impl<'ast, T: Field> Typed for UExpression<'ast, T> {
    fn get_type(&self) -> Type {
        Type::Uint(self.bitwidth)
    }
}

impl<'ast, T: Field> Typed for BooleanExpression<'ast, T> {
    fn get_type(&self) -> Type {
        Type::Boolean
    }
}

pub trait MultiTyped {
    fn get_types(&self) -> &Vec<Type>;
}

#[derive(Clone, PartialEq, Hash, Eq)]
pub enum ZirExpressionList<'ast, T> {
    EmbedCall(FlatEmbed, Vec<u32>, Vec<ZirExpression<'ast, T>>),
}

/// An expression of type `field`
#[derive(Clone, PartialEq, Hash, Eq, Debug)]
pub enum FieldElementExpression<'ast, T> {
    Number(T),
    Identifier(Identifier<'ast>),
    Select(Vec<Self>, Box<UExpression<'ast, T>>),
    Add(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    Sub(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    Mult(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    Div(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    Pow(
        Box<FieldElementExpression<'ast, T>>,
        Box<UExpression<'ast, T>>,
    ),
    Conditional(
        Box<BooleanExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
}

/// An expression of type `bool`
#[derive(Clone, PartialEq, Hash, Eq, Debug)]
pub enum BooleanExpression<'ast, T> {
    Value(bool),
    Identifier(Identifier<'ast>),
    Select(Vec<Self>, Box<UExpression<'ast, T>>),
    FieldLt(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    FieldLe(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    FieldGe(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    FieldGt(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    FieldEq(
        Box<FieldElementExpression<'ast, T>>,
        Box<FieldElementExpression<'ast, T>>,
    ),
    UintLt(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    UintLe(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    UintGe(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    UintGt(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    UintEq(Box<UExpression<'ast, T>>, Box<UExpression<'ast, T>>),
    BoolEq(
        Box<BooleanExpression<'ast, T>>,
        Box<BooleanExpression<'ast, T>>,
    ),
    Or(
        Box<BooleanExpression<'ast, T>>,
        Box<BooleanExpression<'ast, T>>,
    ),
    And(
        Box<BooleanExpression<'ast, T>>,
        Box<BooleanExpression<'ast, T>>,
    ),
    Not(Box<BooleanExpression<'ast, T>>),
    Conditional(
        Box<BooleanExpression<'ast, T>>,
        Box<BooleanExpression<'ast, T>>,
        Box<BooleanExpression<'ast, T>>,
    ),
}

pub struct ConjunctionIterator<T> {
    current: Vec<T>,
}

impl<'ast, T> Iterator for ConjunctionIterator<BooleanExpression<'ast, T>> {
    type Item = BooleanExpression<'ast, T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.current.pop().and_then(|n| match n {
            BooleanExpression::And(box left, box right) => {
                self.current.push(left);
                self.current.push(right);
                self.next()
            }
            n => Some(n),
        })
    }
}

impl<'ast, T> BooleanExpression<'ast, T> {
    pub fn into_conjunction_iterator(self) -> ConjunctionIterator<Self> {
        ConjunctionIterator {
            current: vec![self],
        }
    }
}

// Downcasts
impl<'ast, T> TryFrom<ZirExpression<'ast, T>> for FieldElementExpression<'ast, T> {
    type Error = ();

    fn try_from(
        te: ZirExpression<'ast, T>,
    ) -> Result<FieldElementExpression<'ast, T>, Self::Error> {
        match te {
            ZirExpression::FieldElement(e) => Ok(e),
            _ => Err(()),
        }
    }
}

impl<'ast, T> TryFrom<ZirExpression<'ast, T>> for BooleanExpression<'ast, T> {
    type Error = ();

    fn try_from(te: ZirExpression<'ast, T>) -> Result<BooleanExpression<'ast, T>, Self::Error> {
        match te {
            ZirExpression::Boolean(e) => Ok(e),
            _ => Err(()),
        }
    }
}

impl<'ast, T> TryFrom<ZirExpression<'ast, T>> for UExpression<'ast, T> {
    type Error = ();

    fn try_from(te: ZirExpression<'ast, T>) -> Result<UExpression<'ast, T>, Self::Error> {
        match te {
            ZirExpression::Uint(e) => Ok(e),
            _ => Err(()),
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for FieldElementExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FieldElementExpression::Number(ref i) => write!(f, "{}", i),
            FieldElementExpression::Identifier(ref var) => write!(f, "{}", var),
            FieldElementExpression::Select(ref a, ref i) => write!(
                f,
                "[{}][{}]",
                a.iter()
                    .map(|a| a.to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
                i
            ),
            FieldElementExpression::Add(ref lhs, ref rhs) => write!(f, "({} + {})", lhs, rhs),
            FieldElementExpression::Sub(ref lhs, ref rhs) => write!(f, "({} - {})", lhs, rhs),
            FieldElementExpression::Mult(ref lhs, ref rhs) => write!(f, "({} * {})", lhs, rhs),
            FieldElementExpression::Div(ref lhs, ref rhs) => write!(f, "({} / {})", lhs, rhs),
            FieldElementExpression::Pow(ref lhs, ref rhs) => write!(f, "{}**{}", lhs, rhs),
            FieldElementExpression::Conditional(ref condition, ref consequent, ref alternative) => {
                write!(
                    f,
                    "if {} {{ {} }} else {{ {} }}",
                    condition, consequent, alternative
                )
            }
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for UExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.inner {
            UExpressionInner::Value(ref v) => write!(f, "{}", v),
            UExpressionInner::Identifier(ref var) => write!(f, "{}", var),
            UExpressionInner::Select(ref a, ref i) => write!(
                f,
                "[{}][{}]",
                a.iter()
                    .map(|a| a.to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
                i
            ),
            UExpressionInner::Add(ref lhs, ref rhs) => write!(f, "({} + {})", lhs, rhs),
            UExpressionInner::Sub(ref lhs, ref rhs) => write!(f, "({} - {})", lhs, rhs),
            UExpressionInner::Mult(ref lhs, ref rhs) => write!(f, "({} * {})", lhs, rhs),
            UExpressionInner::Div(ref lhs, ref rhs) => write!(f, "({} * {})", lhs, rhs),
            UExpressionInner::Rem(ref lhs, ref rhs) => write!(f, "({} % {})", lhs, rhs),
            UExpressionInner::Xor(ref lhs, ref rhs) => write!(f, "({} ^ {})", lhs, rhs),
            UExpressionInner::And(ref lhs, ref rhs) => write!(f, "({} & {})", lhs, rhs),
            UExpressionInner::Or(ref lhs, ref rhs) => write!(f, "({} | {})", lhs, rhs),
            UExpressionInner::LeftShift(ref e, ref by) => write!(f, "({} << {})", e, by),
            UExpressionInner::RightShift(ref e, ref by) => write!(f, "({} >> {})", e, by),
            UExpressionInner::Not(ref e) => write!(f, "!{}", e),
            UExpressionInner::Conditional(ref condition, ref consequent, ref alternative) => {
                write!(
                    f,
                    "if {} {{ {} }} else {{ {} }}",
                    condition, consequent, alternative
                )
            }
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for BooleanExpression<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            BooleanExpression::Identifier(ref var) => write!(f, "{}", var),
            BooleanExpression::Value(b) => write!(f, "{}", b),
            BooleanExpression::Select(ref a, ref i) => write!(
                f,
                "[{}][{}]",
                a.iter()
                    .map(|a| a.to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
                i
            ),
            BooleanExpression::FieldLt(ref lhs, ref rhs) => write!(f, "{} < {}", lhs, rhs),
            BooleanExpression::FieldLe(ref lhs, ref rhs) => write!(f, "{} <= {}", lhs, rhs),
            BooleanExpression::FieldGe(ref lhs, ref rhs) => write!(f, "{} >= {}", lhs, rhs),
            BooleanExpression::FieldGt(ref lhs, ref rhs) => write!(f, "{} > {}", lhs, rhs),
            BooleanExpression::UintLt(ref lhs, ref rhs) => write!(f, "{} < {}", lhs, rhs),
            BooleanExpression::UintLe(ref lhs, ref rhs) => write!(f, "{} <= {}", lhs, rhs),
            BooleanExpression::UintGe(ref lhs, ref rhs) => write!(f, "{} >= {}", lhs, rhs),
            BooleanExpression::UintGt(ref lhs, ref rhs) => write!(f, "{} > {}", lhs, rhs),
            BooleanExpression::FieldEq(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            BooleanExpression::BoolEq(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            BooleanExpression::UintEq(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            BooleanExpression::Or(ref lhs, ref rhs) => write!(f, "{} || {}", lhs, rhs),
            BooleanExpression::And(ref lhs, ref rhs) => write!(f, "{} && {}", lhs, rhs),
            BooleanExpression::Not(ref exp) => write!(f, "!{}", exp),
            BooleanExpression::Conditional(ref condition, ref consequent, ref alternative) => {
                write!(
                    f,
                    "if {} {{ {} }} else {{ {} }}",
                    condition, consequent, alternative
                )
            }
        }
    }
}

impl<'ast, T: fmt::Display> fmt::Display for ZirExpressionList<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ZirExpressionList::EmbedCall(ref embed, ref generics, ref p) => {
                write!(
                    f,
                    "{}{}(",
                    embed.id(),
                    if generics.is_empty() {
                        "".into()
                    } else {
                        format!(
                            "::<{}>",
                            generics
                                .iter()
                                .map(|g| g.to_string())
                                .collect::<Vec<_>>()
                                .join(", ")
                        )
                    }
                )?;
                for (i, param) in p.iter().enumerate() {
                    write!(f, "{}", param)?;
                    if i < p.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
        }
    }
}

impl<'ast, T: fmt::Debug> fmt::Debug for ZirExpressionList<'ast, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ZirExpressionList::EmbedCall(ref embed, ref generics, ref p) => {
                write!(f, "EmbedCall({:?}, {:?}, (", generics, embed)?;
                f.debug_list().entries(p.iter()).finish()?;
                write!(f, ")")
            }
        }
    }
}

// Common behaviour accross expressions

pub trait Conditional<'ast, T> {
    fn conditional(
        condition: BooleanExpression<'ast, T>,
        consequence: Self,
        alternative: Self,
    ) -> Self;
}

impl<'ast, T> Conditional<'ast, T> for FieldElementExpression<'ast, T> {
    fn conditional(
        condition: BooleanExpression<'ast, T>,
        consequence: Self,
        alternative: Self,
    ) -> Self {
        FieldElementExpression::Conditional(box condition, box consequence, box alternative)
    }
}

impl<'ast, T> Conditional<'ast, T> for BooleanExpression<'ast, T> {
    fn conditional(
        condition: BooleanExpression<'ast, T>,
        consequence: Self,
        alternative: Self,
    ) -> Self {
        BooleanExpression::Conditional(box condition, box consequence, box alternative)
    }
}

impl<'ast, T> Conditional<'ast, T> for UExpression<'ast, T> {
    fn conditional(
        condition: BooleanExpression<'ast, T>,
        consequence: Self,
        alternative: Self,
    ) -> Self {
        let bitwidth = consequence.bitwidth;

        UExpressionInner::Conditional(box condition, box consequence, box alternative)
            .annotate(bitwidth)
    }
}
