use from_pest::FromPest;
use pest::error::Error as PestError;
use pest::iterators::Pairs;
use std::fmt;
use zokrates_parser::parse;
use zokrates_parser::Rule;
#[macro_use]
extern crate lazy_static;

pub use ast::{
    Access, ArrayAccess, ArrayInitializerExpression, ArrayType, AssertionStatement, Assignee,
    AssigneeAccess, AssignmentStatement, BasicOrStructType, BasicType, BinaryExpression,
    BinaryOperator, CallAccess, ConstantExpression, DefinitionStatement, Expression, File,
    FromExpression, Function, IdentifierExpression, ImportDirective, ImportSource,
    InlineArrayExpression, InlineStructExpression, InlineStructMember, IterationStatement,
    MultiAssignmentStatement, Parameter, PostfixExpression, Range, RangeOrExpression,
    ReturnStatement, Span, Spread, SpreadOrExpression, Statement, StructDefinition, StructField,
    TernaryExpression, ToExpression, Type, UnaryExpression, UnaryOperator, Visibility,
};

mod ast {
    use from_pest::ConversionError;
    use from_pest::FromPest;
    use from_pest::Void;
    use pest::iterators::{Pair, Pairs};
    use pest::prec_climber::{Assoc, Operator, PrecClimber};
    pub use pest::Span;
    use pest_ast::FromPest;
    use zokrates_parser::Rule;

    lazy_static! {
        static ref PREC_CLIMBER: PrecClimber<Rule> = build_precedence_climber();
    }

    fn build_precedence_climber() -> PrecClimber<Rule> {
        PrecClimber::new(vec![
            Operator::new(Rule::op_inclusive_or, Assoc::Left),
            Operator::new(Rule::op_exclusive_or, Assoc::Left),
            Operator::new(Rule::op_and, Assoc::Left),
            Operator::new(Rule::op_equal, Assoc::Left)
                | Operator::new(Rule::op_not_equal, Assoc::Left),
            Operator::new(Rule::op_lte, Assoc::Left)
                | Operator::new(Rule::op_gte, Assoc::Left)
                | Operator::new(Rule::op_lt, Assoc::Left)
                | Operator::new(Rule::op_gt, Assoc::Left),
            Operator::new(Rule::op_add, Assoc::Left) | Operator::new(Rule::op_sub, Assoc::Left),
            Operator::new(Rule::op_mul, Assoc::Left) | Operator::new(Rule::op_div, Assoc::Left),
            Operator::new(Rule::op_pow, Assoc::Left),
        ])
    }

    // Create an Expression from left and right terms and an operator
    // Precondition: `pair` MUST be a binary operator
    fn infix_rule<'ast>(
        lhs: Box<Expression<'ast>>,
        pair: Pair<'ast, Rule>,
        rhs: Box<Expression<'ast>>,
    ) -> Box<Expression<'ast>> {
        // a + b spans from the start of a to the end of b
        let (start, _) = lhs.span().clone().split();
        let (_, end) = rhs.span().clone().split();
        let span = start.span(&end);

        Box::new(match pair.as_rule() {
            Rule::op_add => Expression::binary(BinaryOperator::Add, lhs, rhs, span),
            Rule::op_sub => Expression::binary(BinaryOperator::Sub, lhs, rhs, span),
            Rule::op_mul => Expression::binary(BinaryOperator::Mul, lhs, rhs, span),
            Rule::op_div => Expression::binary(BinaryOperator::Div, lhs, rhs, span),
            Rule::op_pow => Expression::binary(BinaryOperator::Pow, lhs, rhs, span),
            Rule::op_equal => Expression::binary(BinaryOperator::Eq, lhs, rhs, span),
            Rule::op_not_equal => Expression::binary(BinaryOperator::NotEq, lhs, rhs, span),
            Rule::op_lte => Expression::binary(BinaryOperator::Lte, lhs, rhs, span),
            Rule::op_lt => Expression::binary(BinaryOperator::Lt, lhs, rhs, span),
            Rule::op_gte => Expression::binary(BinaryOperator::Gte, lhs, rhs, span),
            Rule::op_gt => Expression::binary(BinaryOperator::Gt, lhs, rhs, span),
            Rule::op_inclusive_or => Expression::binary(BinaryOperator::Or, lhs, rhs, span),
            Rule::op_exclusive_or => Expression::binary(BinaryOperator::Xor, lhs, rhs, span),
            Rule::op_and => Expression::binary(BinaryOperator::And, lhs, rhs, span),
            _ => unreachable!(),
        })
    }

    // Create an Expression from an `expression`. `build_factor` turns each term into an `Expression` and `infix_rule` turns each (Expression, operator, Expression) into an Expression
    pub fn climb(pair: Pair<Rule>) -> Box<Expression> {
        PREC_CLIMBER.climb(pair.into_inner(), build_factor, infix_rule)
    }

    // Create an Expression from a `term`.
    // Precondition: `pair` MUST be a term
    fn build_factor(pair: Pair<Rule>) -> Box<Expression> {
        Box::new(match pair.as_rule() {
            Rule::term => {
                // clone the pair to peek into what we should create
                let clone = pair.clone();
                // define the child pair
                let next = clone.into_inner().next().unwrap();
                match next.as_rule() {
                    // this happens when we have an expression in parentheses: it needs to be processed as another sequence of terms and operators
                    Rule::expression => Expression::from_pest(&mut pair.into_inner()).unwrap(),
                    Rule::conditional_expression => Expression::Ternary(
                        TernaryExpression::from_pest(&mut pair.into_inner()).unwrap(),
                    ),
                    Rule::primary_expression => {
                        // maybe this could be simplified
                        let next = next.into_inner().next().unwrap();
                        match next.as_rule() {
                            Rule::constant => Expression::Constant(
                                ConstantExpression::from_pest(
                                    &mut pair.into_inner().next().unwrap().into_inner(),
                                )
                                .unwrap(),
                            ),
                            Rule::identifier => Expression::Identifier(
                                IdentifierExpression::from_pest(
                                    &mut pair.into_inner().next().unwrap().into_inner(),
                                )
                                .unwrap(),
                            ),
                            r => unreachable!("`primary_expression` should contain one of [`constant`, `identifier`], found {:#?}", r),
                        }
                    }
                    Rule::postfix_expression => Expression::Postfix(
                        PostfixExpression::from_pest(&mut pair.into_inner()).unwrap(),
                    ),
                    Rule::inline_struct_expression => Expression::InlineStruct(
                        InlineStructExpression::from_pest(&mut pair.into_inner()).unwrap(),
                    ),
                    Rule::inline_array_expression => Expression::InlineArray(
                        InlineArrayExpression::from_pest(&mut pair.into_inner()).unwrap(),
                    ),
                    Rule::array_initializer_expression => Expression::ArrayInitializer(
                        ArrayInitializerExpression::from_pest(&mut pair.into_inner()).unwrap()
                    ),
                    Rule::unary_expression => {
                        let span = next.as_span();
                        let mut inner = next.into_inner();
                        let op = match inner.next().unwrap().as_rule() {
                            Rule::op_unary => UnaryOperator::from_pest(&mut pair.into_inner().next().unwrap().into_inner()).unwrap(),
                            r => unreachable!("`unary_expression` should yield `op_unary`, found {:#?}", r)
                        };
                        let expression = build_factor(inner.next().unwrap());
                        Expression::Unary(UnaryExpression {
                            op,
                            expression,
                            span
                        })
                    },
                    r => unreachable!("`term` should contain one of [`expression`, `conditional_expression`, `primary_expression`, `postfix_expression`, `inline_array_expression`, `unary_expression`, `array_initializer_expression`], found {:#?}", r)
                }
            }
            r => unreachable!(
                "`build_factor` can only be called on `term`, found {:#?}",
                r
            ),
        })
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::file))]
    pub struct File<'ast> {
        pub imports: Vec<ImportDirective<'ast>>,
        pub structs: Vec<StructDefinition<'ast>>,
        pub functions: Vec<Function<'ast>>,
        pub eoi: EOI,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::ty_struct_definition))]
    pub struct StructDefinition<'ast> {
        pub id: IdentifierExpression<'ast>,
        pub fields: Vec<StructField<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::struct_field))]
    pub struct StructField<'ast> {
        pub ty: Type<'ast>,
        pub id: IdentifierExpression<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::function_definition))]
    pub struct Function<'ast> {
        pub id: IdentifierExpression<'ast>,
        pub parameters: Vec<Parameter<'ast>>,
        pub returns: Vec<Type<'ast>>,
        pub statements: Vec<Statement<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::import_directive))]
    pub enum ImportDirective<'ast> {
        Main(MainImportDirective<'ast>),
        From(FromImportDirective<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::main_import_directive))]
    pub struct MainImportDirective<'ast> {
        pub source: ImportSource<'ast>,
        pub alias: Option<IdentifierExpression<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::from_import_directive))]
    pub struct FromImportDirective<'ast> {
        pub source: ImportSource<'ast>,
        pub symbol: IdentifierExpression<'ast>,
        pub alias: Option<IdentifierExpression<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::import_source))]
    pub struct ImportSource<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub value: String,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::ty))]
    pub enum Type<'ast> {
        Basic(BasicType<'ast>),
        Array(ArrayType<'ast>),
        Struct(StructType<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::ty_basic))]
    pub enum BasicType<'ast> {
        Field(FieldType<'ast>),
        Boolean(BooleanType<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::ty_field))]
    pub struct FieldType<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::ty_array))]
    pub struct ArrayType<'ast> {
        pub ty: BasicOrStructType<'ast>,
        pub dimensions: Vec<Expression<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::ty_basic_or_struct))]
    pub enum BasicOrStructType<'ast> {
        Struct(StructType<'ast>),
        Basic(BasicType<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::ty_bool))]
    pub struct BooleanType<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::ty_struct))]
    pub struct StructType<'ast> {
        pub id: IdentifierExpression<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::parameter))]
    pub struct Parameter<'ast> {
        pub visibility: Option<Visibility>,
        pub ty: Type<'ast>,
        pub id: IdentifierExpression<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::vis))]
    pub enum Visibility {
        Public(PublicVisibility),
        Private(PrivateVisibility),
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::vis_public))]
    pub struct PublicVisibility {}

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::vis_private))]
    pub struct PrivateVisibility {}

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::statement))]
    pub enum Statement<'ast> {
        Return(ReturnStatement<'ast>),
        Definition(DefinitionStatement<'ast>),
        Assertion(AssertionStatement<'ast>),
        Iteration(IterationStatement<'ast>),
        Assignment(AssignmentStatement<'ast>),
        MultiAssignment(MultiAssignmentStatement<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::definition_statement))]
    pub struct DefinitionStatement<'ast> {
        pub ty: Type<'ast>,
        pub id: IdentifierExpression<'ast>,
        pub expression: Expression<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::assignment_statement))]
    pub struct AssignmentStatement<'ast> {
        pub assignee: Assignee<'ast>,
        pub expression: Expression<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::expression_statement))]
    pub struct AssertionStatement<'ast> {
        pub expression: Expression<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::iteration_statement))]
    pub struct IterationStatement<'ast> {
        pub ty: Type<'ast>,
        pub index: IdentifierExpression<'ast>,
        pub from: Expression<'ast>,
        pub to: Expression<'ast>,
        pub statements: Vec<Statement<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::multi_assignment_statement))]
    pub struct MultiAssignmentStatement<'ast> {
        pub lhs: Vec<OptionallyTypedIdentifier<'ast>>,
        pub function_id: IdentifierExpression<'ast>,
        pub arguments: Vec<Expression<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::return_statement))]
    pub struct ReturnStatement<'ast> {
        pub expressions: Vec<Expression<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, PartialEq, Clone)]
    pub enum BinaryOperator {
        Xor,
        Or,
        And,
        Add,
        Sub,
        Mul,
        Div,
        Eq,
        NotEq,
        Lt,
        Gt,
        Lte,
        Gte,
        Pow,
    }

    #[derive(Debug, PartialEq, FromPest, Clone)]
    #[pest_ast(rule(Rule::op_unary))]
    pub enum UnaryOperator<'ast> {
        Not(Not<'ast>),
    }

    #[derive(Debug, PartialEq, FromPest, Clone)]
    #[pest_ast(rule(Rule::op_not))]
    pub struct Not<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, PartialEq, Clone)]
    pub enum Expression<'ast> {
        Ternary(TernaryExpression<'ast>),
        Binary(BinaryExpression<'ast>),
        Postfix(PostfixExpression<'ast>),
        Identifier(IdentifierExpression<'ast>),
        Constant(ConstantExpression<'ast>),
        InlineArray(InlineArrayExpression<'ast>),
        InlineStruct(InlineStructExpression<'ast>),
        ArrayInitializer(ArrayInitializerExpression<'ast>),
        Unary(UnaryExpression<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::spread_or_expression))]
    pub enum SpreadOrExpression<'ast> {
        Spread(Spread<'ast>),
        Expression(Expression<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::spread))]
    pub struct Spread<'ast> {
        pub expression: Expression<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::range_or_expression))]
    pub enum RangeOrExpression<'ast> {
        Range(Range<'ast>),
        Expression(Expression<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::range))]
    pub struct Range<'ast> {
        pub from: Option<FromExpression<'ast>>,
        pub to: Option<ToExpression<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::from_expression))]
    pub struct FromExpression<'ast>(pub Expression<'ast>);

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::to_expression))]
    pub struct ToExpression<'ast>(pub Expression<'ast>);

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::postfix_expression))]
    pub struct PostfixExpression<'ast> {
        pub id: IdentifierExpression<'ast>,
        pub accesses: Vec<Access<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::unary_expression))]
    pub struct UnaryExpression<'ast> {
        pub op: UnaryOperator<'ast>,
        pub expression: Box<Expression<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::inline_array_expression))]
    pub struct InlineArrayExpression<'ast> {
        pub expressions: Vec<SpreadOrExpression<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::inline_struct_expression))]
    pub struct InlineStructExpression<'ast> {
        pub ty: IdentifierExpression<'ast>,
        pub members: Vec<InlineStructMember<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::inline_struct_member))]
    pub struct InlineStructMember<'ast> {
        pub id: IdentifierExpression<'ast>,
        pub expression: Expression<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::array_initializer_expression))]
    pub struct ArrayInitializerExpression<'ast> {
        pub value: Box<Expression<'ast>>,
        pub count: ConstantExpression<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::optionally_typed_identifier))]
    pub struct OptionallyTypedIdentifier<'ast> {
        pub ty: Option<Type<'ast>>,
        pub id: IdentifierExpression<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::access))]
    pub enum Access<'ast> {
        Call(CallAccess<'ast>),
        Select(ArrayAccess<'ast>),
        Member(MemberAccess<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::assignee_access))]
    pub enum AssigneeAccess<'ast> {
        Select(ArrayAccess<'ast>),
        Member(MemberAccess<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::call_access))]
    pub struct CallAccess<'ast> {
        pub expressions: Vec<Expression<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::array_access))]
    pub struct ArrayAccess<'ast> {
        pub expression: RangeOrExpression<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::member_access))]
    pub struct MemberAccess<'ast> {
        pub id: IdentifierExpression<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, PartialEq, Clone)]
    pub struct BinaryExpression<'ast> {
        pub op: BinaryOperator,
        pub left: Box<Expression<'ast>>,
        pub right: Box<Expression<'ast>>,
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::conditional_expression))]
    pub struct TernaryExpression<'ast> {
        pub first: Box<Expression<'ast>>,
        pub second: Box<Expression<'ast>>,
        pub third: Box<Expression<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    impl<'ast> Expression<'ast> {
        pub fn ternary(
            first: Box<Expression<'ast>>,
            second: Box<Expression<'ast>>,
            third: Box<Expression<'ast>>,
            span: Span<'ast>,
        ) -> Self {
            Expression::Ternary(TernaryExpression {
                first,
                second,
                third,
                span,
            })
        }

        pub fn binary(
            op: BinaryOperator,
            left: Box<Expression<'ast>>,
            right: Box<Expression<'ast>>,
            span: Span<'ast>,
        ) -> Self {
            Expression::Binary(BinaryExpression {
                op,
                left,
                right,
                span,
            })
        }

        pub fn span(&self) -> &Span<'ast> {
            match self {
                Expression::Binary(b) => &b.span,
                Expression::Identifier(i) => &i.span,
                Expression::Constant(c) => &c.span(),
                Expression::Ternary(t) => &t.span,
                Expression::Postfix(p) => &p.span,
                Expression::InlineArray(a) => &a.span,
                Expression::InlineStruct(s) => &s.span,
                Expression::ArrayInitializer(a) => &a.span,
                Expression::Unary(u) => &u.span,
            }
        }
    }

    impl<'ast> FromPest<'ast> for Expression<'ast> {
        type Rule = Rule;
        type FatalError = Void;

        // We implement AST creation manually here for Expression
        // `pest` should yield an `expression` which we can generate AST with, based on precedence rules
        fn from_pest(pest: &mut Pairs<'ast, Rule>) -> Result<Self, ConversionError<Void>> {
            // get a clone to "try" to match
            let mut clone = pest.clone();
            // advance by one pair in the clone, if none error out, `pest` is still the original
            let pair = clone.next().ok_or(::from_pest::ConversionError::NoMatch)?;
            // this should be an expression
            match pair.as_rule() {
                Rule::expression => {
                    // we can replace `pest` with the clone we tried with and got pairs from to create the AST
                    *pest = clone;
                    Ok(*climb(pair))
                }
                _ => Err(ConversionError::NoMatch),
            }
        }
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::constant))]
    pub enum ConstantExpression<'ast> {
        DecimalNumber(DecimalNumberExpression<'ast>),
        BooleanLiteral(BooleanLiteralExpression<'ast>),
    }

    impl<'ast> ConstantExpression<'ast> {
        pub fn span(&self) -> &Span<'ast> {
            match self {
                ConstantExpression::DecimalNumber(n) => &n.span,
                ConstantExpression::BooleanLiteral(c) => &c.span,
            }
        }
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::decimal_number))]
    pub struct DecimalNumberExpression<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub value: String,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::boolean_literal))]
    pub struct BooleanLiteralExpression<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub value: String,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::identifier))]
    pub struct IdentifierExpression<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub value: String,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::assignee))]
    pub struct Assignee<'ast> {
        pub id: IdentifierExpression<'ast>,      // a
        pub accesses: Vec<AssigneeAccess<'ast>>, // [42 + x].foo[7]
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    fn span_into_str(span: Span) -> String {
        span.as_str().to_string()
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::EOI))]
    pub struct EOI;
}

struct Prog<'ast>(ast::File<'ast>);

impl<'ast> From<Pairs<'ast, Rule>> for Prog<'ast> {
    fn from(mut pairs: Pairs<'ast, Rule>) -> Prog<'ast> {
        Prog(ast::File::from_pest(&mut pairs).unwrap())
    }
}

#[derive(PartialEq, Clone, Debug)]
pub struct Error(PestError<Rule>);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub fn generate_ast(input: &str) -> Result<ast::File, Error> {
    let parse_tree = parse(input).map_err(|e| Error(e))?;
    Ok(Prog::from(parse_tree).0)
}

#[cfg(test)]
mod tests {
    use super::ast::*;
    use super::*;
    use pest::Span;

    #[test]
    fn examples() {
        use glob::glob;
        use std::fs;
        use std::io::Read;
        // Traverse all .zok files in examples dir
        for entry in glob("../zokrates_cli/examples/**/*.zok").expect("Failed to read glob pattern")
        {
            match entry {
                Ok(path) => {
                    if path.to_str().unwrap().contains("error") {
                        continue;
                    }
                    println!("Parsing {:?}", path.display());
                    let mut file = fs::File::open(path).unwrap();
                    let mut data = String::new();
                    file.read_to_string(&mut data).unwrap();
                    let _res = generate_ast(&data).unwrap();
                }
                Err(e) => println!("{:?}", e),
            }
        }
    }

    impl<'ast> Expression<'ast> {
        pub fn add(left: Expression<'ast>, right: Expression<'ast>, span: Span<'ast>) -> Self {
            Self::binary(BinaryOperator::Add, Box::new(left), Box::new(right), span)
        }

        pub fn mul(left: Expression<'ast>, right: Expression<'ast>, span: Span<'ast>) -> Self {
            Self::binary(BinaryOperator::Mul, Box::new(left), Box::new(right), span)
        }

        pub fn pow(left: Expression<'ast>, right: Expression<'ast>, span: Span<'ast>) -> Self {
            Self::binary(BinaryOperator::Pow, Box::new(left), Box::new(right), span)
        }

        pub fn if_else(
            condition: Expression<'ast>,
            consequence: Expression<'ast>,
            alternative: Expression<'ast>,
            span: Span<'ast>,
        ) -> Self {
            Self::ternary(
                Box::new(condition),
                Box::new(consequence),
                Box::new(alternative),
                span,
            )
        }
    }

    #[test]
    fn one_plus_one() {
        let source = r#"import "foo"
                def main() -> (field): return 1 + 1
"#;
        assert_eq!(
            generate_ast(&source),
            Ok(File {
                structs: vec![],
                functions: vec![Function {
                    id: IdentifierExpression {
                        value: String::from("main"),
                        span: Span::new(&source, 33, 37).unwrap()
                    },
                    parameters: vec![],
                    returns: vec![Type::Basic(BasicType::Field(FieldType {
                        span: Span::new(&source, 44, 49).unwrap()
                    }))],
                    statements: vec![Statement::Return(ReturnStatement {
                        expressions: vec![Expression::add(
                            Expression::Constant(ConstantExpression::DecimalNumber(
                                DecimalNumberExpression {
                                    value: String::from("1"),
                                    span: Span::new(&source, 59, 60).unwrap()
                                }
                            )),
                            Expression::Constant(ConstantExpression::DecimalNumber(
                                DecimalNumberExpression {
                                    value: String::from("1"),
                                    span: Span::new(&source, 63, 64).unwrap()
                                }
                            )),
                            Span::new(&source, 59, 64).unwrap()
                        )],
                        span: Span::new(&source, 52, 64).unwrap(),
                    })],
                    span: Span::new(&source, 29, source.len()).unwrap(),
                }],
                imports: vec![ImportDirective::Main(MainImportDirective {
                    source: ImportSource {
                        value: String::from("foo"),
                        span: Span::new(&source, 8, 11).unwrap()
                    },
                    alias: None,
                    span: Span::new(&source, 0, 29).unwrap()
                })],
                eoi: EOI {},
                span: Span::new(&source, 0, 65).unwrap()
            })
        );
    }

    #[test]
    fn precedence() {
        let source = r#"import "foo"
                def main() -> (field): return 1 + 2 * 3 ** 4
"#;
        assert_eq!(
            generate_ast(&source),
            Ok(File {
                structs: vec![],
                functions: vec![Function {
                    id: IdentifierExpression {
                        value: String::from("main"),
                        span: Span::new(&source, 33, 37).unwrap()
                    },
                    parameters: vec![],
                    returns: vec![Type::Basic(BasicType::Field(FieldType {
                        span: Span::new(&source, 44, 49).unwrap()
                    }))],
                    statements: vec![Statement::Return(ReturnStatement {
                        expressions: vec![Expression::add(
                            Expression::Constant(ConstantExpression::DecimalNumber(
                                DecimalNumberExpression {
                                    value: String::from("1"),
                                    span: Span::new(&source, 59, 60).unwrap()
                                }
                            )),
                            Expression::mul(
                                Expression::Constant(ConstantExpression::DecimalNumber(
                                    DecimalNumberExpression {
                                        value: String::from("2"),
                                        span: Span::new(&source, 63, 64).unwrap()
                                    }
                                )),
                                Expression::pow(
                                    Expression::Constant(ConstantExpression::DecimalNumber(
                                        DecimalNumberExpression {
                                            value: String::from("3"),
                                            span: Span::new(&source, 67, 68).unwrap()
                                        }
                                    )),
                                    Expression::Constant(ConstantExpression::DecimalNumber(
                                        DecimalNumberExpression {
                                            value: String::from("4"),
                                            span: Span::new(&source, 72, 73).unwrap()
                                        }
                                    )),
                                    Span::new(&source, 67, 73).unwrap()
                                ),
                                Span::new(&source, 63, 73).unwrap()
                            ),
                            Span::new(&source, 59, 73).unwrap()
                        )],
                        span: Span::new(&source, 52, 73).unwrap(),
                    })],
                    span: Span::new(&source, 29, 74).unwrap(),
                }],
                imports: vec![ImportDirective::Main(MainImportDirective {
                    source: ImportSource {
                        value: String::from("foo"),
                        span: Span::new(&source, 8, 11).unwrap()
                    },
                    alias: None,
                    span: Span::new(&source, 0, 29).unwrap()
                })],
                eoi: EOI {},
                span: Span::new(&source, 0, 74).unwrap()
            })
        );
    }

    #[test]
    fn ternary() {
        let source = r#"import "foo"
                def main() -> (field): return if 1 then 2 else 3 fi
"#;
        assert_eq!(
            generate_ast(&source),
            Ok(File {
                structs: vec![],
                functions: vec![Function {
                    id: IdentifierExpression {
                        value: String::from("main"),
                        span: Span::new(&source, 33, 37).unwrap()
                    },
                    parameters: vec![],
                    returns: vec![Type::Basic(BasicType::Field(FieldType {
                        span: Span::new(&source, 44, 49).unwrap()
                    }))],
                    statements: vec![Statement::Return(ReturnStatement {
                        expressions: vec![Expression::if_else(
                            Expression::Constant(ConstantExpression::DecimalNumber(
                                DecimalNumberExpression {
                                    value: String::from("1"),
                                    span: Span::new(&source, 62, 63).unwrap()
                                }
                            )),
                            Expression::Constant(ConstantExpression::DecimalNumber(
                                DecimalNumberExpression {
                                    value: String::from("2"),
                                    span: Span::new(&source, 69, 70).unwrap()
                                }
                            )),
                            Expression::Constant(ConstantExpression::DecimalNumber(
                                DecimalNumberExpression {
                                    value: String::from("3"),
                                    span: Span::new(&source, 76, 77).unwrap()
                                }
                            )),
                            Span::new(&source, 59, 80).unwrap()
                        )],
                        span: Span::new(&source, 52, 80).unwrap(),
                    })],
                    span: Span::new(&source, 29, 81).unwrap(),
                }],
                imports: vec![ImportDirective::Main(MainImportDirective {
                    source: ImportSource {
                        value: String::from("foo"),
                        span: Span::new(&source, 8, 11).unwrap()
                    },
                    alias: None,
                    span: Span::new(&source, 0, 29).unwrap()
                })],
                eoi: EOI {},
                span: Span::new(&source, 0, 81).unwrap()
            })
        );
    }

    #[test]
    fn parentheses() {
        let source = r#"def main() -> (field): return (1)
"#;
        assert_eq!(
            generate_ast(&source),
            Ok(File {
                structs: vec![],
                functions: vec![Function {
                    id: IdentifierExpression {
                        value: String::from("main"),
                        span: Span::new(&source, 4, 8).unwrap()
                    },
                    parameters: vec![],
                    returns: vec![Type::Basic(BasicType::Field(FieldType {
                        span: Span::new(&source, 15, 20).unwrap()
                    }))],
                    statements: vec![Statement::Return(ReturnStatement {
                        expressions: vec![Expression::Constant(ConstantExpression::DecimalNumber(
                            DecimalNumberExpression {
                                value: String::from("1"),
                                span: Span::new(&source, 31, 32).unwrap()
                            }
                        ))],
                        span: Span::new(&source, 23, 33).unwrap(),
                    })],
                    span: Span::new(&source, 0, 34).unwrap(),
                }],
                imports: vec![],
                eoi: EOI {},
                span: Span::new(&source, 0, 34).unwrap()
            })
        );
    }

    #[test]
    fn multidef() {
        let source = r#"def main() -> (field): field a, b = foo(1, 2 + 3)
"#;
        assert_eq!(
            generate_ast(&source),
            Ok(File {
                structs: vec![],
                functions: vec![Function {
                    id: IdentifierExpression {
                        value: String::from("main"),
                        span: Span::new(&source, 4, 8).unwrap()
                    },
                    parameters: vec![],
                    returns: vec![Type::Basic(BasicType::Field(FieldType {
                        span: Span::new(&source, 15, 20).unwrap()
                    }))],
                    statements: vec![Statement::MultiAssignment(MultiAssignmentStatement {
                        function_id: IdentifierExpression {
                            value: String::from("foo"),
                            span: Span::new(&source, 36, 39).unwrap()
                        },
                        lhs: vec![
                            OptionallyTypedIdentifier {
                                ty: Some(Type::Basic(BasicType::Field(FieldType {
                                    span: Span::new(&source, 23, 28).unwrap()
                                }))),
                                id: IdentifierExpression {
                                    value: String::from("a"),
                                    span: Span::new(&source, 29, 30).unwrap(),
                                },
                                span: Span::new(&source, 23, 30).unwrap()
                            },
                            OptionallyTypedIdentifier {
                                ty: None,
                                id: IdentifierExpression {
                                    value: String::from("b"),
                                    span: Span::new(&source, 32, 33).unwrap(),
                                },
                                span: Span::new(&source, 32, 33).unwrap()
                            },
                        ],
                        arguments: vec![
                            Expression::Constant(ConstantExpression::DecimalNumber(
                                DecimalNumberExpression {
                                    value: String::from("1"),
                                    span: Span::new(&source, 40, 41).unwrap()
                                }
                            )),
                            Expression::add(
                                Expression::Constant(ConstantExpression::DecimalNumber(
                                    DecimalNumberExpression {
                                        value: String::from("2"),
                                        span: Span::new(&source, 43, 44).unwrap()
                                    }
                                )),
                                Expression::Constant(ConstantExpression::DecimalNumber(
                                    DecimalNumberExpression {
                                        value: String::from("3"),
                                        span: Span::new(&source, 47, 48).unwrap()
                                    }
                                )),
                                Span::new(&source, 43, 48).unwrap()
                            ),
                        ],
                        span: Span::new(&source, 23, 49).unwrap()
                    })],
                    span: Span::new(&source, 0, 50).unwrap(),
                }],
                imports: vec![],
                eoi: EOI {},
                span: Span::new(&source, 0, 50).unwrap()
            })
        );
    }

    #[test]
    fn playground() {
        let source = r#"import "heyman" as yo

        struct Foo {
            field[2] foo
            Bar bar
        }

        def main(private field[23] a) -> (bool[234 + 6]):
        field a = 1
        a[32 + x][55] = y
        for field i in 0..3 do
               a == 1 + 2 + 3+ 4+ 5+ 6+ 6+ 7+ 8 + 4+ 5+ 3+ 4+ 2+ 3
        endfor
        a.member == 1
        return a
"#;
        let res = generate_ast(&source);
        println!("{:#?}", generate_ast(&source));
        assert!(res.is_ok());
    }
}
