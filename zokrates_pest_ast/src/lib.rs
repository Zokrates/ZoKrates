use from_pest::FromPest;
use pest::error::Error as PestError;
use pest::iterators::Pairs;
use std::fmt;
use zokrates_parser::parse;
use zokrates_parser::Rule;
#[macro_use]
extern crate lazy_static;

pub use ast::{
    Access, Arguments, ArrayAccess, ArrayInitializerExpression, ArrayType, AssertionStatement,
    Assignee, AssigneeAccess, BasicOrStructType, BasicType, BinaryExpression, BinaryOperator,
    CallAccess, ConstantGenericValue, DecimalLiteralExpression, DecimalNumber, DecimalSuffix,
    DefinitionStatement, ExplicitGenerics, Expression, FieldType, File, FromExpression, Function,
    HexLiteralExpression, HexNumberExpression, IdentifierExpression, ImportDirective, ImportSource,
    InlineArrayExpression, InlineStructExpression, InlineStructMember, IterationStatement,
    LiteralExpression, OptionallyTypedAssignee, Parameter, PostfixExpression, Range,
    RangeOrExpression, ReturnStatement, Span, Spread, SpreadOrExpression, Statement,
    StructDefinition, StructField, TernaryExpression, ToExpression, Type, UnaryExpression,
    UnaryOperator, Underscore, Visibility,
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

    // based on https://docs.python.org/3/reference/expressions.html#operator-precedence
    fn build_precedence_climber() -> PrecClimber<Rule> {
        PrecClimber::new(vec![
            Operator::new(Rule::op_or, Assoc::Left),
            Operator::new(Rule::op_and, Assoc::Left),
            Operator::new(Rule::op_lt, Assoc::Left)
                | Operator::new(Rule::op_lte, Assoc::Left)
                | Operator::new(Rule::op_gt, Assoc::Left)
                | Operator::new(Rule::op_gte, Assoc::Left)
                | Operator::new(Rule::op_not_equal, Assoc::Left)
                | Operator::new(Rule::op_equal, Assoc::Left),
            Operator::new(Rule::op_bit_or, Assoc::Left),
            Operator::new(Rule::op_bit_xor, Assoc::Left),
            Operator::new(Rule::op_bit_and, Assoc::Left),
            Operator::new(Rule::op_left_shift, Assoc::Left)
                | Operator::new(Rule::op_right_shift, Assoc::Left),
            Operator::new(Rule::op_add, Assoc::Left) | Operator::new(Rule::op_sub, Assoc::Left),
            Operator::new(Rule::op_mul, Assoc::Left)
                | Operator::new(Rule::op_div, Assoc::Left)
                | Operator::new(Rule::op_rem, Assoc::Left),
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
            Rule::op_rem => Expression::binary(BinaryOperator::Rem, lhs, rhs, span),
            Rule::op_equal => Expression::binary(BinaryOperator::Eq, lhs, rhs, span),
            Rule::op_not_equal => Expression::binary(BinaryOperator::NotEq, lhs, rhs, span),
            Rule::op_lte => Expression::binary(BinaryOperator::Lte, lhs, rhs, span),
            Rule::op_lt => Expression::binary(BinaryOperator::Lt, lhs, rhs, span),
            Rule::op_gte => Expression::binary(BinaryOperator::Gte, lhs, rhs, span),
            Rule::op_gt => Expression::binary(BinaryOperator::Gt, lhs, rhs, span),
            Rule::op_or => Expression::binary(BinaryOperator::Or, lhs, rhs, span),
            Rule::op_and => Expression::binary(BinaryOperator::And, lhs, rhs, span),
            Rule::op_bit_xor => Expression::binary(BinaryOperator::BitXor, lhs, rhs, span),
            Rule::op_bit_and => Expression::binary(BinaryOperator::BitAnd, lhs, rhs, span),
            Rule::op_bit_or => Expression::binary(BinaryOperator::BitOr, lhs, rhs, span),
            Rule::op_right_shift => Expression::binary(BinaryOperator::RightShift, lhs, rhs, span),
            Rule::op_left_shift => Expression::binary(BinaryOperator::LeftShift, lhs, rhs, span),
            _ => unreachable!(),
        })
    }

    // Create an Expression from an `expression`. `build_factor` turns each term into an `Expression` and `infix_rule` turns each (Expression, operator, Expression) into an Expression
    pub fn climb(pair: Pair<Rule>) -> Box<Expression> {
        PREC_CLIMBER.climb(pair.into_inner(), build_factor, infix_rule)
    }

    // Create an Expression from a `unaried_term`.
    // Precondition: `pair` MUST be a `unaried_term`
    fn build_factor(pair: Pair<Rule>) -> Box<Expression> {
        Box::new(Expression::from(
            UnariedTerm::from_pest(&mut Pairs::single(pair)).unwrap(),
        ))
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::file))]
    pub struct File<'ast> {
        pub pragma: Option<Pragma<'ast>>,
        pub imports: Vec<ImportDirective<'ast>>,
        pub structs: Vec<StructDefinition<'ast>>,
        pub functions: Vec<Function<'ast>>,
        pub eoi: EOI,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::pragma))]
    pub struct Pragma<'ast> {
        pub curve: Curve<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::curve))]
    pub struct Curve<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub name: String,
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
        pub generics: Vec<IdentifierExpression<'ast>>,
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
        U8(U8Type<'ast>),
        U16(U16Type<'ast>),
        U32(U32Type<'ast>),
        U64(U64Type<'ast>),
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
    #[pest_ast(rule(Rule::ty_u8))]
    pub struct U8Type<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::ty_u16))]
    pub struct U16Type<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::ty_u32))]
    pub struct U32Type<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::ty_u64))]
    pub struct U64Type<'ast> {
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

    #[allow(clippy::large_enum_variant)]
    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::statement))]
    pub enum Statement<'ast> {
        Return(ReturnStatement<'ast>),
        Definition(DefinitionStatement<'ast>),
        Assertion(AssertionStatement<'ast>),
        Iteration(IterationStatement<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::definition_statement))]
    pub struct DefinitionStatement<'ast> {
        pub lhs: Vec<OptionallyTypedAssignee<'ast>>,
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
    #[pest_ast(rule(Rule::return_statement))]
    pub struct ReturnStatement<'ast> {
        pub expressions: Vec<Expression<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, PartialEq, Clone)]
    pub enum BinaryOperator {
        BitXor,
        BitAnd,
        BitOr,
        RightShift,
        LeftShift,
        Or,
        And,
        Add,
        Sub,
        Mul,
        Div,
        Rem,
        Eq,
        NotEq,
        Lt,
        Gt,
        Lte,
        Gte,
        Pow,
    }

    #[derive(Debug, PartialEq, Clone)]
    pub enum Expression<'ast> {
        Ternary(TernaryExpression<'ast>),
        Binary(BinaryExpression<'ast>),
        Unary(UnaryExpression<'ast>),
        Postfix(PostfixExpression<'ast>),
        Identifier(IdentifierExpression<'ast>),
        Literal(LiteralExpression<'ast>),
        InlineArray(InlineArrayExpression<'ast>),
        InlineStruct(InlineStructExpression<'ast>),
        ArrayInitializer(ArrayInitializerExpression<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::term))]
    pub enum Term<'ast> {
        Expression(Expression<'ast>),
        InlineStruct(InlineStructExpression<'ast>),
        Ternary(TernaryExpression<'ast>),
        Postfix(PostfixExpression<'ast>),
        Primary(PrimaryExpression<'ast>),
        InlineArray(InlineArrayExpression<'ast>),
        ArrayInitializer(ArrayInitializerExpression<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::powered_term))]
    struct PoweredTerm<'ast> {
        base: Term<'ast>,
        op: Option<PowOperator>,
        exponent: Option<ExponentExpression<'ast>>,
        #[pest_ast(outer())]
        span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::op_pow))]
    struct PowOperator;

    impl<'ast> From<PoweredTerm<'ast>> for Expression<'ast> {
        fn from(t: PoweredTerm<'ast>) -> Self {
            let base = Expression::from(t.base);

            match t.exponent {
                Some(exponent) => Expression::Binary(BinaryExpression {
                    op: BinaryOperator::Pow,
                    left: Box::new(base),
                    right: Box::new(exponent.into()),
                    span: t.span,
                }),
                None => base,
            }
        }
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::unaried_term))]
    struct UnariedTerm<'ast> {
        op: Option<UnaryOperator>,
        expression: PoweredTerm<'ast>,
        #[pest_ast(outer())]
        span: Span<'ast>,
    }

    impl<'ast> From<UnariedTerm<'ast>> for Expression<'ast> {
        fn from(t: UnariedTerm<'ast>) -> Self {
            let expression = Expression::from(t.expression);

            match t.op {
                Some(sign) => Expression::Unary(UnaryExpression {
                    op: sign,
                    expression: Box::new(expression),
                    span: t.span,
                }),
                None => expression,
            }
        }
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::op_unary))]
    pub enum UnaryOperator {
        Pos(PosOperator),
        Neg(NegOperator),
        Not(NotOperator),
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::op_pos))]
    pub struct PosOperator;

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::op_neg))]
    pub struct NegOperator;

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::op_not))]
    pub struct NotOperator;

    impl<'ast> From<Term<'ast>> for Expression<'ast> {
        fn from(t: Term<'ast>) -> Self {
            match t {
                Term::Expression(e) => e,
                Term::Ternary(e) => Expression::Ternary(e),
                Term::Postfix(e) => Expression::Postfix(e),
                Term::Primary(e) => e.into(),
                Term::InlineArray(e) => Expression::InlineArray(e),
                Term::InlineStruct(e) => Expression::InlineStruct(e),
                Term::ArrayInitializer(e) => Expression::ArrayInitializer(e),
            }
        }
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::primary_expression))]
    pub enum PrimaryExpression<'ast> {
        Identifier(IdentifierExpression<'ast>),
        Literal(LiteralExpression<'ast>),
    }

    impl<'ast> From<PrimaryExpression<'ast>> for Expression<'ast> {
        fn from(e: PrimaryExpression<'ast>) -> Self {
            match e {
                PrimaryExpression::Literal(c) => Expression::Literal(c),
                PrimaryExpression::Identifier(i) => Expression::Identifier(i),
            }
        }
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::exponent_expression))]
    pub enum ExponentExpression<'ast> {
        Expression(Expression<'ast>),
        Primary(PrimaryExpression<'ast>),
    }

    impl<'ast> From<ExponentExpression<'ast>> for Expression<'ast> {
        fn from(e: ExponentExpression<'ast>) -> Self {
            match e {
                ExponentExpression::Expression(e) => e,
                ExponentExpression::Primary(e) => e.into(),
            }
        }
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
        pub count: Box<Expression<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::optionally_typed_assignee))]
    pub struct OptionallyTypedAssignee<'ast> {
        pub ty: Option<Type<'ast>>,
        pub a: Assignee<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[allow(clippy::large_enum_variant)]
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
        pub explicit_generics: Option<ExplicitGenerics<'ast>>,
        pub arguments: Arguments<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::explicit_generics))]
    pub struct ExplicitGenerics<'ast> {
        pub values: Vec<ConstantGenericValue<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::constant_generics_value))]
    pub enum ConstantGenericValue<'ast> {
        Value(LiteralExpression<'ast>),
        Identifier(IdentifierExpression<'ast>),
        Underscore(Underscore<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::underscore))]
    pub struct Underscore<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::arguments))]
    pub struct Arguments<'ast> {
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

    #[derive(Debug, PartialEq, Clone)]
    pub struct UnaryExpression<'ast> {
        pub op: UnaryOperator,
        pub expression: Box<Expression<'ast>>,
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
                Expression::Literal(c) => &c.span(),
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
    #[pest_ast(rule(Rule::literal))]
    pub enum LiteralExpression<'ast> {
        DecimalLiteral(DecimalLiteralExpression<'ast>),
        BooleanLiteral(BooleanLiteralExpression<'ast>),
        HexLiteral(HexLiteralExpression<'ast>),
    }

    impl<'ast> LiteralExpression<'ast> {
        pub fn span(&self) -> &Span<'ast> {
            match self {
                LiteralExpression::DecimalLiteral(n) => &n.span,
                LiteralExpression::BooleanLiteral(c) => &c.span,
                LiteralExpression::HexLiteral(h) => &h.span,
            }
        }
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::decimal_suffix))]
    pub enum DecimalSuffix<'ast> {
        U8(U8Suffix<'ast>),
        U16(U16Suffix<'ast>),
        U32(U32Suffix<'ast>),
        U64(U64Suffix<'ast>),
        Field(FieldSuffix<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::decimal_suffix_u8))]
    pub struct U8Suffix<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::decimal_suffix_u16))]
    pub struct U16Suffix<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::decimal_suffix_u32))]
    pub struct U32Suffix<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::decimal_suffix_u64))]
    pub struct U64Suffix<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::decimal_suffix_field))]
    pub struct FieldSuffix<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::decimal_number))]
    pub struct DecimalNumber<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::decimal_literal))]
    pub struct DecimalLiteralExpression<'ast> {
        pub value: DecimalNumber<'ast>,
        pub suffix: Option<DecimalSuffix<'ast>>,
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
    #[pest_ast(rule(Rule::hex_literal))]
    pub struct HexLiteralExpression<'ast> {
        pub value: HexNumberExpression<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::hex_number))]
    pub enum HexNumberExpression<'ast> {
        U8(U8NumberExpression<'ast>),
        U16(U16NumberExpression<'ast>),
        U32(U32NumberExpression<'ast>),
        U64(U64NumberExpression<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::hex_number_u8))]
    pub struct U8NumberExpression<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub value: String,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::hex_number_u16))]
    pub struct U16NumberExpression<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub value: String,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::hex_number_u32))]
    pub struct U32NumberExpression<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub value: String,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::hex_number_u64))]
    pub struct U64NumberExpression<'ast> {
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
    #[allow(clippy::upper_case_acronyms)]
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
    let parse_tree = parse(input).map_err(Error)?;
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
                pragma: None,
                structs: vec![],
                functions: vec![Function {
                    generics: vec![],
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
                            Expression::Literal(LiteralExpression::DecimalLiteral(
                                DecimalLiteralExpression {
                                    value: DecimalNumber {
                                        span: Span::new(&source, 59, 60).unwrap()
                                    },
                                    suffix: None,
                                    span: Span::new(&source, 59, 60).unwrap()
                                }
                            )),
                            Expression::Literal(LiteralExpression::DecimalLiteral(
                                DecimalLiteralExpression {
                                    value: DecimalNumber {
                                        span: Span::new(&source, 63, 64).unwrap()
                                    },
                                    suffix: None,
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
                pragma: None,
                structs: vec![],
                functions: vec![Function {
                    generics: vec![],
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
                            Expression::Literal(LiteralExpression::DecimalLiteral(
                                DecimalLiteralExpression {
                                    suffix: None,
                                    value: DecimalNumber {
                                        span: Span::new(&source, 59, 60).unwrap()
                                    },
                                    span: Span::new(&source, 59, 60).unwrap()
                                }
                            )),
                            Expression::mul(
                                Expression::Literal(LiteralExpression::DecimalLiteral(
                                    DecimalLiteralExpression {
                                        suffix: None,
                                        value: DecimalNumber {
                                            span: Span::new(&source, 63, 64).unwrap()
                                        },
                                        span: Span::new(&source, 63, 64).unwrap()
                                    }
                                )),
                                Expression::pow(
                                    Expression::Literal(LiteralExpression::DecimalLiteral(
                                        DecimalLiteralExpression {
                                            suffix: None,
                                            value: DecimalNumber {
                                                span: Span::new(&source, 67, 68).unwrap()
                                            },
                                            span: Span::new(&source, 67, 68).unwrap()
                                        }
                                    )),
                                    Expression::Literal(LiteralExpression::DecimalLiteral(
                                        DecimalLiteralExpression {
                                            suffix: None,
                                            value: DecimalNumber {
                                                span: Span::new(&source, 72, 73).unwrap()
                                            },
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
                pragma: None,
                structs: vec![],
                functions: vec![Function {
                    generics: vec![],
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
                            Expression::Literal(LiteralExpression::DecimalLiteral(
                                DecimalLiteralExpression {
                                    suffix: None,
                                    value: DecimalNumber {
                                        span: Span::new(&source, 62, 63).unwrap()
                                    },
                                    span: Span::new(&source, 62, 63).unwrap()
                                }
                            )),
                            Expression::Literal(LiteralExpression::DecimalLiteral(
                                DecimalLiteralExpression {
                                    suffix: None,
                                    value: DecimalNumber {
                                        span: Span::new(&source, 69, 70).unwrap()
                                    },
                                    span: Span::new(&source, 69, 70).unwrap()
                                }
                            )),
                            Expression::Literal(LiteralExpression::DecimalLiteral(
                                DecimalLiteralExpression {
                                    suffix: None,
                                    value: DecimalNumber {
                                        span: Span::new(&source, 76, 77).unwrap()
                                    },
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
                pragma: None,
                structs: vec![],
                functions: vec![Function {
                    generics: vec![],
                    id: IdentifierExpression {
                        value: String::from("main"),
                        span: Span::new(&source, 4, 8).unwrap()
                    },
                    parameters: vec![],
                    returns: vec![Type::Basic(BasicType::Field(FieldType {
                        span: Span::new(&source, 15, 20).unwrap()
                    }))],
                    statements: vec![Statement::Return(ReturnStatement {
                        expressions: vec![Expression::Literal(LiteralExpression::DecimalLiteral(
                            DecimalLiteralExpression {
                                suffix: None,
                                value: DecimalNumber {
                                    span: Span::new(&source, 31, 32).unwrap()
                                },
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
                pragma: None,
                structs: vec![],
                functions: vec![Function {
                    generics: vec![],
                    id: IdentifierExpression {
                        value: String::from("main"),
                        span: Span::new(&source, 4, 8).unwrap()
                    },
                    parameters: vec![],
                    returns: vec![Type::Basic(BasicType::Field(FieldType {
                        span: Span::new(&source, 15, 20).unwrap()
                    }))],
                    statements: vec![Statement::Definition(DefinitionStatement {
                        lhs: vec![
                            OptionallyTypedAssignee {
                                ty: Some(Type::Basic(BasicType::Field(FieldType {
                                    span: Span::new(&source, 23, 28).unwrap()
                                }))),
                                a: Assignee {
                                    id: IdentifierExpression {
                                        value: String::from("a"),
                                        span: Span::new(&source, 29, 30).unwrap(),
                                    },
                                    accesses: vec![],
                                    span: Span::new(&source, 29, 30).unwrap()
                                },
                                span: Span::new(&source, 23, 30).unwrap()
                            },
                            OptionallyTypedAssignee {
                                ty: None,
                                a: Assignee {
                                    id: IdentifierExpression {
                                        value: String::from("b"),
                                        span: Span::new(&source, 32, 33).unwrap(),
                                    },
                                    accesses: vec![],
                                    span: Span::new(&source, 32, 34).unwrap()
                                },
                                span: Span::new(&source, 32, 34).unwrap()
                            },
                        ],
                        expression: Expression::Postfix(PostfixExpression {
                            id: IdentifierExpression {
                                value: String::from("foo"),
                                span: Span::new(&source, 36, 39).unwrap()
                            },
                            accesses: vec![Access::Call(CallAccess {
                                explicit_generics: None,
                                arguments: Arguments {
                                    expressions: vec![
                                        Expression::Literal(LiteralExpression::DecimalLiteral(
                                            DecimalLiteralExpression {
                                                suffix: None,
                                                value: DecimalNumber {
                                                    span: Span::new(&source, 40, 41).unwrap()
                                                },
                                                span: Span::new(&source, 40, 41).unwrap()
                                            }
                                        )),
                                        Expression::add(
                                            Expression::Literal(LiteralExpression::DecimalLiteral(
                                                DecimalLiteralExpression {
                                                    suffix: None,
                                                    value: DecimalNumber {
                                                        span: Span::new(&source, 43, 44).unwrap()
                                                    },
                                                    span: Span::new(&source, 43, 44).unwrap()
                                                }
                                            )),
                                            Expression::Literal(LiteralExpression::DecimalLiteral(
                                                DecimalLiteralExpression {
                                                    suffix: None,
                                                    value: DecimalNumber {
                                                        span: Span::new(&source, 47, 48).unwrap()
                                                    },
                                                    span: Span::new(&source, 47, 48).unwrap()
                                                }
                                            )),
                                            Span::new(&source, 43, 48).unwrap()
                                        ),
                                    ],
                                    span: Span::new(&source, 40, 48).unwrap()
                                },
                                span: Span::new(&source, 39, 49).unwrap()
                            })],
                            span: Span::new(&source, 36, 49).unwrap(),
                        }),
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
        let source = r#"import "foo" as bar

        struct Foo {
            field[2] foo
            Bar bar
        }

        def main<P>(private field[Q] a) -> (bool[234 + 6]):
        field a = 1
        a[32 + x][55] = foo::<a, _>(y)
        for field i in 0..3 do
               assert(a == 1 + 2 + 3+ 4+ 5+ 6+ 6+ 7+ 8 + 4+ 5+ 3+ 4+ 2+ 3)
        endfor
        assert(a.member == 1)
        return a
"#;
        let res = generate_ast(&source);
        println!("{:#?}", generate_ast(&source));
        assert!(res.is_ok());
    }
}
