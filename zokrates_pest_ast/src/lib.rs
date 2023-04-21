// disable a clippy lint as pest_ast generates improper code
#![allow(clippy::clone_on_copy)]

use from_pest::FromPest;
use pest::error::Error as PestError;
use pest::iterators::Pairs;
use std::fmt;
use zokrates_parser::parse;
use zokrates_parser::Rule;
#[macro_use]
extern crate lazy_static;

pub use ast::{
    Access, Arguments, ArrayAccess, ArrayInitializerExpression, ArrayType, AssemblyStatement,
    AssemblyStatementInner, AssertionStatement, Assignee, AssigneeAccess, AssignmentOperator,
    BasicOrStructOrTupleType, BasicType, BinaryExpression, BinaryOperator, CallAccess,
    ConstantDefinition, ConstantGenericValue, DecimalLiteralExpression, DecimalNumber,
    DecimalSuffix, DefinitionStatement, ExplicitGenerics, Expression, FieldType, File,
    FromExpression, FunctionDefinition, HexLiteralExpression, HexNumberExpression,
    IdentifierExpression, IdentifierOrDecimal, IfElseExpression, ImportDirective, ImportSymbol,
    InlineArrayExpression, InlineStructExpression, InlineStructMember, InlineTupleExpression,
    IterationStatement, LiteralExpression, LogStatement, Parameter, PostfixExpression, Range,
    RangeOrExpression, ReturnStatement, Span, Spread, SpreadOrExpression, Statement,
    StructDefinition, StructField, SymbolDeclaration, TernaryExpression, ToExpression, Type,
    TypeDefinition, TypedIdentifier, TypedIdentifierOrAssignee, UnaryExpression, UnaryOperator,
    Underscore, Visibility,
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
            Operator::new(Rule::op_ternary, Assoc::Right),
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
        let (start, _) = lhs.span().split();
        let (_, end) = rhs.span().split();
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
            Rule::op_ternary => Expression::ternary(
                lhs,
                Box::new(Expression::from_pest(&mut pair.into_inner()).unwrap()),
                rhs,
                span,
            ),
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
        pub declarations: Vec<SymbolDeclaration<'ast>>,
        pub eoi: EOI,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::pragma))]
    pub struct Pragma<'ast> {
        pub curve: Curve<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::curve))]
    pub struct Curve<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub name: String,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[allow(clippy::large_enum_variant)]
    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::symbol_declaration))]
    pub enum SymbolDeclaration<'ast> {
        Import(ImportDirective<'ast>),
        Constant(ConstantDefinition<'ast>),
        Struct(StructDefinition<'ast>),
        Type(TypeDefinition<'ast>),
        Function(FunctionDefinition<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::ty_struct_definition))]
    pub struct StructDefinition<'ast> {
        pub id: IdentifierExpression<'ast>,
        pub generics: Vec<IdentifierExpression<'ast>>,
        pub fields: Vec<StructField<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::struct_field))]
    pub struct StructField<'ast> {
        pub id: TypedIdentifier<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::function_definition))]
    pub struct FunctionDefinition<'ast> {
        pub id: IdentifierExpression<'ast>,
        pub generics: Vec<IdentifierExpression<'ast>>,
        pub parameters: Vec<Parameter<'ast>>,
        pub return_type: Option<Type<'ast>>,
        pub statements: Vec<Statement<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::const_definition))]
    pub struct ConstantDefinition<'ast> {
        pub id: TypedIdentifier<'ast>,
        pub expression: Expression<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::type_definition))]
    pub struct TypeDefinition<'ast> {
        pub id: IdentifierExpression<'ast>,
        pub generics: Vec<IdentifierExpression<'ast>>,
        pub ty: Type<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::import_directive))]
    pub enum ImportDirective<'ast> {
        Main(MainImportDirective<'ast>),
        From(FromImportDirective<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::main_import_directive))]
    pub struct MainImportDirective<'ast> {
        pub source: QString<'ast>,
        pub alias: Option<IdentifierExpression<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::import_symbol))]
    pub struct ImportSymbol<'ast> {
        pub id: IdentifierExpression<'ast>,
        pub alias: Option<IdentifierExpression<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::from_import_directive))]
    pub struct FromImportDirective<'ast> {
        pub source: QString<'ast>,
        pub symbols: Vec<ImportSymbol<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::ty))]
    pub enum Type<'ast> {
        Basic(BasicType<'ast>),
        Array(ArrayType<'ast>),
        Struct(StructType<'ast>),
        Tuple(TupleType<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::ty_basic))]
    pub enum BasicType<'ast> {
        Field(FieldType<'ast>),
        Boolean(BooleanType<'ast>),
        U8(U8Type<'ast>),
        U16(U16Type<'ast>),
        U32(U32Type<'ast>),
        U64(U64Type<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::ty_field))]
    pub struct FieldType<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::ty_array))]
    pub struct ArrayType<'ast> {
        pub ty: BasicOrStructOrTupleType<'ast>,
        pub dimensions: Vec<Expression<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::ty_basic_or_struct_or_tuple))]
    pub enum BasicOrStructOrTupleType<'ast> {
        Struct(StructType<'ast>),
        Basic(BasicType<'ast>),
        Tuple(TupleType<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::ty_bool))]
    pub struct BooleanType<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::ty_u8))]
    pub struct U8Type<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::ty_u16))]
    pub struct U16Type<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::ty_u32))]
    pub struct U32Type<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::ty_u64))]
    pub struct U64Type<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::ty_struct))]
    pub struct StructType<'ast> {
        pub id: IdentifierExpression<'ast>,
        pub explicit_generics: Option<ExplicitGenerics<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::ty_tuple))]
    pub struct TupleType<'ast> {
        pub elements: Vec<Type<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::parameter))]
    pub struct Parameter<'ast> {
        pub visibility: Option<Visibility>,
        pub ty: Type<'ast>,
        pub mutable: Option<Mutable>,
        pub id: IdentifierExpression<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::vis))]
    pub enum Visibility {
        Public(PublicVisibility),
        Private(PrivateVisibility),
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::vis_public))]
    pub struct PublicVisibility {}

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
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
        Log(LogStatement<'ast>),
        Assembly(AssemblyStatement<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::log_statement))]
    pub struct LogStatement<'ast> {
        pub format_string: QString<'ast>,
        pub expressions: Vec<Expression<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::definition_statement))]
    pub struct DefinitionStatement<'ast> {
        pub lhs: TypedIdentifierOrAssignee<'ast>,
        pub expression: Expression<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::string))]
    pub struct RawString<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub value: String,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::quoted_string))]
    pub struct QString<'ast> {
        pub raw: RawString<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::assertion_statement))]
    pub struct AssertionStatement<'ast> {
        pub expression: Expression<'ast>,
        pub message: Option<QString<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::iteration_statement))]
    pub struct IterationStatement<'ast> {
        pub index: TypedIdentifier<'ast>,
        pub from: Expression<'ast>,
        pub to: Expression<'ast>,
        pub statements: Vec<Statement<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::return_statement))]
    pub struct ReturnStatement<'ast> {
        pub expression: Option<Expression<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::op_asm))]
    pub enum AssignmentOperator {
        Assign(AssignOperator),
        AssignConstrain(AssignConstrainOperator),
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::op_asm_assign))]
    pub struct AssignOperator;

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::op_asm_assign_constrain))]
    pub struct AssignConstrainOperator;

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::asm_assignment))]
    pub struct AssemblyAssignment<'ast> {
        pub assignee: Assignee<'ast>,
        pub operator: AssignmentOperator,
        pub expression: Expression<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::asm_constraint))]
    pub struct AssemblyConstraint<'ast> {
        pub lhs: Expression<'ast>,
        pub rhs: Expression<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::asm_statement_inner))]
    pub enum AssemblyStatementInner<'ast> {
        Assignment(AssemblyAssignment<'ast>),
        Constraint(AssemblyConstraint<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::asm_statement))]
    pub struct AssemblyStatement<'ast> {
        pub inner: Vec<AssemblyStatementInner<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
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
        IfElse(IfElseExpression<'ast>),
        Binary(BinaryExpression<'ast>),
        Unary(UnaryExpression<'ast>),
        Postfix(PostfixExpression<'ast>),
        Identifier(IdentifierExpression<'ast>),
        Literal(LiteralExpression<'ast>),
        InlineArray(InlineArrayExpression<'ast>),
        InlineStruct(InlineStructExpression<'ast>),
        InlineTuple(InlineTupleExpression<'ast>),
        ArrayInitializer(ArrayInitializerExpression<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::term))]
    pub enum Term<'ast> {
        Expression(Expression<'ast>),
        InlineStruct(InlineStructExpression<'ast>),
        IfElse(IfElseExpression<'ast>),
        Primary(PrimaryExpression<'ast>),
        InlineArray(InlineArrayExpression<'ast>),
        InlineTuple(InlineTupleExpression<'ast>),
        ArrayInitializer(ArrayInitializerExpression<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::postfixed_term))]
    pub struct PostfixedTerm<'ast> {
        pub base: Term<'ast>,
        pub accesses: Vec<Access<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, Clone, PartialEq)]
    pub struct PostfixExpression<'ast> {
        pub base: Box<Expression<'ast>>,
        pub accesses: Vec<Access<'ast>>,
        pub span: Span<'ast>,
    }

    impl<'ast> From<PostfixedTerm<'ast>> for Expression<'ast> {
        fn from(t: PostfixedTerm<'ast>) -> Self {
            let base = Expression::from(t.base);
            let accesses = t.accesses;
            if accesses.is_empty() {
                base
            } else {
                Expression::Postfix(PostfixExpression {
                    base: Box::new(base),
                    accesses,
                    span: t.span,
                })
            }
        }
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::powered_term))]
    struct PoweredTerm<'ast> {
        base: PostfixedTerm<'ast>,
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

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::op_unary))]
    pub enum UnaryOperator {
        Pos(PosOperator),
        Neg(NegOperator),
        Not(NotOperator),
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::op_pos))]
    pub struct PosOperator;

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::op_neg))]
    pub struct NegOperator;

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::op_not))]
    pub struct NotOperator;

    impl<'ast> From<Term<'ast>> for Expression<'ast> {
        fn from(t: Term<'ast>) -> Self {
            match t {
                Term::Expression(e) => e,
                Term::IfElse(e) => Expression::IfElse(e),
                Term::Primary(e) => e.into(),
                Term::InlineArray(e) => Expression::InlineArray(e),
                Term::InlineTuple(e) => Expression::InlineTuple(e),
                Term::InlineStruct(e) => Expression::InlineStruct(e),
                Term::ArrayInitializer(e) => Expression::ArrayInitializer(e),
            }
        }
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
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
    #[pest_ast(rule(Rule::inline_tuple_expression))]
    pub struct InlineTupleExpression<'ast> {
        pub elements: Vec<Expression<'ast>>,
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
    #[pest_ast(rule(Rule::typed_identifier_or_assignee))]
    pub enum TypedIdentifierOrAssignee<'ast> {
        Assignee(Assignee<'ast>),
        TypedIdentifier(TypedIdentifier<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::_mut))]
    pub struct Mutable {}

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::typed_identifier))]
    pub struct TypedIdentifier<'ast> {
        pub ty: Type<'ast>,
        pub mutable: Option<Mutable>,
        pub identifier: IdentifierExpression<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[allow(clippy::large_enum_variant)]
    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::access))]
    pub enum Access<'ast> {
        Call(CallAccess<'ast>),
        Select(ArrayAccess<'ast>),
        Dot(DotAccess<'ast>),
    }

    #[allow(clippy::large_enum_variant)]
    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::assignee_access))]
    pub enum AssigneeAccess<'ast> {
        Select(ArrayAccess<'ast>),
        Dot(DotAccess<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::call_access))]
    pub struct CallAccess<'ast> {
        pub explicit_generics: Option<ExplicitGenerics<'ast>>,
        pub arguments: Arguments<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::explicit_generics))]
    pub struct ExplicitGenerics<'ast> {
        pub values: Vec<ConstantGenericValue<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::constant_generics_value))]
    pub enum ConstantGenericValue<'ast> {
        Value(LiteralExpression<'ast>),
        Identifier(IdentifierExpression<'ast>),
        Underscore(Underscore<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
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

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::dot_access))]
    pub struct DotAccess<'ast> {
        pub inner: IdentifierOrDecimal<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::identifier_or_decimal))]
    pub enum IdentifierOrDecimal<'ast> {
        Identifier(IdentifierExpression<'ast>),
        Decimal(DecimalNumber<'ast>),
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

    #[derive(Debug, PartialEq, Clone)]
    pub struct TernaryExpression<'ast> {
        pub condition: Box<Expression<'ast>>,
        pub consequence: Box<Expression<'ast>>,
        pub alternative: Box<Expression<'ast>>,
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Clone)]
    #[pest_ast(rule(Rule::if_else_expression))]
    pub struct IfElseExpression<'ast> {
        pub condition: Box<Expression<'ast>>,
        pub consequence_statements: Vec<Statement<'ast>>,
        pub consequence: Box<Expression<'ast>>,
        pub alternative_statements: Vec<Statement<'ast>>,
        pub alternative: Box<Expression<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    impl<'ast> Expression<'ast> {
        pub fn if_else(
            condition: Box<Expression<'ast>>,
            consequence: Box<Expression<'ast>>,
            alternative: Box<Expression<'ast>>,
            span: Span<'ast>,
        ) -> Self {
            Expression::IfElse(IfElseExpression {
                condition,
                consequence_statements: vec![],
                consequence,
                alternative_statements: vec![],
                alternative,
                span,
            })
        }

        pub fn ternary(
            condition: Box<Expression<'ast>>,
            consequence: Box<Expression<'ast>>,
            alternative: Box<Expression<'ast>>,
            span: Span<'ast>,
        ) -> Self {
            Expression::Ternary(TernaryExpression {
                condition,
                consequence,
                alternative,
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
                Expression::Literal(c) => c.span(),
                Expression::Ternary(t) => &t.span,
                Expression::IfElse(ie) => &ie.span,
                Expression::Postfix(p) => &p.span,
                Expression::InlineArray(a) => &a.span,
                Expression::InlineStruct(s) => &s.span,
                Expression::InlineTuple(t) => &t.span,
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

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
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

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::decimal_suffix))]
    pub enum DecimalSuffix<'ast> {
        U8(U8Suffix<'ast>),
        U16(U16Suffix<'ast>),
        U32(U32Suffix<'ast>),
        U64(U64Suffix<'ast>),
        Field(FieldSuffix<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::decimal_suffix_u8))]
    pub struct U8Suffix<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::decimal_suffix_u16))]
    pub struct U16Suffix<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::decimal_suffix_u32))]
    pub struct U32Suffix<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::decimal_suffix_u64))]
    pub struct U64Suffix<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::decimal_suffix_field))]
    pub struct FieldSuffix<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::decimal_number))]
    pub struct DecimalNumber<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::decimal_literal))]
    pub struct DecimalLiteralExpression<'ast> {
        pub value: DecimalNumber<'ast>,
        pub suffix: Option<DecimalSuffix<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::boolean_literal))]
    pub struct BooleanLiteralExpression<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub value: String,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::hex_literal))]
    pub struct HexLiteralExpression<'ast> {
        pub value: HexNumberExpression<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::hex_number))]
    pub enum HexNumberExpression<'ast> {
        U8(U8NumberExpression<'ast>),
        U16(U16NumberExpression<'ast>),
        U32(U32NumberExpression<'ast>),
        U64(U64NumberExpression<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::hex_number_u8))]
    pub struct U8NumberExpression<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub value: String,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::hex_number_u16))]
    pub struct U16NumberExpression<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub value: String,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::hex_number_u32))]
    pub struct U32NumberExpression<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub value: String,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::hex_number_u64))]
    pub struct U64NumberExpression<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub value: String,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
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

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
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

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Error(PestError<Rule>);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[allow(clippy::result_large_err)]
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
    }

    #[test]
    fn one_plus_one() {
        let source = r#"
        import "foo";

        def main() -> field {
            return 1 + 1;
        }
"#;
        assert_eq!(
            generate_ast(source),
            Ok(File {
                pragma: None,
                declarations: vec![
                    SymbolDeclaration::Import(ImportDirective::Main(MainImportDirective {
                        source: QString {
                            raw: RawString {
                                value: String::from("foo"),
                                span: Span::new(source, 17, 20).unwrap()
                            },
                            span: Span::new(source, 16, 21).unwrap()
                        },
                        alias: None,
                        span: Span::new(source, 9, 21).unwrap()
                    })),
                    SymbolDeclaration::Function(FunctionDefinition {
                        generics: vec![],
                        id: IdentifierExpression {
                            value: String::from("main"),
                            span: Span::new(source, 36, 40).unwrap()
                        },
                        parameters: vec![],
                        return_type: Some(Type::Basic(BasicType::Field(FieldType {
                            span: Span::new(source, 46, 51).unwrap()
                        }))),
                        statements: vec![Statement::Return(ReturnStatement {
                            expression: Some(Expression::add(
                                Expression::Literal(LiteralExpression::DecimalLiteral(
                                    DecimalLiteralExpression {
                                        value: DecimalNumber {
                                            span: Span::new(source, 73, 74).unwrap()
                                        },
                                        suffix: None,
                                        span: Span::new(source, 73, 74).unwrap()
                                    }
                                )),
                                Expression::Literal(LiteralExpression::DecimalLiteral(
                                    DecimalLiteralExpression {
                                        value: DecimalNumber {
                                            span: Span::new(source, 77, 78).unwrap()
                                        },
                                        suffix: None,
                                        span: Span::new(source, 77, 78).unwrap()
                                    }
                                )),
                                Span::new(source, 73, 78).unwrap()
                            )),
                            span: Span::new(source, 66, 78).unwrap(),
                        })],
                        span: Span::new(source, 32, 89).unwrap(),
                    })
                ],
                eoi: EOI {},
                span: Span::new(source, 0, 90).unwrap()
            })
        );
    }

    #[test]
    fn precedence() {
        let source = r#"
        import "foo";

        def main() -> field {
            return 1 + 2 * 3 ** 4;
        }
"#;
        assert_eq!(
            generate_ast(source),
            Ok(File {
                pragma: None,
                declarations: vec![
                    SymbolDeclaration::Import(ImportDirective::Main(MainImportDirective {
                        source: QString {
                            raw: RawString {
                                value: String::from("foo"),
                                span: Span::new(source, 17, 20).unwrap()
                            },
                            span: Span::new(source, 16, 21).unwrap()
                        },
                        alias: None,
                        span: Span::new(source, 9, 21).unwrap()
                    })),
                    SymbolDeclaration::Function(FunctionDefinition {
                        generics: vec![],
                        id: IdentifierExpression {
                            value: String::from("main"),
                            span: Span::new(source, 36, 40).unwrap()
                        },
                        parameters: vec![],
                        return_type: Some(Type::Basic(BasicType::Field(FieldType {
                            span: Span::new(source, 46, 51).unwrap()
                        }))),
                        statements: vec![Statement::Return(ReturnStatement {
                            expression: Some(Expression::add(
                                Expression::Literal(LiteralExpression::DecimalLiteral(
                                    DecimalLiteralExpression {
                                        suffix: None,
                                        value: DecimalNumber {
                                            span: Span::new(source, 73, 74).unwrap()
                                        },
                                        span: Span::new(source, 73, 74).unwrap()
                                    }
                                )),
                                Expression::mul(
                                    Expression::Literal(LiteralExpression::DecimalLiteral(
                                        DecimalLiteralExpression {
                                            suffix: None,
                                            value: DecimalNumber {
                                                span: Span::new(source, 77, 78).unwrap()
                                            },
                                            span: Span::new(source, 77, 78).unwrap()
                                        }
                                    )),
                                    Expression::pow(
                                        Expression::Literal(LiteralExpression::DecimalLiteral(
                                            DecimalLiteralExpression {
                                                suffix: None,
                                                value: DecimalNumber {
                                                    span: Span::new(source, 81, 82).unwrap()
                                                },
                                                span: Span::new(source, 81, 82).unwrap()
                                            }
                                        )),
                                        Expression::Literal(LiteralExpression::DecimalLiteral(
                                            DecimalLiteralExpression {
                                                suffix: None,
                                                value: DecimalNumber {
                                                    span: Span::new(source, 86, 87).unwrap()
                                                },
                                                span: Span::new(source, 86, 87).unwrap()
                                            }
                                        )),
                                        Span::new(source, 81, 87).unwrap()
                                    ),
                                    Span::new(source, 77, 87).unwrap()
                                ),
                                Span::new(source, 73, 87).unwrap()
                            )),
                            span: Span::new(source, 66, 87).unwrap(),
                        })],
                        span: Span::new(source, 32, 98).unwrap(),
                    })
                ],
                eoi: EOI {},
                span: Span::new(source, 0, 99).unwrap()
            })
        );
    }

    #[test]
    fn ternary() {
        let source = r#"
        import "foo";

        def main() -> field {
            return 1 ? 2 : 3;
        }
"#;
        assert_eq!(
            generate_ast(source),
            Ok(File {
                pragma: None,
                declarations: vec![
                    SymbolDeclaration::Import(ImportDirective::Main(MainImportDirective {
                        source: QString {
                            raw: RawString {
                                value: String::from("foo"),
                                span: Span::new(source, 17, 20).unwrap()
                            },
                            span: Span::new(source, 16, 21).unwrap()
                        },
                        alias: None,
                        span: Span::new(source, 9, 21).unwrap()
                    })),
                    SymbolDeclaration::Function(FunctionDefinition {
                        generics: vec![],
                        id: IdentifierExpression {
                            value: String::from("main"),
                            span: Span::new(source, 36, 40).unwrap()
                        },
                        parameters: vec![],
                        return_type: Some(Type::Basic(BasicType::Field(FieldType {
                            span: Span::new(source, 46, 51).unwrap()
                        }))),
                        statements: vec![Statement::Return(ReturnStatement {
                            expression: Some(Expression::ternary(
                                Box::new(Expression::Literal(LiteralExpression::DecimalLiteral(
                                    DecimalLiteralExpression {
                                        suffix: None,
                                        value: DecimalNumber {
                                            span: Span::new(source, 73, 74).unwrap()
                                        },
                                        span: Span::new(source, 73, 74).unwrap()
                                    }
                                ))),
                                Box::new(Expression::Literal(LiteralExpression::DecimalLiteral(
                                    DecimalLiteralExpression {
                                        suffix: None,
                                        value: DecimalNumber {
                                            span: Span::new(source, 77, 78).unwrap()
                                        },
                                        span: Span::new(source, 77, 78).unwrap()
                                    }
                                ))),
                                Box::new(Expression::Literal(LiteralExpression::DecimalLiteral(
                                    DecimalLiteralExpression {
                                        suffix: None,
                                        value: DecimalNumber {
                                            span: Span::new(source, 81, 82).unwrap()
                                        },
                                        span: Span::new(source, 81, 82).unwrap()
                                    }
                                ))),
                                Span::new(source, 73, 82).unwrap()
                            )),
                            span: Span::new(source, 66, 82).unwrap(),
                        })],
                        span: Span::new(source, 32, 93).unwrap(),
                    })
                ],
                eoi: EOI {},
                span: Span::new(source, 0, 94).unwrap()
            })
        );
    }

    #[test]
    fn parentheses() {
        let source = r#"def main() -> field { return 1; }
"#;
        assert_eq!(
            generate_ast(source),
            Ok(File {
                pragma: None,
                declarations: vec![SymbolDeclaration::Function(FunctionDefinition {
                    generics: vec![],
                    id: IdentifierExpression {
                        value: String::from("main"),
                        span: Span::new(source, 4, 8).unwrap()
                    },
                    parameters: vec![],
                    return_type: Some(Type::Basic(BasicType::Field(FieldType {
                        span: Span::new(source, 14, 19).unwrap()
                    }))),
                    statements: vec![Statement::Return(ReturnStatement {
                        expression: Some(Expression::Literal(LiteralExpression::DecimalLiteral(
                            DecimalLiteralExpression {
                                suffix: None,
                                value: DecimalNumber {
                                    span: Span::new(source, 29, 30).unwrap()
                                },
                                span: Span::new(source, 29, 30).unwrap()
                            }
                        ))),
                        span: Span::new(source, 22, 30).unwrap(),
                    })],
                    span: Span::new(source, 0, 33).unwrap(),
                })],
                eoi: EOI {},
                span: Span::new(source, 0, 34).unwrap()
            })
        );
    }

    #[test]
    fn playground() {
        let source = r#"
        import "foo" as bar;

        struct Foo {
            field[2] foo;
            Bar bar;
        }

        def main<P>(private field[Q] a) -> bool[234 + 6] {
            field a = 1;
            a[32 + x][55] = foo::<a, _>(y);
            for field i in 0..3 {
                assert(a == 1 + 2 + 3 + 4 + 5 + 6 + 6 + 7 + 8 + 4 + 5 + 3 + 4 + 2 + 3);
            }
            assert(a.member == 1);
            return a;
        }
"#;
        let res = generate_ast(source);
        assert!(res.is_ok());
    }

    #[test]
    fn tuples() {
        let source = r#"struct Foo {
            field a;
        }
        
        def foo() -> (field, field) {
            return (1, 2);
        }
        
        def main((field, field) a, (field,) b) -> (Foo,)[2] {
            (field, field) c = foo();
            return [(Foo {a: a.0},); 2];
        }
"#;
        let res = generate_ast(source);
        assert!(res.is_ok());
    }
}
