use crate::untyped::{self, ConditionalExpression, SymbolDefinition};
use num_bigint::BigUint;
use std::path::Path;
use zokrates_pest_ast as pest;

impl<'ast> From<pest::File<'ast>> for untyped::Module<'ast> {
    fn from(file: pest::File<'ast>) -> untyped::Module<'ast> {
        untyped::Module::with_symbols(file.declarations.into_iter().flat_map(|d| match d {
            pest::SymbolDeclaration::Import(i) => import_directive_to_symbol_vec(i),
            pest::SymbolDeclaration::Constant(c) => vec![c.into()],
            pest::SymbolDeclaration::Struct(s) => vec![s.into()],
            pest::SymbolDeclaration::Type(t) => vec![t.into()],
            pest::SymbolDeclaration::Function(f) => vec![f.into()],
        }))
    }
}

fn import_directive_to_symbol_vec(
    import: pest::ImportDirective,
) -> Vec<untyped::SymbolDeclarationNode> {
    use crate::untyped::NodeValue;

    match import {
        pest::ImportDirective::Main(import) => {
            let span = import.span;
            let source = Path::new(import.source.raw.span.as_str());
            let id = "main";
            let alias = import.alias.map(|a| a.span.as_str());

            let import = untyped::CanonicalImport {
                source,
                id: untyped::SymbolIdentifier::from(id).alias(alias),
            }
            .span(span);

            vec![untyped::SymbolDeclaration {
                id: alias.unwrap_or(id),
                symbol: untyped::Symbol::Here(untyped::SymbolDefinition::Import(import)),
            }
            .span(span)]
        }
        pest::ImportDirective::From(import) => {
            let span = import.span;
            let source = Path::new(import.source.raw.span.as_str());
            import
                .symbols
                .into_iter()
                .map(|symbol| {
                    let alias = symbol
                        .alias
                        .as_ref()
                        .map(|a| a.span.as_str())
                        .unwrap_or_else(|| symbol.id.span.as_str());

                    let import = untyped::CanonicalImport {
                        source,
                        id: untyped::SymbolIdentifier::from(symbol.id.span.as_str())
                            .alias(Some(alias)),
                    }
                    .span(span);

                    untyped::SymbolDeclaration {
                        id: alias,
                        symbol: untyped::Symbol::Here(untyped::SymbolDefinition::Import(import)),
                    }
                    .span(span)
                })
                .collect()
        }
    }
}

impl<'ast> From<pest::StructDefinition<'ast>> for untyped::SymbolDeclarationNode<'ast> {
    fn from(definition: pest::StructDefinition<'ast>) -> untyped::SymbolDeclarationNode<'ast> {
        use crate::untyped::NodeValue;

        let span = definition.span;

        let id = definition.id.span.as_str();

        let ty = untyped::StructDefinition {
            generics: definition
                .generics
                .into_iter()
                .map(untyped::ConstantGenericNode::from)
                .collect(),
            fields: definition
                .fields
                .into_iter()
                .map(untyped::StructDefinitionFieldNode::from)
                .collect(),
        }
        .span(span);

        untyped::SymbolDeclaration {
            id,
            symbol: untyped::Symbol::Here(untyped::SymbolDefinition::Struct(ty)),
        }
        .span(span)
    }
}

impl<'ast> From<pest::StructField<'ast>> for untyped::StructDefinitionFieldNode<'ast> {
    fn from(field: pest::StructField<'ast>) -> untyped::StructDefinitionFieldNode<'ast> {
        use crate::untyped::NodeValue;

        let span = field.span;

        let id = field.id.identifier.span.as_str();

        let ty = untyped::UnresolvedTypeNode::from(field.id.ty);

        untyped::StructDefinitionField { id, ty }.span(span)
    }
}

impl<'ast> From<pest::ConstantDefinition<'ast>> for untyped::SymbolDeclarationNode<'ast> {
    fn from(definition: pest::ConstantDefinition<'ast>) -> untyped::SymbolDeclarationNode<'ast> {
        use crate::untyped::NodeValue;

        let span = definition.span;
        let id = definition.id.identifier.span.as_str();

        let ty = untyped::ConstantDefinition {
            ty: definition.id.ty.into(),
            expression: definition.expression.into(),
        }
        .span(span);

        untyped::SymbolDeclaration {
            id,
            symbol: untyped::Symbol::Here(untyped::SymbolDefinition::Constant(ty)),
        }
        .span(span)
    }
}

impl<'ast> From<pest::TypeDefinition<'ast>> for untyped::SymbolDeclarationNode<'ast> {
    fn from(definition: pest::TypeDefinition<'ast>) -> untyped::SymbolDeclarationNode<'ast> {
        use crate::untyped::NodeValue;

        let span = definition.span;
        let id = definition.id.span.as_str();

        let ty = untyped::TypeDefinition {
            generics: definition
                .generics
                .into_iter()
                .map(untyped::ConstantGenericNode::from)
                .collect(),
            ty: definition.ty.into(),
        }
        .span(span);

        untyped::SymbolDeclaration {
            id,
            symbol: untyped::Symbol::Here(SymbolDefinition::Type(ty)),
        }
        .span(span)
    }
}

impl<'ast> From<pest::FunctionDefinition<'ast>> for untyped::SymbolDeclarationNode<'ast> {
    fn from(function: pest::FunctionDefinition<'ast>) -> untyped::SymbolDeclarationNode<'ast> {
        use crate::untyped::NodeValue;

        let span = function.span;

        let signature = untyped::UnresolvedSignature::new()
            .generics(
                function
                    .generics
                    .into_iter()
                    .map(untyped::ConstantGenericNode::from)
                    .collect(),
            )
            .inputs(
                function
                    .parameters
                    .clone()
                    .into_iter()
                    .map(|p| untyped::UnresolvedTypeNode::from(p.ty))
                    .collect(),
            );

        let signature = match function.return_type {
            Some(ret_ty) => signature.output(untyped::UnresolvedTypeNode::from(ret_ty)),
            None => signature,
        };

        let id = function.id.span.as_str();

        let function = untyped::Function {
            arguments: function
                .parameters
                .into_iter()
                .map(untyped::ParameterNode::from)
                .collect(),
            statements: function.statements.into_iter().map(|s| s.into()).collect(),
            signature,
        }
        .span(span);

        untyped::SymbolDeclaration {
            id,
            symbol: untyped::Symbol::Here(untyped::SymbolDefinition::Function(function)),
        }
        .span(span)
    }
}

impl<'ast> From<pest::IdentifierExpression<'ast>> for untyped::ConstantGenericNode<'ast> {
    fn from(g: pest::IdentifierExpression<'ast>) -> untyped::ConstantGenericNode<'ast> {
        use untyped::NodeValue;

        let name = g.span.as_str();

        name.span(g.span)
    }
}

impl<'ast> From<pest::Parameter<'ast>> for untyped::ParameterNode<'ast> {
    fn from(param: pest::Parameter<'ast>) -> untyped::ParameterNode<'ast> {
        use crate::untyped::NodeValue;

        let is_private = param.visibility.map(|v| match v {
            pest::Visibility::Private(_) => true,
            pest::Visibility::Public(_) => false,
        });

        let is_mutable = param.mutable.is_some();

        let variable = untyped::Variable::new(
            param.id.span.as_str(),
            untyped::UnresolvedTypeNode::from(param.ty),
            is_mutable,
        )
        .span(param.id.span);

        untyped::Parameter::new(variable, is_private).span(param.span)
    }
}

impl<'ast> From<pest::LogStatement<'ast>> for untyped::StatementNode<'ast> {
    fn from(statement: pest::LogStatement<'ast>) -> untyped::StatementNode<'ast> {
        use crate::untyped::NodeValue;

        let expressions = statement
            .expressions
            .into_iter()
            .map(untyped::ExpressionNode::from)
            .collect();

        untyped::Statement::Log(statement.format_string.raw.span.as_str(), expressions)
            .span(statement.span)
    }
}

impl<'ast> From<pest::TypedIdentifier<'ast>> for untyped::VariableNode<'ast> {
    fn from(i: pest::TypedIdentifier<'ast>) -> Self {
        use crate::untyped::NodeValue;

        untyped::Variable::new(
            i.identifier.span.as_str(),
            untyped::UnresolvedTypeNode::from(i.ty),
            i.mutable.is_some(),
        )
        .span(i.span)
    }
}

impl<'ast> From<pest::Statement<'ast>> for untyped::StatementNode<'ast> {
    fn from(statement: pest::Statement<'ast>) -> Self {
        match statement {
            pest::Statement::Definition(s) => untyped::StatementNode::from(s),
            pest::Statement::Iteration(s) => untyped::StatementNode::from(s),
            pest::Statement::Assertion(s) => untyped::StatementNode::from(s),
            pest::Statement::Return(s) => untyped::StatementNode::from(s),
            pest::Statement::Log(s) => untyped::StatementNode::from(s),
            pest::Statement::Assembly(s) => untyped::StatementNode::from(s),
        }
    }
}

impl<'ast> From<pest::DefinitionStatement<'ast>> for untyped::StatementNode<'ast> {
    fn from(definition: pest::DefinitionStatement<'ast>) -> Self {
        use crate::untyped::NodeValue;

        let lhs = definition.lhs;
        let e: untyped::ExpressionNode = untyped::ExpressionNode::from(definition.expression);

        match lhs {
            pest::TypedIdentifierOrAssignee::TypedIdentifier(i) => untyped::Statement::Definition(
                untyped::Variable::new(
                    i.identifier.span.as_str(),
                    untyped::UnresolvedTypeNode::from(i.ty),
                    i.mutable.is_some(),
                )
                .span(i.span),
                e,
            ),
            pest::TypedIdentifierOrAssignee::Assignee(a) => {
                untyped::Statement::Assignment(untyped::AssigneeNode::from(a), e)
            }
        }
        .span(definition.span)
    }
}

impl<'ast> From<pest::ReturnStatement<'ast>> for untyped::StatementNode<'ast> {
    fn from(statement: pest::ReturnStatement<'ast>) -> untyped::StatementNode<'ast> {
        use crate::untyped::NodeValue;

        untyped::Statement::Return(statement.expression.map(untyped::ExpressionNode::from))
            .span(statement.span)
    }
}

impl<'ast> From<pest::AssertionStatement<'ast>> for untyped::StatementNode<'ast> {
    fn from(statement: pest::AssertionStatement<'ast>) -> untyped::StatementNode<'ast> {
        use crate::untyped::NodeValue;

        untyped::Statement::Assertion(
            untyped::ExpressionNode::from(statement.expression),
            statement.message.map(|m| m.raw.value),
        )
        .span(statement.span)
    }
}

impl<'ast> From<pest::IterationStatement<'ast>> for untyped::StatementNode<'ast> {
    fn from(statement: pest::IterationStatement<'ast>) -> untyped::StatementNode<'ast> {
        use crate::untyped::NodeValue;
        let index = untyped::VariableNode::from(statement.index);
        let from = untyped::ExpressionNode::from(statement.from);
        let to = untyped::ExpressionNode::from(statement.to);
        let statements: Vec<untyped::StatementNode<'ast>> =
            statement.statements.into_iter().map(|s| s.into()).collect();

        untyped::Statement::For(index, from, to, statements).span(statement.span)
    }
}

impl<'ast> From<pest::AssemblyStatement<'ast>> for untyped::StatementNode<'ast> {
    fn from(statement: pest::AssemblyStatement<'ast>) -> untyped::StatementNode<'ast> {
        use crate::untyped::NodeValue;

        let statements = statement
            .inner
            .into_iter()
            .map(|s| match s {
                pest::AssemblyStatementInner::Assignment(a) => {
                    untyped::AssemblyStatement::Assignment(
                        a.assignee.into(),
                        a.expression.into(),
                        matches!(a.operator, pest::AssignmentOperator::AssignConstrain(_)),
                    )
                    .span(a.span)
                }
                pest::AssemblyStatementInner::Constraint(c) => {
                    untyped::AssemblyStatement::Constraint(c.lhs.into(), c.rhs.into()).span(c.span)
                }
            })
            .collect();

        untyped::Statement::Assembly(statements).span(statement.span)
    }
}

impl<'ast> From<pest::Expression<'ast>> for untyped::ExpressionNode<'ast> {
    fn from(expression: pest::Expression<'ast>) -> untyped::ExpressionNode<'ast> {
        match expression {
            pest::Expression::Binary(e) => untyped::ExpressionNode::from(e),
            pest::Expression::Ternary(e) => untyped::ExpressionNode::from(e),
            pest::Expression::IfElse(e) => untyped::ExpressionNode::from(e),
            pest::Expression::Literal(e) => untyped::ExpressionNode::from(e),
            pest::Expression::Identifier(e) => untyped::ExpressionNode::from(e),
            pest::Expression::Postfix(e) => untyped::ExpressionNode::from(e),
            pest::Expression::InlineArray(e) => untyped::ExpressionNode::from(e),
            pest::Expression::InlineTuple(e) => untyped::ExpressionNode::from(e),
            pest::Expression::InlineStruct(e) => untyped::ExpressionNode::from(e),
            pest::Expression::ArrayInitializer(e) => untyped::ExpressionNode::from(e),
            pest::Expression::Unary(e) => untyped::ExpressionNode::from(e),
        }
    }
}

impl<'ast> From<pest::BinaryExpression<'ast>> for untyped::ExpressionNode<'ast> {
    fn from(expression: pest::BinaryExpression<'ast>) -> untyped::ExpressionNode<'ast> {
        use crate::untyped::NodeValue;
        match expression.op {
            pest::BinaryOperator::Add => untyped::Expression::Add(
                Box::new(untyped::ExpressionNode::from(*expression.left)),
                Box::new(untyped::ExpressionNode::from(*expression.right)),
            ),
            pest::BinaryOperator::Sub => untyped::Expression::Sub(
                Box::new(untyped::ExpressionNode::from(*expression.left)),
                Box::new(untyped::ExpressionNode::from(*expression.right)),
            ),
            pest::BinaryOperator::Mul => untyped::Expression::Mult(
                Box::new(untyped::ExpressionNode::from(*expression.left)),
                Box::new(untyped::ExpressionNode::from(*expression.right)),
            ),
            pest::BinaryOperator::Div => untyped::Expression::Div(
                Box::new(untyped::ExpressionNode::from(*expression.left)),
                Box::new(untyped::ExpressionNode::from(*expression.right)),
            ),
            pest::BinaryOperator::Rem => untyped::Expression::Rem(
                Box::new(untyped::ExpressionNode::from(*expression.left)),
                Box::new(untyped::ExpressionNode::from(*expression.right)),
            ),
            pest::BinaryOperator::Eq => untyped::Expression::Eq(
                Box::new(untyped::ExpressionNode::from(*expression.left)),
                Box::new(untyped::ExpressionNode::from(*expression.right)),
            ),
            pest::BinaryOperator::Lt => untyped::Expression::Lt(
                Box::new(untyped::ExpressionNode::from(*expression.left)),
                Box::new(untyped::ExpressionNode::from(*expression.right)),
            ),
            pest::BinaryOperator::Lte => untyped::Expression::Le(
                Box::new(untyped::ExpressionNode::from(*expression.left)),
                Box::new(untyped::ExpressionNode::from(*expression.right)),
            ),
            pest::BinaryOperator::Gt => untyped::Expression::Gt(
                Box::new(untyped::ExpressionNode::from(*expression.left)),
                Box::new(untyped::ExpressionNode::from(*expression.right)),
            ),
            pest::BinaryOperator::Gte => untyped::Expression::Ge(
                Box::new(untyped::ExpressionNode::from(*expression.left)),
                Box::new(untyped::ExpressionNode::from(*expression.right)),
            ),
            pest::BinaryOperator::And => untyped::Expression::And(
                Box::new(untyped::ExpressionNode::from(*expression.left)),
                Box::new(untyped::ExpressionNode::from(*expression.right)),
            ),
            pest::BinaryOperator::Or => untyped::Expression::Or(
                Box::new(untyped::ExpressionNode::from(*expression.left)),
                Box::new(untyped::ExpressionNode::from(*expression.right)),
            ),
            pest::BinaryOperator::Pow => untyped::Expression::Pow(
                Box::new(untyped::ExpressionNode::from(*expression.left)),
                Box::new(untyped::ExpressionNode::from(*expression.right)),
            ),
            pest::BinaryOperator::BitXor => untyped::Expression::BitXor(
                Box::new(untyped::ExpressionNode::from(*expression.left)),
                Box::new(untyped::ExpressionNode::from(*expression.right)),
            ),
            pest::BinaryOperator::LeftShift => untyped::Expression::LeftShift(
                Box::new(untyped::ExpressionNode::from(*expression.left)),
                Box::new(untyped::ExpressionNode::from(*expression.right)),
            ),
            pest::BinaryOperator::RightShift => untyped::Expression::RightShift(
                Box::new(untyped::ExpressionNode::from(*expression.left)),
                Box::new(untyped::ExpressionNode::from(*expression.right)),
            ),
            pest::BinaryOperator::BitAnd => untyped::Expression::BitAnd(
                Box::new(untyped::ExpressionNode::from(*expression.left)),
                Box::new(untyped::ExpressionNode::from(*expression.right)),
            ),
            pest::BinaryOperator::BitOr => untyped::Expression::BitOr(
                Box::new(untyped::ExpressionNode::from(*expression.left)),
                Box::new(untyped::ExpressionNode::from(*expression.right)),
            ),
            // rewrite (a != b)` as `!(a == b)`
            pest::BinaryOperator::NotEq => untyped::Expression::Not(Box::new(
                untyped::Expression::Eq(
                    Box::new(untyped::ExpressionNode::from(*expression.left)),
                    Box::new(untyped::ExpressionNode::from(*expression.right)),
                )
                .span(expression.span),
            )),
        }
        .span(expression.span)
    }
}

impl<'ast> From<pest::IfElseExpression<'ast>> for untyped::ExpressionNode<'ast> {
    fn from(expression: pest::IfElseExpression<'ast>) -> untyped::ExpressionNode<'ast> {
        use crate::untyped::NodeValue;
        untyped::Expression::Conditional(Box::new(ConditionalExpression {
            condition: Box::new(untyped::ExpressionNode::from(*expression.condition)),
            consequence_statements: expression
                .consequence_statements
                .into_iter()
                .map(untyped::StatementNode::from)
                .collect(),
            consequence: Box::new(untyped::ExpressionNode::from(*expression.consequence)),
            alternative_statements: expression
                .alternative_statements
                .into_iter()
                .map(untyped::StatementNode::from)
                .collect(),
            alternative: Box::new(untyped::ExpressionNode::from(*expression.alternative)),
            kind: untyped::ConditionalKind::IfElse,
        }))
        .span(expression.span)
    }
}

impl<'ast> From<pest::TernaryExpression<'ast>> for untyped::ExpressionNode<'ast> {
    fn from(expression: pest::TernaryExpression<'ast>) -> untyped::ExpressionNode<'ast> {
        use crate::untyped::NodeValue;
        untyped::Expression::Conditional(Box::new(ConditionalExpression {
            condition: Box::new(untyped::ExpressionNode::from(*expression.condition)),
            consequence_statements: vec![],
            consequence: Box::new(untyped::ExpressionNode::from(*expression.consequence)),
            alternative_statements: vec![],
            alternative: Box::new(untyped::ExpressionNode::from(*expression.alternative)),
            kind: untyped::ConditionalKind::Ternary,
        }))
        .span(expression.span)
    }
}

impl<'ast> From<pest::Spread<'ast>> for untyped::SpreadNode<'ast> {
    fn from(spread: pest::Spread<'ast>) -> untyped::SpreadNode<'ast> {
        use crate::untyped::NodeValue;
        untyped::Spread {
            expression: untyped::ExpressionNode::from(spread.expression),
        }
        .span(spread.span)
    }
}

impl<'ast> From<pest::Range<'ast>> for untyped::RangeNode<'ast> {
    fn from(range: pest::Range<'ast>) -> untyped::RangeNode<'ast> {
        use crate::untyped::NodeValue;

        let from = range.from.map(|e| untyped::ExpressionNode::from(e.0));

        let to = range.to.map(|e| untyped::ExpressionNode::from(e.0));

        untyped::Range { from, to }.span(range.span)
    }
}

impl<'ast> From<pest::RangeOrExpression<'ast>> for untyped::RangeOrExpression<'ast> {
    fn from(
        range_or_expression: pest::RangeOrExpression<'ast>,
    ) -> untyped::RangeOrExpression<'ast> {
        match range_or_expression {
            pest::RangeOrExpression::Expression(e) => {
                untyped::RangeOrExpression::Expression(untyped::ExpressionNode::from(e))
            }
            pest::RangeOrExpression::Range(r) => {
                untyped::RangeOrExpression::Range(untyped::RangeNode::from(r))
            }
        }
    }
}

impl<'ast> From<pest::SpreadOrExpression<'ast>> for untyped::SpreadOrExpression<'ast> {
    fn from(
        spread_or_expression: pest::SpreadOrExpression<'ast>,
    ) -> untyped::SpreadOrExpression<'ast> {
        match spread_or_expression {
            pest::SpreadOrExpression::Expression(e) => {
                untyped::SpreadOrExpression::Expression(untyped::ExpressionNode::from(e))
            }
            pest::SpreadOrExpression::Spread(s) => {
                untyped::SpreadOrExpression::Spread(untyped::SpreadNode::from(s))
            }
        }
    }
}

impl<'ast> From<pest::InlineArrayExpression<'ast>> for untyped::ExpressionNode<'ast> {
    fn from(array: pest::InlineArrayExpression<'ast>) -> untyped::ExpressionNode<'ast> {
        use crate::untyped::NodeValue;
        untyped::Expression::InlineArray(
            array
                .expressions
                .into_iter()
                .map(untyped::SpreadOrExpression::from)
                .collect(),
        )
        .span(array.span)
    }
}

impl<'ast> From<pest::InlineTupleExpression<'ast>> for untyped::ExpressionNode<'ast> {
    fn from(tuple: pest::InlineTupleExpression<'ast>) -> untyped::ExpressionNode<'ast> {
        use crate::untyped::NodeValue;
        untyped::Expression::InlineTuple(
            tuple
                .elements
                .into_iter()
                .map(untyped::ExpressionNode::from)
                .collect(),
        )
        .span(tuple.span)
    }
}

impl<'ast> From<pest::InlineStructExpression<'ast>> for untyped::ExpressionNode<'ast> {
    fn from(s: pest::InlineStructExpression<'ast>) -> untyped::ExpressionNode<'ast> {
        use crate::untyped::NodeValue;
        untyped::Expression::InlineStruct(
            s.ty.span.as_str().to_string(),
            s.members
                .into_iter()
                .map(|member| {
                    (
                        member.id.span.as_str(),
                        untyped::ExpressionNode::from(member.expression),
                    )
                })
                .collect(),
        )
        .span(s.span)
    }
}

impl<'ast> From<pest::ArrayInitializerExpression<'ast>> for untyped::ExpressionNode<'ast> {
    fn from(initializer: pest::ArrayInitializerExpression<'ast>) -> untyped::ExpressionNode<'ast> {
        use crate::untyped::NodeValue;

        let value = untyped::ExpressionNode::from(*initializer.value);
        let count = untyped::ExpressionNode::from(*initializer.count);
        untyped::Expression::ArrayInitializer(Box::new(value), Box::new(count))
            .span(initializer.span)
    }
}

impl<'ast> From<pest::UnaryExpression<'ast>> for untyped::ExpressionNode<'ast> {
    fn from(unary: pest::UnaryExpression<'ast>) -> untyped::ExpressionNode<'ast> {
        use crate::untyped::NodeValue;

        let expression = Box::new(untyped::ExpressionNode::from(*unary.expression));

        match unary.op {
            pest::UnaryOperator::Not(..) => untyped::Expression::Not(expression),
            pest::UnaryOperator::Neg(..) => untyped::Expression::Neg(expression),
            pest::UnaryOperator::Pos(..) => untyped::Expression::Pos(expression),
        }
        .span(unary.span)
    }
}

impl<'ast> From<pest::PostfixExpression<'ast>> for untyped::ExpressionNode<'ast> {
    fn from(expression: pest::PostfixExpression<'ast>) -> untyped::ExpressionNode<'ast> {
        use crate::untyped::NodeValue;

        let base = untyped::ExpressionNode::from(*expression.base);

        // pest::PostFixExpression contains an array of "accesses": `a(34)[42]` is represented as `[a, [Call(34), Select(42)]]`, but untyped::ExpressionNode
        // is recursive, so it is `Select(Call(a, 34), 42)`. We apply this transformation here
        // we start with the base, and we fold the array of accesses by wrapping the current value
        expression
            .accesses
            .into_iter()
            .fold(base, |acc, a| match a {
                pest::Access::Call(a) => untyped::Expression::FunctionCall(
                    Box::new(acc),
                    a.explicit_generics.map(|explicit_generics| {
                        explicit_generics
                            .values
                            .into_iter()
                            .map(|i| match i {
                                pest::ConstantGenericValue::Underscore(_) => None,
                                pest::ConstantGenericValue::Value(v) => {
                                    Some(untyped::ExpressionNode::from(v))
                                }
                                pest::ConstantGenericValue::Identifier(i) => Some(
                                    untyped::Expression::Identifier(i.span.as_str()).span(i.span),
                                ),
                            })
                            .collect()
                    }),
                    a.arguments
                        .expressions
                        .into_iter()
                        .map(untyped::ExpressionNode::from)
                        .collect(),
                )
                .span(a.span),
                pest::Access::Select(a) => untyped::Expression::Select(
                    Box::new(acc),
                    Box::new(untyped::RangeOrExpression::from(a.expression)),
                )
                .span(a.span),
                pest::Access::Dot(m) => match m.inner {
                    pest::IdentifierOrDecimal::Identifier(id) => {
                        untyped::Expression::Member(Box::new(acc), Box::new(id.span.as_str()))
                            .span(m.span)
                    }
                    pest::IdentifierOrDecimal::Decimal(id) => untyped::Expression::Element(
                        Box::new(acc),
                        id.span.as_str().parse().unwrap(),
                    )
                    .span(m.span),
                },
            })
    }
}

impl<'ast> From<pest::DecimalLiteralExpression<'ast>> for untyped::ExpressionNode<'ast> {
    fn from(expression: pest::DecimalLiteralExpression<'ast>) -> untyped::ExpressionNode<'ast> {
        use crate::untyped::NodeValue;

        match expression.suffix {
            Some(suffix) => match suffix {
                pest::DecimalSuffix::Field(_) => untyped::Expression::FieldConstant(
                    BigUint::parse_bytes(expression.value.span.as_str().as_bytes(), 10).unwrap(),
                ),
                pest::DecimalSuffix::U64(_) => untyped::Expression::U64Constant(
                    expression.value.span.as_str().parse().unwrap(),
                ),
                pest::DecimalSuffix::U32(_) => untyped::Expression::U32Constant(
                    expression.value.span.as_str().parse().unwrap(),
                ),
                pest::DecimalSuffix::U16(_) => untyped::Expression::U16Constant(
                    expression.value.span.as_str().parse().unwrap(),
                ),
                pest::DecimalSuffix::U8(_) => {
                    untyped::Expression::U8Constant(expression.value.span.as_str().parse().unwrap())
                }
            }
            .span(expression.span),
            None => untyped::Expression::IntConstant(
                BigUint::parse_bytes(expression.value.span.as_str().as_bytes(), 10).unwrap(),
            )
            .span(expression.span),
        }
    }
}

impl<'ast> From<pest::HexLiteralExpression<'ast>> for untyped::ExpressionNode<'ast> {
    fn from(expression: pest::HexLiteralExpression<'ast>) -> untyped::ExpressionNode<'ast> {
        use crate::untyped::NodeValue;

        match expression.value {
            pest::HexNumberExpression::U64(e) => {
                untyped::Expression::U64Constant(u64::from_str_radix(e.span.as_str(), 16).unwrap())
            }
            pest::HexNumberExpression::U32(e) => {
                untyped::Expression::U32Constant(u32::from_str_radix(e.span.as_str(), 16).unwrap())
            }
            pest::HexNumberExpression::U16(e) => {
                untyped::Expression::U16Constant(u16::from_str_radix(e.span.as_str(), 16).unwrap())
            }
            pest::HexNumberExpression::U8(e) => {
                untyped::Expression::U8Constant(u8::from_str_radix(e.span.as_str(), 16).unwrap())
            }
        }
        .span(expression.span)
    }
}

impl<'ast> From<pest::LiteralExpression<'ast>> for untyped::ExpressionNode<'ast> {
    fn from(expression: pest::LiteralExpression<'ast>) -> untyped::ExpressionNode<'ast> {
        use crate::untyped::NodeValue;

        match expression {
            pest::LiteralExpression::BooleanLiteral(c) => {
                untyped::Expression::BooleanConstant(c.value.parse().unwrap()).span(c.span)
            }
            pest::LiteralExpression::DecimalLiteral(n) => untyped::ExpressionNode::from(n),
            pest::LiteralExpression::HexLiteral(n) => untyped::ExpressionNode::from(n),
        }
    }
}

impl<'ast> From<pest::IdentifierExpression<'ast>> for untyped::ExpressionNode<'ast> {
    fn from(expression: pest::IdentifierExpression<'ast>) -> untyped::ExpressionNode<'ast> {
        use crate::untyped::NodeValue;
        untyped::Expression::Identifier(expression.span.as_str()).span(expression.span)
    }
}

impl<'ast> From<pest::IdentifierExpression<'ast>> for untyped::AssigneeNode<'ast> {
    fn from(expression: pest::IdentifierExpression<'ast>) -> untyped::AssigneeNode<'ast> {
        use crate::untyped::NodeValue;

        untyped::Assignee::Identifier(expression.span.as_str()).span(expression.span)
    }
}

impl<'ast> From<pest::Assignee<'ast>> for untyped::AssigneeNode<'ast> {
    fn from(assignee: pest::Assignee<'ast>) -> untyped::AssigneeNode<'ast> {
        use crate::untyped::NodeValue;

        let a = untyped::AssigneeNode::from(assignee.id);
        let span = assignee.span;

        assignee.accesses.into_iter().fold(a, |acc, s| {
            match s {
                pest::AssigneeAccess::Select(s) => untyped::Assignee::Select(
                    Box::new(acc),
                    Box::new(untyped::RangeOrExpression::from(s.expression)),
                ),
                pest::AssigneeAccess::Dot(a) => match a.inner {
                    pest::IdentifierOrDecimal::Identifier(id) => {
                        untyped::Assignee::Member(Box::new(acc), Box::new(id.span.as_str()))
                    }
                    pest::IdentifierOrDecimal::Decimal(id) => {
                        untyped::Assignee::Element(Box::new(acc), id.span.as_str().parse().unwrap())
                    }
                },
            }
            .span(span)
        })
    }
}

impl<'ast> From<pest::Type<'ast>> for untyped::UnresolvedTypeNode<'ast> {
    fn from(t: pest::Type<'ast>) -> untyped::UnresolvedTypeNode<'ast> {
        use crate::untyped::types::UnresolvedType;
        use crate::untyped::NodeValue;

        match t {
            pest::Type::Basic(t) => match t {
                pest::BasicType::Field(t) => UnresolvedType::FieldElement.span(t.span),
                pest::BasicType::Boolean(t) => UnresolvedType::Boolean.span(t.span),
                pest::BasicType::U8(t) => UnresolvedType::Uint(8).span(t.span),
                pest::BasicType::U16(t) => UnresolvedType::Uint(16).span(t.span),
                pest::BasicType::U32(t) => UnresolvedType::Uint(32).span(t.span),
                pest::BasicType::U64(t) => UnresolvedType::Uint(64).span(t.span),
            },
            pest::Type::Array(t) => {
                let inner_type = match t.ty {
                    pest::BasicOrStructOrTupleType::Basic(t) => match t {
                        pest::BasicType::Field(t) => UnresolvedType::FieldElement.span(t.span),
                        pest::BasicType::Boolean(t) => UnresolvedType::Boolean.span(t.span),
                        pest::BasicType::U8(t) => UnresolvedType::Uint(8).span(t.span),
                        pest::BasicType::U16(t) => UnresolvedType::Uint(16).span(t.span),
                        pest::BasicType::U32(t) => UnresolvedType::Uint(32).span(t.span),
                        pest::BasicType::U64(t) => UnresolvedType::Uint(64).span(t.span),
                    },
                    pest::BasicOrStructOrTupleType::Struct(t) => UnresolvedType::User(
                        t.id.span.as_str().to_string(),
                        t.explicit_generics.map(|explicit_generics| {
                            explicit_generics
                                .values
                                .into_iter()
                                .map(|i| match i {
                                    pest::ConstantGenericValue::Underscore(_) => None,
                                    pest::ConstantGenericValue::Value(v) => {
                                        Some(untyped::ExpressionNode::from(v))
                                    }
                                    pest::ConstantGenericValue::Identifier(i) => Some(
                                        untyped::Expression::Identifier(i.span.as_str())
                                            .span(i.span),
                                    ),
                                })
                                .collect()
                        }),
                    )
                    .span(t.span),
                    pest::BasicOrStructOrTupleType::Tuple(t) => UnresolvedType::Tuple(
                        t.elements
                            .into_iter()
                            .map(untyped::UnresolvedTypeNode::from)
                            .collect(),
                    )
                    .span(t.span),
                };

                let span = t.span;

                t.dimensions
                    .into_iter()
                    .map(untyped::ExpressionNode::from)
                    .rev()
                    .fold(None, |acc, s| match acc {
                        None => Some(UnresolvedType::array(inner_type.clone(), s)),
                        Some(acc) => Some(UnresolvedType::array(acc.span(span), s)),
                    })
                    .unwrap()
                    .span(span)
            }
            pest::Type::Struct(s) => UnresolvedType::User(
                s.id.span.as_str().to_string(),
                s.explicit_generics.map(|explicit_generics| {
                    explicit_generics
                        .values
                        .into_iter()
                        .map(|i| match i {
                            pest::ConstantGenericValue::Underscore(_) => None,
                            pest::ConstantGenericValue::Value(v) => {
                                Some(untyped::ExpressionNode::from(v))
                            }
                            pest::ConstantGenericValue::Identifier(i) => {
                                Some(untyped::Expression::Identifier(i.span.as_str()).span(i.span))
                            }
                        })
                        .collect()
                }),
            )
            .span(s.span),
            pest::Type::Tuple(t) => UnresolvedType::Tuple(
                t.elements
                    .into_iter()
                    .map(untyped::UnresolvedTypeNode::from)
                    .collect(),
            )
            .span(t.span),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::untyped::types::{UnresolvedSignature, UnresolvedType};
    use crate::untyped::NodeValue;

    #[test]
    fn return_forty_two() {
        let source = "def main() -> field { return 42; }";
        let ast = pest::generate_ast(source).unwrap();
        let expected: untyped::Module = untyped::Module {
            symbols: vec![untyped::SymbolDeclaration {
                id: &source[4..8],
                symbol: untyped::Symbol::Here(untyped::SymbolDefinition::Function(
                    untyped::Function {
                        arguments: vec![],
                        statements: vec![untyped::Statement::Return(Some(
                            untyped::Expression::IntConstant(42usize.into()).into(),
                        ))
                        .into()],
                        signature: UnresolvedSignature::new()
                            .inputs(vec![])
                            .output(UnresolvedType::FieldElement.mock()),
                    }
                    .into(),
                )),
            }
            .into()],
        };
        assert_eq!(untyped::Module::from(ast), expected);
    }

    #[test]
    fn return_true() {
        let source = "def main() -> bool { return true; }";
        let ast = pest::generate_ast(source).unwrap();
        let expected: untyped::Module = untyped::Module {
            symbols: vec![untyped::SymbolDeclaration {
                id: &source[4..8],
                symbol: untyped::Symbol::Here(untyped::SymbolDefinition::Function(
                    untyped::Function {
                        arguments: vec![],
                        statements: vec![untyped::Statement::Return(Some(
                            untyped::Expression::BooleanConstant(true).into(),
                        ))
                        .into()],
                        signature: UnresolvedSignature::new()
                            .inputs(vec![])
                            .output(UnresolvedType::Boolean.mock()),
                    }
                    .into(),
                )),
            }
            .into()],
        };
        assert_eq!(untyped::Module::from(ast), expected);
    }

    #[test]
    fn arguments() {
        let source = "def main(private field a, bool mut b) -> field { return 42; }";
        let ast = pest::generate_ast(source).unwrap();

        let expected: untyped::Module = untyped::Module {
            symbols: vec![untyped::SymbolDeclaration {
                id: &source[4..8],
                symbol: untyped::Symbol::Here(untyped::SymbolDefinition::Function(
                    untyped::Function {
                        arguments: vec![
                            untyped::Parameter::private(
                                untyped::Variable::immutable(
                                    "a",
                                    UnresolvedType::FieldElement.mock(),
                                )
                                .into(),
                            )
                            .into(),
                            untyped::Parameter::new(
                                untyped::Variable::mutable("b", UnresolvedType::Boolean.mock())
                                    .mock(),
                                None,
                            )
                            .into(),
                        ],
                        statements: vec![untyped::Statement::Return(Some(
                            untyped::Expression::IntConstant(42usize.into()).into(),
                        ))
                        .into()],
                        signature: UnresolvedSignature::new()
                            .inputs(vec![
                                UnresolvedType::FieldElement.mock(),
                                UnresolvedType::Boolean.mock(),
                            ])
                            .output(UnresolvedType::FieldElement.mock()),
                    }
                    .into(),
                )),
            }
            .into()],
        };

        assert_eq!(untyped::Module::from(ast), expected);
    }

    mod types {
        use super::*;

        /// Helper method to generate the ast for `def main(private {ty} a) { return; }` which we use to check ty
        fn wrap(ty: UnresolvedType<'static>) -> untyped::Module<'static> {
            untyped::Module {
                symbols: vec![untyped::SymbolDeclaration {
                    id: "main",
                    symbol: untyped::Symbol::Here(untyped::SymbolDefinition::Function(
                        untyped::Function {
                            arguments: vec![untyped::Parameter::private(
                                untyped::Variable::new("a", ty.clone().mock(), false).into(),
                            )
                            .into()],
                            statements: vec![untyped::Statement::Return(None).into()],
                            signature: UnresolvedSignature::new().inputs(vec![ty.mock()]),
                        }
                        .into(),
                    )),
                }
                .into()],
            }
        }

        #[test]
        fn array() {
            let vectors = vec![
                ("field", UnresolvedType::FieldElement),
                ("bool", UnresolvedType::Boolean),
                (
                    "field[2]",
                    untyped::UnresolvedType::Array(
                        Box::new(untyped::UnresolvedType::FieldElement.mock()),
                        untyped::Expression::IntConstant(2usize.into()).mock(),
                    ),
                ),
                (
                    "field[2][3]",
                    untyped::UnresolvedType::Array(
                        Box::new(
                            untyped::UnresolvedType::Array(
                                Box::new(untyped::UnresolvedType::FieldElement.mock()),
                                untyped::Expression::IntConstant(3usize.into()).mock(),
                            )
                            .mock(),
                        ),
                        untyped::Expression::IntConstant(2usize.into()).mock(),
                    ),
                ),
                (
                    "bool[2][3u32]",
                    untyped::UnresolvedType::Array(
                        Box::new(
                            untyped::UnresolvedType::Array(
                                Box::new(untyped::UnresolvedType::Boolean.mock()),
                                untyped::Expression::U32Constant(3u32).mock(),
                            )
                            .mock(),
                        ),
                        untyped::Expression::IntConstant(2usize.into()).mock(),
                    ),
                ),
            ];

            for (ty, expected) in vectors {
                let source = format!("def main(private {} a) {{ return; }}", ty);
                let expected = wrap(expected);
                let ast = pest::generate_ast(&source).unwrap();
                assert_eq!(untyped::Module::from(ast), expected);
            }
        }
    }

    mod postfix {
        use super::*;
        fn wrap(expression: untyped::Expression<'static>) -> untyped::Module {
            untyped::Module {
                symbols: vec![untyped::SymbolDeclaration {
                    id: "main",
                    symbol: untyped::Symbol::Here(untyped::SymbolDefinition::Function(
                        untyped::Function {
                            arguments: vec![],
                            statements: vec![
                                untyped::Statement::Return(Some(expression.into())).into()
                            ],
                            signature: UnresolvedSignature::new(),
                        }
                        .into(),
                    )),
                }
                .into()],
            }
        }

        #[test]
        fn success() {
            // we basically accept `()?[]*` : an optional call at first, then only array accesses

            let vectors = vec![
                ("a", untyped::Expression::Identifier("a")),
                (
                    "a[3]",
                    untyped::Expression::Select(
                        Box::new(untyped::Expression::Identifier("a").into()),
                        Box::new(untyped::RangeOrExpression::Expression(
                            untyped::Expression::IntConstant(3usize.into()).into(),
                        ),
                    )),
                ),
                (
                    "a[3][4]",
                    untyped::Expression::Select(
                        Box::new(untyped::Expression::Select(
                            Box::new(untyped::Expression::Identifier("a").into()),
                            Box::new(untyped::RangeOrExpression::Expression(
                                untyped::Expression::IntConstant(3usize.into()).into(),
                            )),
                        )
                        .into()),
                        Box::new(untyped::RangeOrExpression::Expression(
                            untyped::Expression::IntConstant(4usize.into()).into(),
                        )),
                    ),
                ),
                (
                    "a(3)[4]",
                    untyped::Expression::Select(
                        Box::new(untyped::Expression::FunctionCall(
                            Box::new(untyped::Expression::Identifier("a").mock()),
                            None,
                            vec![untyped::Expression::IntConstant(3usize.into()).into()],
                        )
                        .into()),
                        Box::new(untyped::RangeOrExpression::Expression(
                            untyped::Expression::IntConstant(4usize.into()).into(),
                        )),
                    ),
                ),
                (
                    "a(3)[4][5]",
                    untyped::Expression::Select(
                        Box::new(untyped::Expression::Select(
                            Box::new(untyped::Expression::FunctionCall(
                                Box::new(untyped::Expression::Identifier("a").mock()),
                                None,
                                vec![untyped::Expression::IntConstant(3usize.into()).into()],
                            )
                            .into()),
                            Box::new(untyped::RangeOrExpression::Expression(
                                untyped::Expression::IntConstant(4usize.into()).into(),
                            )),
                        )
                        .into()),
                        Box::new(untyped::RangeOrExpression::Expression(
                            untyped::Expression::IntConstant(5usize.into()).into(),
                        )),
                    ),
                ),
            ];

            for (source, expected) in vectors {
                let source = format!("def main() {{ return {}; }}", source);
                let expected = wrap(expected);
                let ast = pest::generate_ast(&source).unwrap();
                assert_eq!(untyped::Module::from(ast), expected);
            }
        }

        #[test]
        fn call_array_element() {
            // a call after an array access should be accepted
            let source = "def main() { return a[2](3); }";
            let ast = pest::generate_ast(source).unwrap();
            assert_eq!(
                untyped::Module::from(ast),
                wrap(untyped::Expression::FunctionCall(
                    Box::new(
                        untyped::Expression::Select(
                            Box::new(untyped::Expression::Identifier("a").mock()),
                            Box::new(untyped::RangeOrExpression::Expression(
                                untyped::Expression::IntConstant(2u32.into()).mock()
                            ))
                        )
                        .mock()
                    ),
                    None,
                    vec![untyped::Expression::IntConstant(3u32.into()).mock()],
                ))
            );
        }

        #[test]
        fn call_call_result() {
            // a call after a call should be accepted
            let source = "def main() { return a(2)(3); }";

            let ast = pest::generate_ast(source).unwrap();
            assert_eq!(
                untyped::Module::from(ast),
                wrap(untyped::Expression::FunctionCall(
                    Box::new(
                        untyped::Expression::FunctionCall(
                            Box::new(untyped::Expression::Identifier("a").mock()),
                            None,
                            vec![untyped::Expression::IntConstant(2u32.into()).mock()]
                        )
                        .mock()
                    ),
                    None,
                    vec![untyped::Expression::IntConstant(3u32.into()).mock()],
                ))
            );
        }
    }
    #[test]
    fn declarations() {
        use self::pest::Span;

        let span = Span::new("", 0, 0).unwrap();

        // Case 1: `id = expr`
        // A simple assignment to an already defined variable

        let definition = pest::DefinitionStatement {
            lhs: pest::TypedIdentifierOrAssignee::Assignee(pest::Assignee {
                id: pest::IdentifierExpression {
                    value: String::from("a"),
                    span,
                },
                accesses: vec![],
                span,
            }),
            expression: pest::Expression::Literal(pest::LiteralExpression::DecimalLiteral(
                pest::DecimalLiteralExpression {
                    value: pest::DecimalNumber {
                        span: Span::new("1", 0, 1).unwrap(),
                    },
                    suffix: None,
                    span,
                },
            )),
            span,
        };

        let statement = untyped::StatementNode::from(definition);

        match statement.value {
            untyped::Statement::Assignment(..) => {}
            s => {
                panic!("should be an Assignment, found {}", s);
            }
        };

        // Case 2: `type id = expr`
        // A definition statement is generated

        let definition = pest::DefinitionStatement {
            lhs: pest::TypedIdentifierOrAssignee::TypedIdentifier(pest::TypedIdentifier {
                ty: pest::Type::Basic(pest::BasicType::Field(pest::FieldType { span })),
                identifier: pest::IdentifierExpression {
                    value: String::from("a"),
                    span,
                },
                mutable: None,
                span,
            }),
            expression: pest::Expression::Postfix(pest::PostfixExpression {
                base: Box::new(pest::Expression::Identifier(pest::IdentifierExpression {
                    value: String::from("foo"),
                    span,
                })),
                accesses: vec![pest::Access::Call(pest::CallAccess {
                    explicit_generics: None,
                    arguments: pest::Arguments {
                        expressions: vec![],
                        span,
                    },
                    span,
                })],
                span,
            }),
            span,
        };

        let statement = untyped::StatementNode::from(definition);

        match statement.value {
            untyped::Statement::Definition(..) => {}
            s => {
                panic!("should be a Definition, found {}", s);
            }
        };
    }
}
