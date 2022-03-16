use crate::absy;

use crate::absy::SymbolDefinition;
use num_bigint::BigUint;
use std::path::Path;
use zokrates_pest_ast as pest;

impl<'ast> From<pest::File<'ast>> for absy::Module<'ast> {
    fn from(file: pest::File<'ast>) -> absy::Module<'ast> {
        absy::Module::with_symbols(file.declarations.into_iter().flat_map(|d| match d {
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
) -> Vec<absy::SymbolDeclarationNode> {
    use crate::absy::NodeValue;

    match import {
        pest::ImportDirective::Main(import) => {
            let span = import.span;
            let source = Path::new(import.source.span.as_str());
            let id = "main";
            let alias = import.alias.map(|a| a.span.as_str());

            let import = absy::CanonicalImport {
                source,
                id: absy::SymbolIdentifier::from(id).alias(alias),
            }
            .span(span.clone());

            vec![absy::SymbolDeclaration {
                id: alias.unwrap_or(id),
                symbol: absy::Symbol::Here(absy::SymbolDefinition::Import(import)),
            }
            .span(span.clone())]
        }
        pest::ImportDirective::From(import) => {
            let span = import.span;
            let source = Path::new(import.source.span.as_str());
            import
                .symbols
                .into_iter()
                .map(|symbol| {
                    let alias = symbol
                        .alias
                        .as_ref()
                        .map(|a| a.span.as_str())
                        .unwrap_or_else(|| symbol.id.span.as_str());

                    let import = absy::CanonicalImport {
                        source,
                        id: absy::SymbolIdentifier::from(symbol.id.span.as_str())
                            .alias(Some(alias)),
                    }
                    .span(span.clone());

                    absy::SymbolDeclaration {
                        id: alias,
                        symbol: absy::Symbol::Here(absy::SymbolDefinition::Import(import)),
                    }
                    .span(span.clone())
                })
                .collect()
        }
    }
}

impl<'ast> From<pest::StructDefinition<'ast>> for absy::SymbolDeclarationNode<'ast> {
    fn from(definition: pest::StructDefinition<'ast>) -> absy::SymbolDeclarationNode<'ast> {
        use crate::absy::NodeValue;

        let span = definition.span;

        let id = definition.id.span.as_str();

        let ty = absy::StructDefinition {
            generics: definition
                .generics
                .into_iter()
                .map(absy::ConstantGenericNode::from)
                .collect(),
            fields: definition
                .fields
                .into_iter()
                .map(absy::StructDefinitionFieldNode::from)
                .collect(),
        }
        .span(span.clone());

        absy::SymbolDeclaration {
            id,
            symbol: absy::Symbol::Here(absy::SymbolDefinition::Struct(ty)),
        }
        .span(span)
    }
}

impl<'ast> From<pest::StructField<'ast>> for absy::StructDefinitionFieldNode<'ast> {
    fn from(field: pest::StructField<'ast>) -> absy::StructDefinitionFieldNode<'ast> {
        use crate::absy::NodeValue;

        let span = field.span;

        let id = field.id.span.as_str();

        let ty = absy::UnresolvedTypeNode::from(field.ty);

        absy::StructDefinitionField { id, ty }.span(span)
    }
}

impl<'ast> From<pest::ConstantDefinition<'ast>> for absy::SymbolDeclarationNode<'ast> {
    fn from(definition: pest::ConstantDefinition<'ast>) -> absy::SymbolDeclarationNode<'ast> {
        use crate::absy::NodeValue;

        let span = definition.span;
        let id = definition.id.span.as_str();

        let ty = absy::ConstantDefinition {
            ty: definition.ty.into(),
            expression: definition.expression.into(),
        }
        .span(span.clone());

        absy::SymbolDeclaration {
            id,
            symbol: absy::Symbol::Here(absy::SymbolDefinition::Constant(ty)),
        }
        .span(span)
    }
}

impl<'ast> From<pest::TypeDefinition<'ast>> for absy::SymbolDeclarationNode<'ast> {
    fn from(definition: pest::TypeDefinition<'ast>) -> absy::SymbolDeclarationNode<'ast> {
        use crate::absy::NodeValue;

        let span = definition.span;
        let id = definition.id.span.as_str();

        let ty = absy::TypeDefinition {
            generics: definition
                .generics
                .into_iter()
                .map(absy::ConstantGenericNode::from)
                .collect(),
            ty: definition.ty.into(),
        }
        .span(span.clone());

        absy::SymbolDeclaration {
            id,
            symbol: absy::Symbol::Here(SymbolDefinition::Type(ty)),
        }
        .span(span)
    }
}

impl<'ast> From<pest::FunctionDefinition<'ast>> for absy::SymbolDeclarationNode<'ast> {
    fn from(function: pest::FunctionDefinition<'ast>) -> absy::SymbolDeclarationNode<'ast> {
        use crate::absy::NodeValue;

        let span = function.span;

        let signature = absy::UnresolvedSignature::new()
            .generics(
                function
                    .generics
                    .into_iter()
                    .map(absy::ConstantGenericNode::from)
                    .collect(),
            )
            .inputs(
                function
                    .parameters
                    .clone()
                    .into_iter()
                    .map(|p| absy::UnresolvedTypeNode::from(p.ty))
                    .collect(),
            )
            .outputs(
                function
                    .returns
                    .clone()
                    .into_iter()
                    .map(absy::UnresolvedTypeNode::from)
                    .collect(),
            );

        let id = function.id.span.as_str();

        let function = absy::Function {
            arguments: function
                .parameters
                .into_iter()
                .map(absy::ParameterNode::from)
                .collect(),
            statements: function
                .statements
                .into_iter()
                .flat_map(statements_from_statement)
                .collect(),
            signature,
        }
        .span(span.clone());

        absy::SymbolDeclaration {
            id,
            symbol: absy::Symbol::Here(absy::SymbolDefinition::Function(function)),
        }
        .span(span)
    }
}

impl<'ast> From<pest::IdentifierExpression<'ast>> for absy::ConstantGenericNode<'ast> {
    fn from(g: pest::IdentifierExpression<'ast>) -> absy::ConstantGenericNode<'ast> {
        use absy::NodeValue;

        let name = g.span.as_str();

        name.span(g.span)
    }
}

impl<'ast> From<pest::Parameter<'ast>> for absy::ParameterNode<'ast> {
    fn from(param: pest::Parameter<'ast>) -> absy::ParameterNode<'ast> {
        use crate::absy::NodeValue;

        let private = param
            .visibility
            .map(|v| match v {
                pest::Visibility::Private(_) => true,
                pest::Visibility::Public(_) => false,
            })
            .unwrap_or(false);

        let variable = absy::Variable::new(
            param.id.span.as_str(),
            absy::UnresolvedTypeNode::from(param.ty),
        )
        .span(param.id.span);

        absy::Parameter::new(variable, private).span(param.span)
    }
}

fn statements_from_statement(statement: pest::Statement) -> Vec<absy::StatementNode> {
    match statement {
        pest::Statement::Definition(s) => statements_from_definition(s),
        pest::Statement::Iteration(s) => vec![absy::StatementNode::from(s)],
        pest::Statement::Assertion(s) => vec![absy::StatementNode::from(s)],
        pest::Statement::Return(s) => vec![absy::StatementNode::from(s)],
    }
}

fn statements_from_definition(definition: pest::DefinitionStatement) -> Vec<absy::StatementNode> {
    use crate::absy::NodeValue;

    let lhs = definition.lhs;

    match lhs.len() {
        1 => {
            // Definition or assignment
            let a = lhs[0].clone();

            let e: absy::ExpressionNode = absy::ExpressionNode::from(definition.expression);

            match a {
                pest::TypedIdentifierOrAssignee::TypedIdentifier(i) => {
                    let declaration = absy::Statement::Declaration(
                        absy::Variable::new(
                            i.identifier.span.as_str(),
                            absy::UnresolvedTypeNode::from(i.ty),
                        )
                        .span(i.identifier.span.clone()),
                    )
                    .span(definition.span.clone());

                    let s = match e.value {
                        absy::Expression::FunctionCall(..) => absy::Statement::MultipleDefinition(
                            vec![absy::AssigneeNode::from(i.identifier.clone())],
                            e,
                        ),
                        _ => absy::Statement::Definition(
                            absy::AssigneeNode::from(i.identifier.clone()),
                            e,
                        ),
                    };

                    vec![declaration, s.span(definition.span)]
                }
                pest::TypedIdentifierOrAssignee::Assignee(a) => {
                    let s = match e.value {
                        absy::Expression::FunctionCall(..) => absy::Statement::MultipleDefinition(
                            vec![absy::AssigneeNode::from(a)],
                            e,
                        ),
                        _ => absy::Statement::Definition(absy::AssigneeNode::from(a), e),
                    };

                    vec![s.span(definition.span)]
                }
            }
        }
        _ => {
            // Multidefinition
            let declarations = lhs.clone().into_iter().filter_map(|i| match i {
                pest::TypedIdentifierOrAssignee::TypedIdentifier(i) => {
                    let ty = i.ty;
                    let id = i.identifier;

                    Some(
                        absy::Statement::Declaration(
                            absy::Variable::new(
                                id.span.as_str(),
                                absy::UnresolvedTypeNode::from(ty),
                            )
                            .span(id.span),
                        )
                        .span(i.span),
                    )
                }
                _ => None,
            });

            let lhs = lhs
                .into_iter()
                .map(|i| match i {
                    pest::TypedIdentifierOrAssignee::TypedIdentifier(i) => {
                        absy::Assignee::Identifier(i.identifier.span.as_str())
                            .span(i.identifier.span)
                    }
                    pest::TypedIdentifierOrAssignee::Assignee(a) => absy::AssigneeNode::from(a),
                })
                .collect();

            let multi_def = absy::Statement::MultipleDefinition(
                lhs,
                absy::ExpressionNode::from(definition.expression),
            )
            .span(definition.span);

            declarations.chain(std::iter::once(multi_def)).collect()
        }
    }
}

impl<'ast> From<pest::ReturnStatement<'ast>> for absy::StatementNode<'ast> {
    fn from(statement: pest::ReturnStatement<'ast>) -> absy::StatementNode<'ast> {
        use crate::absy::NodeValue;

        absy::Statement::Return(
            absy::ExpressionList {
                expressions: statement
                    .expressions
                    .into_iter()
                    .map(absy::ExpressionNode::from)
                    .collect(),
            }
            .span(statement.span.clone()),
        )
        .span(statement.span)
    }
}

impl<'ast> From<pest::AssertionStatement<'ast>> for absy::StatementNode<'ast> {
    fn from(statement: pest::AssertionStatement<'ast>) -> absy::StatementNode<'ast> {
        use crate::absy::NodeValue;

        absy::Statement::Assertion(
            absy::ExpressionNode::from(statement.expression),
            statement.message.map(|m| m.value),
        )
        .span(statement.span)
    }
}

impl<'ast> From<pest::IterationStatement<'ast>> for absy::StatementNode<'ast> {
    fn from(statement: pest::IterationStatement<'ast>) -> absy::StatementNode<'ast> {
        use crate::absy::NodeValue;
        let from = absy::ExpressionNode::from(statement.from);
        let to = absy::ExpressionNode::from(statement.to);
        let index = statement.index.span.as_str();
        let ty = absy::UnresolvedTypeNode::from(statement.ty);
        let statements: Vec<absy::StatementNode<'ast>> = statement
            .statements
            .into_iter()
            .flat_map(statements_from_statement)
            .collect();

        let var = absy::Variable::new(index, ty).span(statement.index.span);

        absy::Statement::For(var, from, to, statements).span(statement.span)
    }
}

impl<'ast> From<pest::Expression<'ast>> for absy::ExpressionNode<'ast> {
    fn from(expression: pest::Expression<'ast>) -> absy::ExpressionNode<'ast> {
        match expression {
            pest::Expression::Binary(e) => absy::ExpressionNode::from(e),
            pest::Expression::Ternary(e) => absy::ExpressionNode::from(e),
            pest::Expression::IfElse(e) => absy::ExpressionNode::from(e),
            pest::Expression::Literal(e) => absy::ExpressionNode::from(e),
            pest::Expression::Identifier(e) => absy::ExpressionNode::from(e),
            pest::Expression::Postfix(e) => absy::ExpressionNode::from(e),
            pest::Expression::InlineArray(e) => absy::ExpressionNode::from(e),
            pest::Expression::InlineTuple(e) => absy::ExpressionNode::from(e),
            pest::Expression::InlineStruct(e) => absy::ExpressionNode::from(e),
            pest::Expression::ArrayInitializer(e) => absy::ExpressionNode::from(e),
            pest::Expression::Unary(e) => absy::ExpressionNode::from(e),
        }
    }
}

impl<'ast> From<pest::BinaryExpression<'ast>> for absy::ExpressionNode<'ast> {
    fn from(expression: pest::BinaryExpression<'ast>) -> absy::ExpressionNode<'ast> {
        use crate::absy::NodeValue;
        match expression.op {
            pest::BinaryOperator::Add => absy::Expression::Add(
                box absy::ExpressionNode::from(*expression.left),
                box absy::ExpressionNode::from(*expression.right),
            ),
            pest::BinaryOperator::Sub => absy::Expression::Sub(
                box absy::ExpressionNode::from(*expression.left),
                box absy::ExpressionNode::from(*expression.right),
            ),
            pest::BinaryOperator::Mul => absy::Expression::Mult(
                box absy::ExpressionNode::from(*expression.left),
                box absy::ExpressionNode::from(*expression.right),
            ),
            pest::BinaryOperator::Div => absy::Expression::Div(
                box absy::ExpressionNode::from(*expression.left),
                box absy::ExpressionNode::from(*expression.right),
            ),
            pest::BinaryOperator::Rem => absy::Expression::Rem(
                box absy::ExpressionNode::from(*expression.left),
                box absy::ExpressionNode::from(*expression.right),
            ),
            pest::BinaryOperator::Eq => absy::Expression::Eq(
                box absy::ExpressionNode::from(*expression.left),
                box absy::ExpressionNode::from(*expression.right),
            ),
            pest::BinaryOperator::Lt => absy::Expression::Lt(
                box absy::ExpressionNode::from(*expression.left),
                box absy::ExpressionNode::from(*expression.right),
            ),
            pest::BinaryOperator::Lte => absy::Expression::Le(
                box absy::ExpressionNode::from(*expression.left),
                box absy::ExpressionNode::from(*expression.right),
            ),
            pest::BinaryOperator::Gt => absy::Expression::Gt(
                box absy::ExpressionNode::from(*expression.left),
                box absy::ExpressionNode::from(*expression.right),
            ),
            pest::BinaryOperator::Gte => absy::Expression::Ge(
                box absy::ExpressionNode::from(*expression.left),
                box absy::ExpressionNode::from(*expression.right),
            ),
            pest::BinaryOperator::And => absy::Expression::And(
                box absy::ExpressionNode::from(*expression.left),
                box absy::ExpressionNode::from(*expression.right),
            ),
            pest::BinaryOperator::Or => absy::Expression::Or(
                box absy::ExpressionNode::from(*expression.left),
                box absy::ExpressionNode::from(*expression.right),
            ),
            pest::BinaryOperator::Pow => absy::Expression::Pow(
                box absy::ExpressionNode::from(*expression.left),
                box absy::ExpressionNode::from(*expression.right),
            ),
            pest::BinaryOperator::BitXor => absy::Expression::BitXor(
                box absy::ExpressionNode::from(*expression.left),
                box absy::ExpressionNode::from(*expression.right),
            ),
            pest::BinaryOperator::LeftShift => absy::Expression::LeftShift(
                box absy::ExpressionNode::from(*expression.left),
                box absy::ExpressionNode::from(*expression.right),
            ),
            pest::BinaryOperator::RightShift => absy::Expression::RightShift(
                box absy::ExpressionNode::from(*expression.left),
                box absy::ExpressionNode::from(*expression.right),
            ),
            pest::BinaryOperator::BitAnd => absy::Expression::BitAnd(
                box absy::ExpressionNode::from(*expression.left),
                box absy::ExpressionNode::from(*expression.right),
            ),
            pest::BinaryOperator::BitOr => absy::Expression::BitOr(
                box absy::ExpressionNode::from(*expression.left),
                box absy::ExpressionNode::from(*expression.right),
            ),
            // rewrite (a != b)` as `!(a == b)`
            pest::BinaryOperator::NotEq => absy::Expression::Not(
                box absy::Expression::Eq(
                    box absy::ExpressionNode::from(*expression.left),
                    box absy::ExpressionNode::from(*expression.right),
                )
                .span(expression.span.clone()),
            ),
        }
        .span(expression.span)
    }
}

impl<'ast> From<pest::IfElseExpression<'ast>> for absy::ExpressionNode<'ast> {
    fn from(expression: pest::IfElseExpression<'ast>) -> absy::ExpressionNode<'ast> {
        use crate::absy::NodeValue;
        absy::Expression::Conditional(
            box absy::ExpressionNode::from(*expression.condition),
            box absy::ExpressionNode::from(*expression.consequence),
            box absy::ExpressionNode::from(*expression.alternative),
            absy::ConditionalKind::IfElse,
        )
        .span(expression.span)
    }
}

impl<'ast> From<pest::TernaryExpression<'ast>> for absy::ExpressionNode<'ast> {
    fn from(expression: pest::TernaryExpression<'ast>) -> absy::ExpressionNode<'ast> {
        use crate::absy::NodeValue;
        absy::Expression::Conditional(
            box absy::ExpressionNode::from(*expression.condition),
            box absy::ExpressionNode::from(*expression.consequence),
            box absy::ExpressionNode::from(*expression.alternative),
            absy::ConditionalKind::Ternary,
        )
        .span(expression.span)
    }
}

impl<'ast> From<pest::Spread<'ast>> for absy::SpreadNode<'ast> {
    fn from(spread: pest::Spread<'ast>) -> absy::SpreadNode<'ast> {
        use crate::absy::NodeValue;
        absy::Spread {
            expression: absy::ExpressionNode::from(spread.expression),
        }
        .span(spread.span)
    }
}

impl<'ast> From<pest::Range<'ast>> for absy::RangeNode<'ast> {
    fn from(range: pest::Range<'ast>) -> absy::RangeNode<'ast> {
        use crate::absy::NodeValue;

        let from = range.from.map(|e| absy::ExpressionNode::from(e.0));

        let to = range.to.map(|e| absy::ExpressionNode::from(e.0));

        absy::Range { from, to }.span(range.span)
    }
}

impl<'ast> From<pest::RangeOrExpression<'ast>> for absy::RangeOrExpression<'ast> {
    fn from(range_or_expression: pest::RangeOrExpression<'ast>) -> absy::RangeOrExpression<'ast> {
        match range_or_expression {
            pest::RangeOrExpression::Expression(e) => {
                absy::RangeOrExpression::Expression(absy::ExpressionNode::from(e))
            }
            pest::RangeOrExpression::Range(r) => {
                absy::RangeOrExpression::Range(absy::RangeNode::from(r))
            }
        }
    }
}

impl<'ast> From<pest::SpreadOrExpression<'ast>> for absy::SpreadOrExpression<'ast> {
    fn from(
        spread_or_expression: pest::SpreadOrExpression<'ast>,
    ) -> absy::SpreadOrExpression<'ast> {
        match spread_or_expression {
            pest::SpreadOrExpression::Expression(e) => {
                absy::SpreadOrExpression::Expression(absy::ExpressionNode::from(e))
            }
            pest::SpreadOrExpression::Spread(s) => {
                absy::SpreadOrExpression::Spread(absy::SpreadNode::from(s))
            }
        }
    }
}

impl<'ast> From<pest::InlineArrayExpression<'ast>> for absy::ExpressionNode<'ast> {
    fn from(array: pest::InlineArrayExpression<'ast>) -> absy::ExpressionNode<'ast> {
        use crate::absy::NodeValue;
        absy::Expression::InlineArray(
            array
                .expressions
                .into_iter()
                .map(absy::SpreadOrExpression::from)
                .collect(),
        )
        .span(array.span)
    }
}

impl<'ast> From<pest::InlineTupleExpression<'ast>> for absy::ExpressionNode<'ast> {
    fn from(tuple: pest::InlineTupleExpression<'ast>) -> absy::ExpressionNode<'ast> {
        use crate::absy::NodeValue;
        absy::Expression::InlineTuple(
            tuple
                .elements
                .into_iter()
                .map(absy::ExpressionNode::from)
                .collect(),
        )
        .span(tuple.span)
    }
}

impl<'ast> From<pest::InlineStructExpression<'ast>> for absy::ExpressionNode<'ast> {
    fn from(s: pest::InlineStructExpression<'ast>) -> absy::ExpressionNode<'ast> {
        use crate::absy::NodeValue;
        absy::Expression::InlineStruct(
            s.ty.span.as_str().to_string(),
            s.members
                .into_iter()
                .map(|member| {
                    (
                        member.id.span.as_str(),
                        absy::ExpressionNode::from(member.expression),
                    )
                })
                .collect(),
        )
        .span(s.span)
    }
}

impl<'ast> From<pest::ArrayInitializerExpression<'ast>> for absy::ExpressionNode<'ast> {
    fn from(initializer: pest::ArrayInitializerExpression<'ast>) -> absy::ExpressionNode<'ast> {
        use crate::absy::NodeValue;

        let value = absy::ExpressionNode::from(*initializer.value);
        let count = absy::ExpressionNode::from(*initializer.count);
        absy::Expression::ArrayInitializer(box value, box count).span(initializer.span)
    }
}

impl<'ast> From<pest::UnaryExpression<'ast>> for absy::ExpressionNode<'ast> {
    fn from(unary: pest::UnaryExpression<'ast>) -> absy::ExpressionNode<'ast> {
        use crate::absy::NodeValue;

        let expression = Box::new(absy::ExpressionNode::from(*unary.expression));

        match unary.op {
            pest::UnaryOperator::Not(..) => absy::Expression::Not(expression),
            pest::UnaryOperator::Neg(..) => absy::Expression::Neg(expression),
            pest::UnaryOperator::Pos(..) => absy::Expression::Pos(expression),
        }
        .span(unary.span)
    }
}

impl<'ast> From<pest::PostfixExpression<'ast>> for absy::ExpressionNode<'ast> {
    fn from(expression: pest::PostfixExpression<'ast>) -> absy::ExpressionNode<'ast> {
        use crate::absy::NodeValue;

        let base = absy::ExpressionNode::from(*expression.base);

        // pest::PostFixExpression contains an array of "accesses": `a(34)[42]` is represented as `[a, [Call(34), Select(42)]]`, but absy::ExpressionNode
        // is recursive, so it is `Select(Call(a, 34), 42)`. We apply this transformation here
        // we start with the base, and we fold the array of accesses by wrapping the current value
        expression
            .accesses
            .into_iter()
            .fold(base, |acc, a| match a {
                pest::Access::Call(a) => absy::Expression::FunctionCall(
                    Box::new(acc),
                    a.explicit_generics.map(|explicit_generics| {
                        explicit_generics
                            .values
                            .into_iter()
                            .map(|i| match i {
                                pest::ConstantGenericValue::Underscore(_) => None,
                                pest::ConstantGenericValue::Value(v) => {
                                    Some(absy::ExpressionNode::from(v))
                                }
                                pest::ConstantGenericValue::Identifier(i) => {
                                    Some(absy::Expression::Identifier(i.span.as_str()).span(i.span))
                                }
                            })
                            .collect()
                    }),
                    a.arguments
                        .expressions
                        .into_iter()
                        .map(absy::ExpressionNode::from)
                        .collect(),
                )
                .span(a.span),
                pest::Access::Select(a) => absy::Expression::Select(
                    box acc,
                    box absy::RangeOrExpression::from(a.expression),
                )
                .span(a.span),
                pest::Access::Dot(m) => match m.inner {
                    pest::IdentifierOrDecimal::Identifier(id) => {
                        absy::Expression::Member(box acc, box id.span.as_str()).span(m.span)
                    }
                    pest::IdentifierOrDecimal::Decimal(id) => {
                        absy::Expression::Element(box acc, id.span.as_str().parse().unwrap())
                            .span(m.span)
                    }
                },
            })
    }
}

impl<'ast> From<pest::DecimalLiteralExpression<'ast>> for absy::ExpressionNode<'ast> {
    fn from(expression: pest::DecimalLiteralExpression<'ast>) -> absy::ExpressionNode<'ast> {
        use crate::absy::NodeValue;

        match expression.suffix {
            Some(suffix) => match suffix {
                pest::DecimalSuffix::Field(_) => absy::Expression::FieldConstant(
                    BigUint::parse_bytes(expression.value.span.as_str().as_bytes(), 10).unwrap(),
                ),
                pest::DecimalSuffix::U64(_) => {
                    absy::Expression::U64Constant(expression.value.span.as_str().parse().unwrap())
                }
                pest::DecimalSuffix::U32(_) => {
                    absy::Expression::U32Constant(expression.value.span.as_str().parse().unwrap())
                }
                pest::DecimalSuffix::U16(_) => {
                    absy::Expression::U16Constant(expression.value.span.as_str().parse().unwrap())
                }
                pest::DecimalSuffix::U8(_) => {
                    absy::Expression::U8Constant(expression.value.span.as_str().parse().unwrap())
                }
            }
            .span(expression.span),
            None => absy::Expression::IntConstant(
                BigUint::parse_bytes(expression.value.span.as_str().as_bytes(), 10).unwrap(),
            )
            .span(expression.span),
        }
    }
}

impl<'ast> From<pest::HexLiteralExpression<'ast>> for absy::ExpressionNode<'ast> {
    fn from(expression: pest::HexLiteralExpression<'ast>) -> absy::ExpressionNode<'ast> {
        use crate::absy::NodeValue;

        match expression.value {
            pest::HexNumberExpression::U64(e) => {
                absy::Expression::U64Constant(u64::from_str_radix(e.span.as_str(), 16).unwrap())
            }
            pest::HexNumberExpression::U32(e) => {
                absy::Expression::U32Constant(u32::from_str_radix(e.span.as_str(), 16).unwrap())
            }
            pest::HexNumberExpression::U16(e) => {
                absy::Expression::U16Constant(u16::from_str_radix(e.span.as_str(), 16).unwrap())
            }
            pest::HexNumberExpression::U8(e) => {
                absy::Expression::U8Constant(u8::from_str_radix(e.span.as_str(), 16).unwrap())
            }
        }
        .span(expression.span)
    }
}

impl<'ast> From<pest::LiteralExpression<'ast>> for absy::ExpressionNode<'ast> {
    fn from(expression: pest::LiteralExpression<'ast>) -> absy::ExpressionNode<'ast> {
        use crate::absy::NodeValue;

        match expression {
            pest::LiteralExpression::BooleanLiteral(c) => {
                absy::Expression::BooleanConstant(c.value.parse().unwrap()).span(c.span)
            }
            pest::LiteralExpression::DecimalLiteral(n) => absy::ExpressionNode::from(n),
            pest::LiteralExpression::HexLiteral(n) => absy::ExpressionNode::from(n),
        }
    }
}

impl<'ast> From<pest::IdentifierExpression<'ast>> for absy::ExpressionNode<'ast> {
    fn from(expression: pest::IdentifierExpression<'ast>) -> absy::ExpressionNode<'ast> {
        use crate::absy::NodeValue;
        absy::Expression::Identifier(expression.span.as_str()).span(expression.span)
    }
}

impl<'ast> From<pest::IdentifierExpression<'ast>> for absy::AssigneeNode<'ast> {
    fn from(expression: pest::IdentifierExpression<'ast>) -> absy::AssigneeNode<'ast> {
        use crate::absy::NodeValue;

        absy::Assignee::Identifier(expression.span.as_str()).span(expression.span)
    }
}

impl<'ast> From<pest::Assignee<'ast>> for absy::AssigneeNode<'ast> {
    fn from(assignee: pest::Assignee<'ast>) -> absy::AssigneeNode<'ast> {
        use crate::absy::NodeValue;

        let a = absy::AssigneeNode::from(assignee.id);
        let span = assignee.span;

        assignee.accesses.into_iter().fold(a, |acc, s| {
            match s {
                pest::AssigneeAccess::Select(s) => {
                    absy::Assignee::Select(box acc, box absy::RangeOrExpression::from(s.expression))
                }
                pest::AssigneeAccess::Dot(a) => match a.inner {
                    pest::IdentifierOrDecimal::Identifier(id) => {
                        absy::Assignee::Member(box acc, box id.span.as_str())
                    }
                    pest::IdentifierOrDecimal::Decimal(id) => {
                        absy::Assignee::Element(box acc, id.span.as_str().parse().unwrap())
                    }
                },
            }
            .span(span.clone())
        })
    }
}

impl<'ast> From<pest::Type<'ast>> for absy::UnresolvedTypeNode<'ast> {
    fn from(t: pest::Type<'ast>) -> absy::UnresolvedTypeNode<'ast> {
        use crate::absy::types::UnresolvedType;
        use crate::absy::NodeValue;

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
                                        Some(absy::ExpressionNode::from(v))
                                    }
                                    pest::ConstantGenericValue::Identifier(i) => Some(
                                        absy::Expression::Identifier(i.span.as_str()).span(i.span),
                                    ),
                                })
                                .collect()
                        }),
                    )
                    .span(t.span),
                    pest::BasicOrStructOrTupleType::Tuple(t) => UnresolvedType::Tuple(
                        t.elements
                            .into_iter()
                            .map(absy::UnresolvedTypeNode::from)
                            .collect(),
                    )
                    .span(t.span),
                };

                let span = t.span;

                t.dimensions
                    .into_iter()
                    .map(absy::ExpressionNode::from)
                    .rev()
                    .fold(None, |acc, s| match acc {
                        None => Some(UnresolvedType::array(inner_type.clone(), s)),
                        Some(acc) => Some(UnresolvedType::array(acc.span(span.clone()), s)),
                    })
                    .unwrap()
                    .span(span.clone())
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
                                Some(absy::ExpressionNode::from(v))
                            }
                            pest::ConstantGenericValue::Identifier(i) => {
                                Some(absy::Expression::Identifier(i.span.as_str()).span(i.span))
                            }
                        })
                        .collect()
                }),
            )
            .span(s.span),
            pest::Type::Tuple(t) => UnresolvedType::Tuple(
                t.elements
                    .into_iter()
                    .map(absy::UnresolvedTypeNode::from)
                    .collect(),
            )
            .span(t.span),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::absy::types::{UnresolvedSignature, UnresolvedType};
    use crate::absy::NodeValue;

    #[test]
    fn return_forty_two() {
        let source = "def main() -> field: return 42";
        let ast = pest::generate_ast(source).unwrap();
        let expected: absy::Module = absy::Module {
            symbols: vec![absy::SymbolDeclaration {
                id: &source[4..8],
                symbol: absy::Symbol::Here(absy::SymbolDefinition::Function(
                    absy::Function {
                        arguments: vec![],
                        statements: vec![absy::Statement::Return(
                            absy::ExpressionList {
                                expressions: vec![
                                    absy::Expression::IntConstant(42usize.into()).into()
                                ],
                            }
                            .into(),
                        )
                        .into()],
                        signature: UnresolvedSignature::new()
                            .inputs(vec![])
                            .outputs(vec![UnresolvedType::FieldElement.mock()]),
                    }
                    .into(),
                )),
            }
            .into()],
        };
        assert_eq!(absy::Module::from(ast), expected);
    }

    #[test]
    fn return_true() {
        let source = "def main() -> bool: return true";
        let ast = pest::generate_ast(source).unwrap();
        let expected: absy::Module = absy::Module {
            symbols: vec![absy::SymbolDeclaration {
                id: &source[4..8],
                symbol: absy::Symbol::Here(absy::SymbolDefinition::Function(
                    absy::Function {
                        arguments: vec![],
                        statements: vec![absy::Statement::Return(
                            absy::ExpressionList {
                                expressions: vec![absy::Expression::BooleanConstant(true).into()],
                            }
                            .into(),
                        )
                        .into()],
                        signature: UnresolvedSignature::new()
                            .inputs(vec![])
                            .outputs(vec![UnresolvedType::Boolean.mock()]),
                    }
                    .into(),
                )),
            }
            .into()],
        };
        assert_eq!(absy::Module::from(ast), expected);
    }

    #[test]
    fn arguments() {
        let source = "def main(private field a, bool b) -> field: return 42";
        let ast = pest::generate_ast(source).unwrap();

        let expected: absy::Module = absy::Module {
            symbols: vec![absy::SymbolDeclaration {
                id: &source[4..8],
                symbol: absy::Symbol::Here(absy::SymbolDefinition::Function(
                    absy::Function {
                        arguments: vec![
                            absy::Parameter::private(
                                absy::Variable::new(
                                    &source[23..24],
                                    UnresolvedType::FieldElement.mock(),
                                )
                                .into(),
                            )
                            .into(),
                            absy::Parameter::public(
                                absy::Variable::new(
                                    &source[31..32],
                                    UnresolvedType::Boolean.mock(),
                                )
                                .into(),
                            )
                            .into(),
                        ],
                        statements: vec![absy::Statement::Return(
                            absy::ExpressionList {
                                expressions: vec![
                                    absy::Expression::IntConstant(42usize.into()).into()
                                ],
                            }
                            .into(),
                        )
                        .into()],
                        signature: UnresolvedSignature::new()
                            .inputs(vec![
                                UnresolvedType::FieldElement.mock(),
                                UnresolvedType::Boolean.mock(),
                            ])
                            .outputs(vec![UnresolvedType::FieldElement.mock()]),
                    }
                    .into(),
                )),
            }
            .into()],
        };

        assert_eq!(absy::Module::from(ast), expected);
    }

    mod types {
        use super::*;

        /// Helper method to generate the ast for `def main(private {ty} a): return` which we use to check ty
        fn wrap(ty: UnresolvedType<'static>) -> absy::Module<'static> {
            absy::Module {
                symbols: vec![absy::SymbolDeclaration {
                    id: "main",
                    symbol: absy::Symbol::Here(absy::SymbolDefinition::Function(
                        absy::Function {
                            arguments: vec![absy::Parameter::private(
                                absy::Variable::new("a", ty.clone().mock()).into(),
                            )
                            .into()],
                            statements: vec![absy::Statement::Return(
                                absy::ExpressionList {
                                    expressions: vec![],
                                }
                                .into(),
                            )
                            .into()],
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
                    absy::UnresolvedType::Array(
                        box absy::UnresolvedType::FieldElement.mock(),
                        absy::Expression::IntConstant(2usize.into()).mock(),
                    ),
                ),
                (
                    "field[2][3]",
                    absy::UnresolvedType::Array(
                        box absy::UnresolvedType::Array(
                            box absy::UnresolvedType::FieldElement.mock(),
                            absy::Expression::IntConstant(3usize.into()).mock(),
                        )
                        .mock(),
                        absy::Expression::IntConstant(2usize.into()).mock(),
                    ),
                ),
                (
                    "bool[2][3u32]",
                    absy::UnresolvedType::Array(
                        box absy::UnresolvedType::Array(
                            box absy::UnresolvedType::Boolean.mock(),
                            absy::Expression::U32Constant(3u32).mock(),
                        )
                        .mock(),
                        absy::Expression::IntConstant(2usize.into()).mock(),
                    ),
                ),
            ];

            for (ty, expected) in vectors {
                let source = format!("def main(private {} a): return", ty);
                let expected = wrap(expected);
                let ast = pest::generate_ast(&source).unwrap();
                assert_eq!(absy::Module::from(ast), expected);
            }
        }
    }

    mod postfix {
        use super::*;
        fn wrap(expression: absy::Expression<'static>) -> absy::Module {
            absy::Module {
                symbols: vec![absy::SymbolDeclaration {
                    id: "main",
                    symbol: absy::Symbol::Here(absy::SymbolDefinition::Function(
                        absy::Function {
                            arguments: vec![],
                            statements: vec![absy::Statement::Return(
                                absy::ExpressionList {
                                    expressions: vec![expression.into()],
                                }
                                .into(),
                            )
                            .into()],
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
                ("a", absy::Expression::Identifier("a")),
                (
                    "a[3]",
                    absy::Expression::Select(
                        box absy::Expression::Identifier("a").into(),
                        box absy::RangeOrExpression::Expression(
                            absy::Expression::IntConstant(3usize.into()).into(),
                        ),
                    ),
                ),
                (
                    "a[3][4]",
                    absy::Expression::Select(
                        box absy::Expression::Select(
                            box absy::Expression::Identifier("a").into(),
                            box absy::RangeOrExpression::Expression(
                                absy::Expression::IntConstant(3usize.into()).into(),
                            ),
                        )
                        .into(),
                        box absy::RangeOrExpression::Expression(
                            absy::Expression::IntConstant(4usize.into()).into(),
                        ),
                    ),
                ),
                (
                    "a(3)[4]",
                    absy::Expression::Select(
                        box absy::Expression::FunctionCall(
                            box absy::Expression::Identifier("a").mock(),
                            None,
                            vec![absy::Expression::IntConstant(3usize.into()).into()],
                        )
                        .into(),
                        box absy::RangeOrExpression::Expression(
                            absy::Expression::IntConstant(4usize.into()).into(),
                        ),
                    ),
                ),
                (
                    "a(3)[4][5]",
                    absy::Expression::Select(
                        box absy::Expression::Select(
                            box absy::Expression::FunctionCall(
                                box absy::Expression::Identifier("a").mock(),
                                None,
                                vec![absy::Expression::IntConstant(3usize.into()).into()],
                            )
                            .into(),
                            box absy::RangeOrExpression::Expression(
                                absy::Expression::IntConstant(4usize.into()).into(),
                            ),
                        )
                        .into(),
                        box absy::RangeOrExpression::Expression(
                            absy::Expression::IntConstant(5usize.into()).into(),
                        ),
                    ),
                ),
            ];

            for (source, expected) in vectors {
                let source = format!("def main(): return {}", source);
                let expected = wrap(expected);
                let ast = pest::generate_ast(&source).unwrap();
                assert_eq!(absy::Module::from(ast), expected);
            }
        }

        #[test]
        fn call_array_element() {
            // a call after an array access should be accepted
            let source = "def main(): return a[2](3)";
            let ast = pest::generate_ast(source).unwrap();
            assert_eq!(
                absy::Module::from(ast),
                wrap(absy::Expression::FunctionCall(
                    box absy::Expression::Select(
                        box absy::Expression::Identifier("a").mock(),
                        box absy::RangeOrExpression::Expression(
                            absy::Expression::IntConstant(2u32.into()).mock()
                        )
                    )
                    .mock(),
                    None,
                    vec![absy::Expression::IntConstant(3u32.into()).mock()],
                ))
            );
        }

        #[test]
        fn call_call_result() {
            // a call after a call should be accepted
            let source = "def main(): return a(2)(3)";

            let ast = pest::generate_ast(source).unwrap();
            assert_eq!(
                absy::Module::from(ast),
                wrap(absy::Expression::FunctionCall(
                    box absy::Expression::FunctionCall(
                        box absy::Expression::Identifier("a").mock(),
                        None,
                        vec![absy::Expression::IntConstant(2u32.into()).mock()]
                    )
                    .mock(),
                    None,
                    vec![absy::Expression::IntConstant(3u32.into()).mock()],
                ))
            );
        }
    }
    #[test]
    fn declarations() {
        use self::pest::Span;

        let span = Span::new("", 0, 0).unwrap();

        // For different definitions, we generate declarations
        // Case 1: `id = expr` where `expr` is not a function call
        // This is a simple assignment, doesn't implicitely declare a variable
        // A `Definition` is generated and no `Declaration`s

        let definition = pest::DefinitionStatement {
            lhs: vec![pest::TypedIdentifierOrAssignee::Assignee(pest::Assignee {
                id: pest::IdentifierExpression {
                    value: String::from("a"),
                    span: span.clone(),
                },
                accesses: vec![],
                span: span.clone(),
            })],
            expression: pest::Expression::Literal(pest::LiteralExpression::DecimalLiteral(
                pest::DecimalLiteralExpression {
                    value: pest::DecimalNumber {
                        span: Span::new("1", 0, 1).unwrap(),
                    },
                    suffix: None,
                    span: span.clone(),
                },
            )),
            span: span.clone(),
        };

        let statements: Vec<absy::StatementNode> = statements_from_definition(definition);

        assert_eq!(statements.len(), 1);
        match &statements[0].value {
            absy::Statement::Definition(..) => {}
            s => {
                panic!("should be a Definition, found {}", s);
            }
        };

        // Case 2: `id = expr` where `expr` is a function call
        // A MultiDef is generated

        let definition = pest::DefinitionStatement {
            lhs: vec![pest::TypedIdentifierOrAssignee::Assignee(pest::Assignee {
                id: pest::IdentifierExpression {
                    value: String::from("a"),
                    span: span.clone(),
                },
                accesses: vec![],
                span: span.clone(),
            })],
            expression: pest::Expression::Postfix(pest::PostfixExpression {
                base: box pest::Expression::Identifier(pest::IdentifierExpression {
                    value: String::from("foo"),
                    span: span.clone(),
                }),
                accesses: vec![pest::Access::Call(pest::CallAccess {
                    explicit_generics: None,
                    arguments: pest::Arguments {
                        expressions: vec![],
                        span: span.clone(),
                    },
                    span: span.clone(),
                })],
                span: span.clone(),
            }),
            span: span.clone(),
        };

        let statements: Vec<absy::StatementNode> = statements_from_definition(definition);

        assert_eq!(statements.len(), 1);
        match &statements[0].value {
            absy::Statement::MultipleDefinition(..) => {}
            s => {
                panic!("should be a Definition, found {}", s);
            }
        };
        // Case 3: `ids = expr` where `expr` is a function call
        // This implicitely declares all variables which are type annotated

        // `field a, b = foo()`

        let definition = pest::DefinitionStatement {
            lhs: vec![
                pest::TypedIdentifierOrAssignee::TypedIdentifier(pest::TypedIdentifier {
                    ty: pest::Type::Basic(pest::BasicType::Field(pest::FieldType {
                        span: span.clone(),
                    })),
                    identifier: pest::IdentifierExpression {
                        value: String::from("a"),
                        span: span.clone(),
                    },
                    span: span.clone(),
                }),
                pest::TypedIdentifierOrAssignee::Assignee(pest::Assignee {
                    id: pest::IdentifierExpression {
                        value: String::from("b"),
                        span: span.clone(),
                    },
                    accesses: vec![],
                    span: span.clone(),
                }),
            ],
            expression: pest::Expression::Postfix(pest::PostfixExpression {
                base: box pest::Expression::Identifier(pest::IdentifierExpression {
                    value: String::from("foo"),
                    span: span.clone(),
                }),
                accesses: vec![pest::Access::Call(pest::CallAccess {
                    explicit_generics: None,
                    arguments: pest::Arguments {
                        expressions: vec![],
                        span: span.clone(),
                    },
                    span: span.clone(),
                })],
                span: span.clone(),
            }),
            span: span.clone(),
        };

        let statements: Vec<absy::StatementNode> = statements_from_definition(definition);

        assert_eq!(statements.len(), 2);
        match &statements[1].value {
            absy::Statement::MultipleDefinition(..) => {}
            s => {
                panic!("should be a Definition, found {}", s);
            }
        };
    }
}
