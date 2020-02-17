use absy;
use imports;
use zokrates_field::field::Field;
use zokrates_pest_ast as pest;

impl<'ast, T: Field> From<pest::File<'ast>> for absy::Module<'ast, T> {
    fn from(prog: pest::File<'ast>) -> absy::Module<T> {
        absy::Module::with_symbols(
            prog.structs
                .into_iter()
                .map(|t| absy::SymbolDeclarationNode::from(t))
                .chain(
                    prog.functions
                        .into_iter()
                        .map(|f| absy::SymbolDeclarationNode::from(f)),
                ),
        )
        .imports(prog.imports.into_iter().map(|i| absy::ImportNode::from(i)))
    }
}

impl<'ast> From<pest::ImportDirective<'ast>> for absy::ImportNode<'ast> {
    fn from(import: pest::ImportDirective<'ast>) -> absy::ImportNode {
        use absy::NodeValue;

        match import {
            pest::ImportDirective::Main(import) => {
                imports::Import::new(None, std::path::Path::new(import.source.span.as_str()))
                    .alias(import.alias.map(|a| a.span.as_str()))
                    .span(import.span)
            }
            pest::ImportDirective::From(import) => imports::Import::new(
                Some(import.symbol.span.as_str()),
                std::path::Path::new(import.source.span.as_str()),
            )
            .alias(import.alias.map(|a| a.span.as_str()))
            .span(import.span),
        }
    }
}

impl<'ast, T: Field> From<pest::StructDefinition<'ast>> for absy::SymbolDeclarationNode<'ast, T> {
    fn from(definition: pest::StructDefinition<'ast>) -> absy::SymbolDeclarationNode<'ast, T> {
        use absy::NodeValue;

        let span = definition.span;

        let id = definition.id.span.as_str();

        let ty = absy::StructType {
            fields: definition
                .fields
                .into_iter()
                .map(|f| absy::StructFieldNode::from(f))
                .collect(),
        }
        .span(span.clone());

        absy::SymbolDeclaration {
            id,
            symbol: absy::Symbol::HereType(ty),
        }
        .span(span)
    }
}

impl<'ast> From<pest::StructField<'ast>> for absy::StructFieldNode<'ast> {
    fn from(field: pest::StructField<'ast>) -> absy::StructFieldNode {
        use absy::NodeValue;

        let span = field.span;

        let id = field.id.span.as_str();

        let ty = absy::UnresolvedTypeNode::from(field.ty);

        absy::StructField { id, ty }.span(span)
    }
}

impl<'ast, T: Field> From<pest::Function<'ast>> for absy::SymbolDeclarationNode<'ast, T> {
    fn from(function: pest::Function<'ast>) -> absy::SymbolDeclarationNode<T> {
        use absy::NodeValue;

        let span = function.span;

        let signature = absy::UnresolvedSignature::new()
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
                    .map(|r| absy::UnresolvedTypeNode::from(r))
                    .collect(),
            );

        let id = function.id.span.as_str();

        let function = absy::Function::<T> {
            arguments: function
                .parameters
                .into_iter()
                .map(|a| absy::ParameterNode::from(a))
                .collect(),
            statements: function
                .statements
                .into_iter()
                .flat_map(|s| statements_from_statement(s))
                .collect(),
            signature,
        }
        .span(span.clone());

        absy::SymbolDeclaration {
            id,
            symbol: absy::Symbol::HereFunction(function),
        }
        .span(span)
    }
}

impl<'ast> From<pest::Parameter<'ast>> for absy::ParameterNode<'ast> {
    fn from(param: pest::Parameter<'ast>) -> absy::ParameterNode {
        use absy::NodeValue;

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

fn statements_from_statement<'ast, T: Field>(
    statement: pest::Statement<'ast>,
) -> Vec<absy::StatementNode<T>> {
    match statement {
        pest::Statement::Definition(s) => statements_from_definition(s),
        pest::Statement::Iteration(s) => vec![absy::StatementNode::from(s)],
        pest::Statement::Assertion(s) => vec![absy::StatementNode::from(s)],
        pest::Statement::Assignment(s) => vec![absy::StatementNode::from(s)],
        pest::Statement::Return(s) => vec![absy::StatementNode::from(s)],
        pest::Statement::MultiAssignment(s) => statements_from_multi_assignment(s),
    }
}

fn statements_from_multi_assignment<'ast, T: Field>(
    assignment: pest::MultiAssignmentStatement<'ast>,
) -> Vec<absy::StatementNode<T>> {
    use absy::NodeValue;

    let declarations = assignment
        .lhs
        .clone()
        .into_iter()
        .filter(|i| i.ty.is_some())
        .map(|i| {
            absy::Statement::Declaration(
                absy::Variable::new(
                    i.id.span.as_str(),
                    absy::UnresolvedTypeNode::from(i.ty.unwrap()),
                )
                .span(i.id.span),
            )
            .span(i.span)
        });

    let lhs = assignment
        .lhs
        .into_iter()
        .map(|i| absy::Assignee::Identifier(i.id.span.as_str()).span(i.id.span))
        .collect();

    let multi_def = absy::Statement::MultipleDefinition(
        lhs,
        absy::Expression::FunctionCall(
            &assignment.function_id.span.as_str(),
            assignment
                .arguments
                .into_iter()
                .map(|e| absy::ExpressionNode::from(e))
                .collect(),
        )
        .span(assignment.function_id.span),
    )
    .span(assignment.span);

    declarations.chain(std::iter::once(multi_def)).collect()
}

fn statements_from_definition<'ast, T: Field>(
    definition: pest::DefinitionStatement<'ast>,
) -> Vec<absy::StatementNode<T>> {
    use absy::NodeValue;

    vec![
        absy::Statement::Declaration(
            absy::Variable::new(
                definition.id.span.as_str(),
                absy::UnresolvedTypeNode::from(definition.ty),
            )
            .span(definition.id.span.clone()),
        )
        .span(definition.span.clone()),
        absy::Statement::Definition(
            absy::AssigneeNode::from(definition.id),
            absy::ExpressionNode::from(definition.expression),
        )
        .span(definition.span),
    ]
}

impl<'ast, T: Field> From<pest::ReturnStatement<'ast>> for absy::StatementNode<'ast, T> {
    fn from(statement: pest::ReturnStatement<'ast>) -> absy::StatementNode<T> {
        use absy::NodeValue;

        absy::Statement::Return(
            absy::ExpressionList {
                expressions: statement
                    .expressions
                    .into_iter()
                    .map(|e| absy::ExpressionNode::from(e))
                    .collect(),
            }
            .span(statement.span.clone()),
        )
        .span(statement.span)
    }
}

impl<'ast, T: Field> From<pest::AssertionStatement<'ast>> for absy::StatementNode<'ast, T> {
    fn from(statement: pest::AssertionStatement<'ast>) -> absy::StatementNode<T> {
        use absy::NodeValue;

        match statement.expression {
            pest::Expression::Binary(e) => match e.op {
                pest::BinaryOperator::Eq => absy::Statement::Condition(
                    absy::ExpressionNode::from(*e.left),
                    absy::ExpressionNode::from(*e.right),
                ),
                _ => unimplemented!(
                    "Assertion statements should be an equality check, found {}",
                    statement.span.as_str()
                ),
            },
            _ => unimplemented!(
                "Assertion statements should be an equality check, found {}",
                statement.span.as_str()
            ),
        }
        .span(statement.span)
    }
}

impl<'ast, T: Field> From<pest::IterationStatement<'ast>> for absy::StatementNode<'ast, T> {
    fn from(statement: pest::IterationStatement<'ast>) -> absy::StatementNode<T> {
        use absy::NodeValue;
        let from = absy::ExpressionNode::from(statement.from);
        let to = absy::ExpressionNode::from(statement.to);
        let index = statement.index.span.as_str();
        let ty = absy::UnresolvedTypeNode::from(statement.ty);
        let statements: Vec<absy::StatementNode<T>> = statement
            .statements
            .into_iter()
            .flat_map(|s| statements_from_statement(s))
            .collect();

        let var = absy::Variable::new(index, ty).span(statement.index.span);

        absy::Statement::For(var, from, to, statements).span(statement.span)
    }
}

impl<'ast, T: Field> From<pest::AssignmentStatement<'ast>> for absy::StatementNode<'ast, T> {
    fn from(statement: pest::AssignmentStatement<'ast>) -> absy::StatementNode<T> {
        use absy::NodeValue;

        absy::Statement::Definition(
            absy::AssigneeNode::from(statement.assignee),
            absy::ExpressionNode::from(statement.expression),
        )
        .span(statement.span)
    }
}

impl<'ast, T: Field> From<pest::Expression<'ast>> for absy::ExpressionNode<'ast, T> {
    fn from(expression: pest::Expression<'ast>) -> absy::ExpressionNode<'ast, T> {
        match expression {
            pest::Expression::Binary(e) => absy::ExpressionNode::from(e),
            pest::Expression::Ternary(e) => absy::ExpressionNode::from(e),
            pest::Expression::Constant(e) => absy::ExpressionNode::from(e),
            pest::Expression::Identifier(e) => absy::ExpressionNode::from(e),
            pest::Expression::Postfix(e) => absy::ExpressionNode::from(e),
            pest::Expression::InlineArray(e) => absy::ExpressionNode::from(e),
            pest::Expression::InlineStruct(e) => absy::ExpressionNode::from(e),
            pest::Expression::ArrayInitializer(e) => absy::ExpressionNode::from(e),
            pest::Expression::Unary(e) => absy::ExpressionNode::from(e),
        }
    }
}

impl<'ast, T: Field> From<pest::BinaryExpression<'ast>> for absy::ExpressionNode<'ast, T> {
    fn from(expression: pest::BinaryExpression<'ast>) -> absy::ExpressionNode<'ast, T> {
        use absy::NodeValue;
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
            o => unimplemented!("Operator {:?} not implemented", o),
        }
        .span(expression.span)
    }
}

impl<'ast, T: Field> From<pest::TernaryExpression<'ast>> for absy::ExpressionNode<'ast, T> {
    fn from(expression: pest::TernaryExpression<'ast>) -> absy::ExpressionNode<'ast, T> {
        use absy::NodeValue;
        absy::Expression::IfElse(
            box absy::ExpressionNode::from(*expression.first),
            box absy::ExpressionNode::from(*expression.second),
            box absy::ExpressionNode::from(*expression.third),
        )
        .span(expression.span)
    }
}

impl<'ast, T: Field> From<pest::Spread<'ast>> for absy::SpreadNode<'ast, T> {
    fn from(spread: pest::Spread<'ast>) -> absy::SpreadNode<'ast, T> {
        use absy::NodeValue;
        absy::Spread {
            expression: absy::ExpressionNode::from(spread.expression),
        }
        .span(spread.span)
    }
}

impl<'ast, T: Field> From<pest::Range<'ast>> for absy::RangeNode<T> {
    fn from(range: pest::Range<'ast>) -> absy::RangeNode<T> {
        use absy::NodeValue;

        let from = range
            .from
            .map(|e| match absy::ExpressionNode::from(e.0).value {
                absy::Expression::FieldConstant(n) => n,
                e => unimplemented!("Range bounds should be constants, found {}", e),
            });

        let to = range
            .to
            .map(|e| match absy::ExpressionNode::from(e.0).value {
                absy::Expression::FieldConstant(n) => n,
                e => unimplemented!("Range bounds should be constants, found {}", e),
            });

        absy::Range { from, to }.span(range.span)
    }
}

impl<'ast, T: Field> From<pest::RangeOrExpression<'ast>> for absy::RangeOrExpression<'ast, T> {
    fn from(
        range_or_expression: pest::RangeOrExpression<'ast>,
    ) -> absy::RangeOrExpression<'ast, T> {
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

impl<'ast, T: Field> From<pest::SpreadOrExpression<'ast>> for absy::SpreadOrExpression<'ast, T> {
    fn from(
        spread_or_expression: pest::SpreadOrExpression<'ast>,
    ) -> absy::SpreadOrExpression<'ast, T> {
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

impl<'ast, T: Field> From<pest::InlineArrayExpression<'ast>> for absy::ExpressionNode<'ast, T> {
    fn from(array: pest::InlineArrayExpression<'ast>) -> absy::ExpressionNode<'ast, T> {
        use absy::NodeValue;
        absy::Expression::InlineArray(
            array
                .expressions
                .into_iter()
                .map(|e| absy::SpreadOrExpression::from(e))
                .collect(),
        )
        .span(array.span)
    }
}

impl<'ast, T: Field> From<pest::InlineStructExpression<'ast>> for absy::ExpressionNode<'ast, T> {
    fn from(s: pest::InlineStructExpression<'ast>) -> absy::ExpressionNode<'ast, T> {
        use absy::NodeValue;
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

impl<'ast, T: Field> From<pest::ArrayInitializerExpression<'ast>>
    for absy::ExpressionNode<'ast, T>
{
    fn from(initializer: pest::ArrayInitializerExpression<'ast>) -> absy::ExpressionNode<'ast, T> {
        use absy::NodeValue;

        let value = absy::ExpressionNode::from(*initializer.value);
        let count: absy::ExpressionNode<T> = absy::ExpressionNode::from(initializer.count);
        let count = match count.value {
            absy::Expression::FieldConstant(v) => v.to_dec_string().parse::<usize>().unwrap(),
            _ => unreachable!(),
        };
        absy::Expression::InlineArray(vec![absy::SpreadOrExpression::Expression(value); count])
            .span(initializer.span)
    }
}

impl<'ast, T: Field> From<pest::UnaryExpression<'ast>> for absy::ExpressionNode<'ast, T> {
    fn from(unary: pest::UnaryExpression<'ast>) -> absy::ExpressionNode<'ast, T> {
        use absy::NodeValue;

        match unary.op {
            pest::UnaryOperator::Not(_) => {
                absy::Expression::Not(Box::new(absy::ExpressionNode::from(*unary.expression)))
            }
        }
        .span(unary.span)
    }
}

impl<'ast, T: Field> From<pest::PostfixExpression<'ast>> for absy::ExpressionNode<'ast, T> {
    fn from(expression: pest::PostfixExpression<'ast>) -> absy::ExpressionNode<'ast, T> {
        use absy::NodeValue;

        let id_str = expression.id.span.as_str();
        let id = absy::ExpressionNode::from(expression.id);

        // pest::PostFixExpression contains an array of "accesses": `a(34)[42]` is represented as `[a, [Call(34), Select(42)]]`, but absy::ExpressionNode
        // is recursive, so it is `Select(Call(a, 34), 42)`. We apply this transformation here

        // we start with the id, and we fold the array of accesses by wrapping the current value
        expression.accesses.into_iter().fold(id, |acc, a| match a {
            pest::Access::Call(a) => match acc.value {
                absy::Expression::Identifier(_) => absy::Expression::FunctionCall(
                    &id_str,
                    a.expressions
                        .into_iter()
                        .map(|e| absy::ExpressionNode::from(e))
                        .collect(),
                ),
                e => unimplemented!("only identifiers are callable, found \"{}\"", e),
            }
            .span(a.span),
            pest::Access::Select(a) => {
                absy::Expression::Select(box acc, box absy::RangeOrExpression::from(a.expression))
                    .span(a.span)
            }
            pest::Access::Member(m) => {
                absy::Expression::Member(box acc, box m.id.span.as_str()).span(m.span)
            }
        })
    }
}

impl<'ast, T: Field> From<pest::ConstantExpression<'ast>> for absy::ExpressionNode<'ast, T> {
    fn from(expression: pest::ConstantExpression<'ast>) -> absy::ExpressionNode<'ast, T> {
        use absy::NodeValue;
        match expression {
            pest::ConstantExpression::BooleanLiteral(c) => {
                absy::Expression::BooleanConstant(c.value.parse().unwrap()).span(c.span)
            }
            pest::ConstantExpression::DecimalNumber(n) => {
                absy::Expression::FieldConstant(T::try_from_dec_str(&n.value).unwrap()).span(n.span)
            }
        }
    }
}

impl<'ast, T: Field> From<pest::IdentifierExpression<'ast>> for absy::ExpressionNode<'ast, T> {
    fn from(expression: pest::IdentifierExpression<'ast>) -> absy::ExpressionNode<'ast, T> {
        use absy::NodeValue;
        absy::Expression::Identifier(expression.span.as_str()).span(expression.span)
    }
}

impl<'ast, T: Field> From<pest::IdentifierExpression<'ast>> for absy::AssigneeNode<'ast, T> {
    fn from(expression: pest::IdentifierExpression<'ast>) -> absy::AssigneeNode<T> {
        use absy::NodeValue;

        absy::Assignee::Identifier(expression.span.as_str()).span(expression.span)
    }
}

impl<'ast, T: Field> From<pest::Assignee<'ast>> for absy::AssigneeNode<'ast, T> {
    fn from(assignee: pest::Assignee<'ast>) -> absy::AssigneeNode<T> {
        use absy::NodeValue;

        let a = absy::AssigneeNode::from(assignee.id);
        let span = assignee.span;

        assignee.accesses.into_iter().fold(a, |acc, s| {
            match s {
                pest::AssigneeAccess::Select(s) => {
                    absy::Assignee::Select(box acc, box absy::RangeOrExpression::from(s.expression))
                }
                pest::AssigneeAccess::Member(m) => {
                    absy::Assignee::Member(box acc, box m.id.span.as_str())
                }
            }
            .span(span.clone())
        })
    }
}

impl<'ast> From<pest::Type<'ast>> for absy::UnresolvedTypeNode {
    fn from(t: pest::Type<'ast>) -> absy::UnresolvedTypeNode {
        use absy::NodeValue;

        match t {
            pest::Type::Basic(t) => match t {
                pest::BasicType::Field(t) => absy::UnresolvedType::FieldElement.span(t.span),
                pest::BasicType::Boolean(t) => absy::UnresolvedType::Boolean.span(t.span),
            },
            pest::Type::Array(t) => {
                let inner_type = match t.ty {
                    pest::BasicOrStructType::Basic(t) => match t {
                        pest::BasicType::Field(t) => {
                            absy::UnresolvedType::FieldElement.span(t.span)
                        }
                        pest::BasicType::Boolean(t) => absy::UnresolvedType::Boolean.span(t.span),
                    },
                    pest::BasicOrStructType::Struct(t) => {
                        absy::UnresolvedType::User(t.span.as_str().to_string()).span(t.span)
                    }
                };

                let span = t.span;

                t.dimensions
                    .into_iter()
                    .map(|s| match s {
                        pest::Expression::Constant(c) => match c {
                            pest::ConstantExpression::DecimalNumber(n) => {
                                str::parse::<usize>(&n.value).unwrap()
                            }
                            _ => unimplemented!(
                                "Array size should be a decimal number, found {}",
                                c.span().as_str()
                            ),
                        },
                        e => unimplemented!(
                            "Array size should be constant, found {}",
                            e.span().as_str()
                        ),
                    })
                    .rev()
                    .fold(None, |acc, s| match acc {
                        None => Some(absy::UnresolvedType::array(inner_type.clone(), s)),
                        Some(acc) => Some(absy::UnresolvedType::array(acc.span(span.clone()), s)),
                    })
                    .unwrap()
                    .span(span.clone())
            }
            pest::Type::Struct(s) => {
                absy::UnresolvedType::User(s.id.span.as_str().to_string()).span(s.span)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use absy::NodeValue;
    use zokrates_field::field::FieldPrime;

    #[test]
    fn return_forty_two() {
        let source = "def main() -> (field): return 42";
        let ast = pest::generate_ast(&source).unwrap();
        let expected: absy::Module<FieldPrime> = absy::Module {
            symbols: vec![absy::SymbolDeclaration {
                id: &source[4..8],
                symbol: absy::Symbol::HereFunction(
                    absy::Function {
                        arguments: vec![],
                        statements: vec![absy::Statement::Return(
                            absy::ExpressionList {
                                expressions: vec![absy::Expression::FieldConstant(
                                    FieldPrime::from(42),
                                )
                                .into()],
                            }
                            .into(),
                        )
                        .into()],
                        signature: absy::UnresolvedSignature::new()
                            .inputs(vec![])
                            .outputs(vec![absy::UnresolvedType::FieldElement.mock()]),
                    }
                    .into(),
                ),
            }
            .into()],
            imports: vec![],
        };
        assert_eq!(absy::Module::<FieldPrime>::from(ast), expected);
    }

    #[test]
    fn return_true() {
        let source = "def main() -> (bool): return true";
        let ast = pest::generate_ast(&source).unwrap();
        let expected: absy::Module<FieldPrime> = absy::Module {
            symbols: vec![absy::SymbolDeclaration {
                id: &source[4..8],
                symbol: absy::Symbol::HereFunction(
                    absy::Function {
                        arguments: vec![],
                        statements: vec![absy::Statement::Return(
                            absy::ExpressionList {
                                expressions: vec![absy::Expression::BooleanConstant(true).into()],
                            }
                            .into(),
                        )
                        .into()],
                        signature: absy::UnresolvedSignature::new()
                            .inputs(vec![])
                            .outputs(vec![absy::UnresolvedType::Boolean.mock()]),
                    }
                    .into(),
                ),
            }
            .into()],
            imports: vec![],
        };
        assert_eq!(absy::Module::<FieldPrime>::from(ast), expected);
    }

    #[test]
    fn arguments() {
        let source = "def main(private field a, bool b) -> (field): return 42";
        let ast = pest::generate_ast(&source).unwrap();

        let expected: absy::Module<FieldPrime> = absy::Module {
            symbols: vec![absy::SymbolDeclaration {
                id: &source[4..8],
                symbol: absy::Symbol::HereFunction(
                    absy::Function {
                        arguments: vec![
                            absy::Parameter::private(
                                absy::Variable::new(
                                    &source[23..24],
                                    absy::UnresolvedType::FieldElement.mock(),
                                )
                                .into(),
                            )
                            .into(),
                            absy::Parameter::public(
                                absy::Variable::new(
                                    &source[31..32],
                                    absy::UnresolvedType::Boolean.mock(),
                                )
                                .into(),
                            )
                            .into(),
                        ],
                        statements: vec![absy::Statement::Return(
                            absy::ExpressionList {
                                expressions: vec![absy::Expression::FieldConstant(
                                    FieldPrime::from(42),
                                )
                                .into()],
                            }
                            .into(),
                        )
                        .into()],
                        signature: absy::UnresolvedSignature::new()
                            .inputs(vec![
                                absy::UnresolvedType::FieldElement.mock(),
                                absy::UnresolvedType::Boolean.mock(),
                            ])
                            .outputs(vec![absy::UnresolvedType::FieldElement.mock()]),
                    }
                    .into(),
                ),
            }
            .into()],
            imports: vec![],
        };

        assert_eq!(absy::Module::<FieldPrime>::from(ast), expected);
    }

    mod types {
        use super::*;

        /// Helper method to generate the ast for `def main(private {ty} a) -> (): return` which we use to check ty
        fn wrap(ty: absy::UnresolvedType) -> absy::Module<'static, FieldPrime> {
            absy::Module {
                symbols: vec![absy::SymbolDeclaration {
                    id: "main",
                    symbol: absy::Symbol::HereFunction(
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
                            signature: absy::UnresolvedSignature::new().inputs(vec![ty.mock()]),
                        }
                        .into(),
                    ),
                }
                .into()],
                imports: vec![],
            }
        }

        #[test]
        fn array() {
            let vectors = vec![
                ("field", absy::UnresolvedType::FieldElement),
                ("bool", absy::UnresolvedType::Boolean),
                (
                    "field[2]",
                    absy::UnresolvedType::Array(box absy::UnresolvedType::FieldElement.mock(), 2),
                ),
                (
                    "field[2][3]",
                    absy::UnresolvedType::Array(
                        box absy::UnresolvedType::Array(
                            box absy::UnresolvedType::FieldElement.mock(),
                            3,
                        )
                        .mock(),
                        2,
                    ),
                ),
                (
                    "bool[2][3]",
                    absy::UnresolvedType::Array(
                        box absy::UnresolvedType::Array(
                            box absy::UnresolvedType::Boolean.mock(),
                            3,
                        )
                        .mock(),
                        2,
                    ),
                ),
            ];

            for (ty, expected) in vectors {
                let source = format!("def main(private {} a) -> (): return", ty);
                let expected = wrap(expected);
                let ast = pest::generate_ast(&source).unwrap();
                assert_eq!(absy::Module::<FieldPrime>::from(ast), expected);
            }
        }
    }

    mod postfix {
        use super::*;
        fn wrap(expression: absy::Expression<'static, FieldPrime>) -> absy::Module<FieldPrime> {
            absy::Module {
                symbols: vec![absy::SymbolDeclaration {
                    id: "main",
                    symbol: absy::Symbol::HereFunction(
                        absy::Function {
                            arguments: vec![],
                            statements: vec![absy::Statement::Return(
                                absy::ExpressionList {
                                    expressions: vec![expression.into()],
                                }
                                .into(),
                            )
                            .into()],
                            signature: absy::UnresolvedSignature::new(),
                        }
                        .into(),
                    ),
                }
                .into()],
                imports: vec![],
            }
        }

        #[test]
        fn success() {
            // we basically accept `()?[]*` : an optional call at first, then only array accesses

            let vectors = vec![
                ("a", absy::Expression::Identifier("a").into()),
                (
                    "a[3]",
                    absy::Expression::Select(
                        box absy::Expression::Identifier("a").into(),
                        box absy::RangeOrExpression::Expression(
                            absy::Expression::FieldConstant(FieldPrime::from(3)).into(),
                        )
                        .into(),
                    ),
                ),
                (
                    "a[3][4]",
                    absy::Expression::Select(
                        box absy::Expression::Select(
                            box absy::Expression::Identifier("a").into(),
                            box absy::RangeOrExpression::Expression(
                                absy::Expression::FieldConstant(FieldPrime::from(3)).into(),
                            )
                            .into(),
                        )
                        .into(),
                        box absy::RangeOrExpression::Expression(
                            absy::Expression::FieldConstant(FieldPrime::from(4)).into(),
                        )
                        .into(),
                    ),
                ),
                (
                    "a(3)[4]",
                    absy::Expression::Select(
                        box absy::Expression::FunctionCall(
                            "a",
                            vec![absy::Expression::FieldConstant(FieldPrime::from(3)).into()],
                        )
                        .into(),
                        box absy::RangeOrExpression::Expression(
                            absy::Expression::FieldConstant(FieldPrime::from(4)).into(),
                        )
                        .into(),
                    ),
                ),
                (
                    "a(3)[4][5]",
                    absy::Expression::Select(
                        box absy::Expression::Select(
                            box absy::Expression::FunctionCall(
                                "a",
                                vec![absy::Expression::FieldConstant(FieldPrime::from(3)).into()],
                            )
                            .into(),
                            box absy::RangeOrExpression::Expression(
                                absy::Expression::FieldConstant(FieldPrime::from(4)).into(),
                            )
                            .into(),
                        )
                        .into(),
                        box absy::RangeOrExpression::Expression(
                            absy::Expression::FieldConstant(FieldPrime::from(5)).into(),
                        )
                        .into(),
                    ),
                ),
            ];

            for (source, expected) in vectors {
                let source = format!("def main() -> (): return {}", source);
                let expected = wrap(expected);
                let ast = pest::generate_ast(&source).unwrap();
                assert_eq!(absy::Module::<FieldPrime>::from(ast), expected);
            }
        }

        #[test]
        #[should_panic]
        fn call_array_element() {
            // a call after an array access should be rejected
            let source = "def main() -> (): return a[2](3)";
            let ast = pest::generate_ast(&source).unwrap();
            absy::Module::<FieldPrime>::from(ast);
        }

        #[test]
        #[should_panic]
        fn call_call_result() {
            // a call after a call should be rejected
            let source = "def main() -> (): return a(2)(3)";
            let ast = pest::generate_ast(&source).unwrap();
            absy::Module::<FieldPrime>::from(ast);
        }
    }
}
