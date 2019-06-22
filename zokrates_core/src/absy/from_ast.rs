use absy;
use imports;
use types::Type;
use zokrates_field::field::Field;
use zokrates_pest_ast as pest;

impl<'ast, T: Field> From<pest::File<'ast>> for absy::Prog<'ast, T> {
    fn from(prog: pest::File<'ast>) -> absy::Prog<T> {
        absy::Prog {
            functions: prog
                .functions
                .into_iter()
                .map(|f| absy::FunctionNode::from(f))
                .collect(),
            imports: prog
                .imports
                .into_iter()
                .map(|i| absy::ImportNode::from(i))
                .collect(),
            imported_functions: vec![],
        }
    }
}

impl<'ast> From<pest::ImportDirective<'ast>> for absy::ImportNode {
    fn from(import: pest::ImportDirective<'ast>) -> absy::ImportNode {
        use absy::NodeValue;

        imports::Import::new(import.source.value)
            .alias(import.alias.map(|a| a.value))
            .span(import.span)
    }
}

impl<'ast, T: Field> From<pest::Function<'ast>> for absy::FunctionNode<'ast, T> {
    fn from(function: pest::Function<'ast>) -> absy::FunctionNode<T> {
        use absy::NodeValue;

        let span = function.span;

        let signature = absy::Signature::new()
            .inputs(
                function
                    .parameters
                    .clone()
                    .into_iter()
                    .map(|p| absy::ParameterNode::from(p).value.id.value.get_type())
                    .collect(),
            )
            .outputs(
                function
                    .returns
                    .clone()
                    .into_iter()
                    .map(|r| Type::from(r))
                    .collect(),
            );

        absy::Function::<T> {
            id: function.id.span.as_str(),
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

        let variable =
            absy::Variable::new(param.id.span.as_str(), Type::from(param.ty)).span(param.id.span);

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
                absy::Variable::new(i.id.span.as_str(), Type::from(i.ty.unwrap())).span(i.id.span),
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
            assignment.function_id.value,
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
            absy::Variable::new(definition.id.span.as_str(), Type::from(definition.ty))
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
        let ty = Type::from(statement.ty);
        let statements: Vec<absy::StatementNode<T>> = statement
            .statements
            .into_iter()
            .flat_map(|s| statements_from_statement(s))
            .collect();

        let from = match from.value {
            absy::Expression::Number(n) => n,
            e => unimplemented!("For loop bounds should be constants, found {}", e),
        };

        let to = match to.value {
            absy::Expression::Number(n) => n,
            e => unimplemented!("For loop bounds should be constants, found {}", e),
        };

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
                absy::Expression::Number(n) => n,
                e => unimplemented!("Range bounds should be constants, found {}", e),
            });

        let to = range
            .to
            .map(|e| match absy::ExpressionNode::from(e.0).value {
                absy::Expression::Number(n) => n,
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

impl<'ast, T: Field> From<pest::ArrayInitializerExpression<'ast>>
    for absy::ExpressionNode<'ast, T>
{
    fn from(initializer: pest::ArrayInitializerExpression<'ast>) -> absy::ExpressionNode<'ast, T> {
        use absy::NodeValue;

        let value = absy::ExpressionNode::from(*initializer.value);
        let count: absy::ExpressionNode<T> = absy::ExpressionNode::from(initializer.count);
        let count = match count.value {
            absy::Expression::Number(v) => v.to_dec_string().parse::<usize>().unwrap(),
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

        assert!(expression.access.len() == 1); // we only allow a single access: function call or array access

        match expression.access[0].clone() {
            pest::Access::Call(a) => absy::Expression::FunctionCall(
                expression.id.value,
                a.expressions
                    .into_iter()
                    .map(|e| absy::ExpressionNode::from(e))
                    .collect(),
            ),
            pest::Access::Select(a) => absy::Expression::Select(
                box absy::ExpressionNode::from(expression.id),
                box absy::RangeOrExpression::from(a.expression),
            ),
        }
        .span(expression.span)
    }
}

impl<'ast, T: Field> From<pest::ConstantExpression<'ast>> for absy::ExpressionNode<'ast, T> {
    fn from(expression: pest::ConstantExpression<'ast>) -> absy::ExpressionNode<'ast, T> {
        use absy::NodeValue;
        match expression {
            pest::ConstantExpression::BooleanConstant(c) => {
                absy::Expression::BooleanConstant(c.value.parse().unwrap()).span(c.span)
            }
            pest::ConstantExpression::DecimalNumber(n) => {
                absy::Expression::Number(T::try_from_dec_str(&n.value).unwrap()).span(n.span)
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
        match assignee.indices.len() {
            0 => a,
            1 => absy::Assignee::ArrayElement(
                box a,
                box absy::RangeOrExpression::from(assignee.indices[0].clone()),
            )
            .span(assignee.span),
            n => unimplemented!("Array should have one dimension, found {} in {}", n, a),
        }
    }
}

impl<'ast> From<pest::Type<'ast>> for Type {
    fn from(t: pest::Type<'ast>) -> Type {
        match t {
            pest::Type::Basic(t) => match t {
                pest::BasicType::Field(_) => Type::FieldElement,
                pest::BasicType::Boolean(_) => Type::Boolean,
            },
            pest::Type::Array(t) => {
                let size = match t.size {
                    pest::Expression::Constant(c) => match c {
                        pest::ConstantExpression::DecimalNumber(n) => {
                            str::parse::<usize>(&n.value).unwrap()
                        }
                        _ => unimplemented!(
                            "Array size should be a decimal number, found {}",
                            c.span().as_str()
                        ),
                    },
                    e => {
                        unimplemented!("Array size should be constant, found {}", e.span().as_str())
                    }
                };
                match t.ty {
                    pest::BasicType::Field(_) => Type::FieldElementArray(size),
                    _ => unimplemented!(
                        "Array elements should be field elements, found {}",
                        t.span.as_str()
                    ),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    #[test]
    fn forty_two() {
        let source = "def main() -> (field): return 42
		";
        let ast = pest::generate_ast(&source).unwrap();
        let expected: absy::Prog<FieldPrime> = absy::Prog {
            functions: vec![absy::Function {
                id: &source[4..8],
                arguments: vec![],
                statements: vec![absy::Statement::Return(
                    absy::ExpressionList {
                        expressions: vec![absy::Expression::Number(FieldPrime::from(42)).into()],
                    }
                    .into(),
                )
                .into()],
                signature: absy::Signature::new()
                    .inputs(vec![])
                    .outputs(vec![Type::FieldElement]),
            }
            .into()],
            imports: vec![],
            imported_functions: vec![],
        };
        assert_eq!(absy::Prog::<FieldPrime>::from(ast), expected);
    }

    #[test]
    fn arguments() {
        let source = "def main(private field a, bool b) -> (field): return 42
        ";
        let ast = pest::generate_ast(&source).unwrap();

        let expected: absy::Prog<FieldPrime> = absy::Prog {
            functions: vec![absy::Function {
                id: &source[4..8],
                arguments: vec![
                    absy::Parameter::private(absy::Variable::field_element(&source[23..24]).into())
                        .into(),
                    absy::Parameter::public(absy::Variable::boolean(&source[31..32]).into()).into(),
                ],
                statements: vec![absy::Statement::Return(
                    absy::ExpressionList {
                        expressions: vec![absy::Expression::Number(FieldPrime::from(42)).into()],
                    }
                    .into(),
                )
                .into()],
                signature: absy::Signature::new()
                    .inputs(vec![Type::FieldElement, Type::Boolean])
                    .outputs(vec![Type::FieldElement]),
            }
            .into()],
            imports: vec![],
            imported_functions: vec![],
        };

        assert_eq!(absy::Prog::<FieldPrime>::from(ast), expected);
    }
}
