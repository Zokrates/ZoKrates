use crate::absy;
use crate::imports;

use num::ToPrimitive;
use num_bigint::BigUint;
use zokrates_pest_ast as pest;

impl<'ast> From<pest::File<'ast>> for absy::Module<'ast> {
    fn from(prog: pest::File<'ast>) -> absy::Module<'ast> {
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
    fn from(import: pest::ImportDirective<'ast>) -> absy::ImportNode<'ast> {
        use crate::absy::NodeValue;

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
            .alias(
                import
                    .alias
                    .map(|a| a.span.as_str())
                    .or(Some(import.symbol.span.as_str())),
            )
            .span(import.span),
        }
    }
}

impl<'ast> From<pest::StructDefinition<'ast>> for absy::SymbolDeclarationNode<'ast> {
    fn from(definition: pest::StructDefinition<'ast>) -> absy::SymbolDeclarationNode<'ast> {
        use crate::absy::NodeValue;

        let span = definition.span;

        let id = definition.id.span.as_str();

        let ty = absy::StructDefinition {
            fields: definition
                .fields
                .into_iter()
                .map(|f| absy::StructDefinitionFieldNode::from(f))
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

impl<'ast> From<pest::StructField<'ast>> for absy::StructDefinitionFieldNode<'ast> {
    fn from(field: pest::StructField<'ast>) -> absy::StructDefinitionFieldNode {
        use crate::absy::NodeValue;

        let span = field.span;

        let id = field.id.span.as_str();

        let ty = absy::UnresolvedTypeNode::from(field.ty);

        absy::StructDefinitionField { id, ty }.span(span)
    }
}

impl<'ast> From<pest::Function<'ast>> for absy::SymbolDeclarationNode<'ast> {
    fn from(function: pest::Function<'ast>) -> absy::SymbolDeclarationNode<'ast> {
        use crate::absy::NodeValue;

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

        let function = absy::Function {
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

            let s = match e.value {
                absy::Expression::FunctionCall(..) => absy::Statement::MultipleDefinition(
                    vec![absy::AssigneeNode::from(a.a.clone())],
                    e,
                ),
                _ => absy::Statement::Definition(absy::AssigneeNode::from(a.a.clone()), e),
            };

            match a.ty {
                Some(ty) => {
                    assert_eq!(a.a.accesses.len(), 0);

                    let declaration = absy::Statement::Declaration(
                        absy::Variable::new(
                            a.a.id.span.as_str(),
                            absy::UnresolvedTypeNode::from(ty),
                        )
                        .span(a.a.id.span.clone()),
                    )
                    .span(definition.span.clone());

                    vec![declaration, s.span(definition.span)]
                }
                None => {
                    // Assignment
                    vec![s.span(definition.span)]
                }
            }
        }
        _ => {
            // Multidefinition
            let declarations = lhs.clone().into_iter().filter(|i| i.ty.is_some()).map(|a| {
                let ty = a.ty;
                let a = a.a;

                assert_eq!(a.accesses.len(), 0);
                absy::Statement::Declaration(
                    absy::Variable::new(
                        a.id.span.as_str(),
                        absy::UnresolvedTypeNode::from(ty.unwrap()),
                    )
                    .span(a.id.span),
                )
                .span(a.span)
            });
            let lhs = lhs
                .into_iter()
                .map(|i| absy::Assignee::Identifier(i.a.id.span.as_str()).span(i.a.id.span))
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
                    .map(|e| absy::ExpressionNode::from(e))
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

        absy::Statement::Assertion(absy::ExpressionNode::from(statement.expression))
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
            .flat_map(|s| statements_from_statement(s))
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

impl<'ast> From<pest::TernaryExpression<'ast>> for absy::ExpressionNode<'ast> {
    fn from(expression: pest::TernaryExpression<'ast>) -> absy::ExpressionNode<'ast> {
        use crate::absy::NodeValue;
        absy::Expression::IfElse(
            box absy::ExpressionNode::from(*expression.first),
            box absy::ExpressionNode::from(*expression.second),
            box absy::ExpressionNode::from(*expression.third),
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
                .map(|e| absy::SpreadOrExpression::from(e))
                .collect(),
        )
        .span(array.span)
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
        let count: absy::ExpressionNode<'ast> = absy::ExpressionNode::from(initializer.count);
        let count = match count.value {
            absy::Expression::FieldConstant(v) => v.to_usize().unwrap(),
            _ => unreachable!(),
        };
        absy::Expression::InlineArray(vec![absy::SpreadOrExpression::Expression(value); count])
            .span(initializer.span)
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

impl<'ast> From<pest::ConstantExpression<'ast>> for absy::ExpressionNode<'ast> {
    fn from(expression: pest::ConstantExpression<'ast>) -> absy::ExpressionNode<'ast> {
        use crate::absy::NodeValue;
        match expression {
            pest::ConstantExpression::BooleanLiteral(c) => {
                absy::Expression::BooleanConstant(c.value.parse().unwrap()).span(c.span)
            }
            pest::ConstantExpression::DecimalNumber(n) => absy::Expression::FieldConstant(
                BigUint::parse_bytes(&n.value.as_bytes(), 10).unwrap(),
            )
            .span(n.span),
            pest::ConstantExpression::U8(n) => absy::Expression::U8Constant(
                u8::from_str_radix(&n.value.trim_start_matches("0x"), 16).unwrap(),
            )
            .span(n.span),
            pest::ConstantExpression::U16(n) => absy::Expression::U16Constant(
                u16::from_str_radix(&n.value.trim_start_matches("0x"), 16).unwrap(),
            )
            .span(n.span),
            pest::ConstantExpression::U32(n) => absy::Expression::U32Constant(
                u32::from_str_radix(&n.value.trim_start_matches("0x"), 16).unwrap(),
            )
            .span(n.span),
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
        use crate::absy::types::UnresolvedType;
        use crate::absy::NodeValue;

        match t {
            pest::Type::Basic(t) => match t {
                pest::BasicType::Field(t) => UnresolvedType::FieldElement.span(t.span),
                pest::BasicType::Boolean(t) => UnresolvedType::Boolean.span(t.span),
                pest::BasicType::U8(t) => UnresolvedType::Uint(8).span(t.span),
                pest::BasicType::U16(t) => UnresolvedType::Uint(16).span(t.span),
                pest::BasicType::U32(t) => UnresolvedType::Uint(32).span(t.span),
            },
            pest::Type::Array(t) => {
                let inner_type = match t.ty {
                    pest::BasicOrStructType::Basic(t) => match t {
                        pest::BasicType::Field(t) => UnresolvedType::FieldElement.span(t.span),
                        pest::BasicType::Boolean(t) => UnresolvedType::Boolean.span(t.span),
                        pest::BasicType::U8(t) => UnresolvedType::Uint(8).span(t.span),
                        pest::BasicType::U16(t) => UnresolvedType::Uint(16).span(t.span),
                        pest::BasicType::U32(t) => UnresolvedType::Uint(32).span(t.span),
                    },
                    pest::BasicOrStructType::Struct(t) => {
                        UnresolvedType::User(t.span.as_str().to_string()).span(t.span)
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
                        None => Some(UnresolvedType::array(inner_type.clone(), s)),
                        Some(acc) => Some(UnresolvedType::array(acc.span(span.clone()), s)),
                    })
                    .unwrap()
                    .span(span.clone())
            }
            pest::Type::Struct(s) => {
                UnresolvedType::User(s.id.span.as_str().to_string()).span(s.span)
            }
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
        let ast = pest::generate_ast(&source).unwrap();
        let expected: absy::Module = absy::Module {
            symbols: vec![absy::SymbolDeclaration {
                id: &source[4..8],
                symbol: absy::Symbol::HereFunction(
                    absy::Function {
                        arguments: vec![],
                        statements: vec![absy::Statement::Return(
                            absy::ExpressionList {
                                expressions: vec![absy::Expression::FieldConstant(BigUint::from(
                                    42u32,
                                ))
                                .into()],
                            }
                            .into(),
                        )
                        .into()],
                        signature: UnresolvedSignature::new()
                            .inputs(vec![])
                            .outputs(vec![UnresolvedType::FieldElement.mock()]),
                    }
                    .into(),
                ),
            }
            .into()],
            imports: vec![],
        };
        assert_eq!(absy::Module::from(ast), expected);
    }

    #[test]
    fn return_true() {
        let source = "def main() -> bool: return true";
        let ast = pest::generate_ast(&source).unwrap();
        let expected: absy::Module = absy::Module {
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
                        signature: UnresolvedSignature::new()
                            .inputs(vec![])
                            .outputs(vec![UnresolvedType::Boolean.mock()]),
                    }
                    .into(),
                ),
            }
            .into()],
            imports: vec![],
        };
        assert_eq!(absy::Module::from(ast), expected);
    }

    #[test]
    fn arguments() {
        let source = "def main(private field a, bool b) -> field: return 42";
        let ast = pest::generate_ast(&source).unwrap();

        let expected: absy::Module = absy::Module {
            symbols: vec![absy::SymbolDeclaration {
                id: &source[4..8],
                symbol: absy::Symbol::HereFunction(
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
                                expressions: vec![absy::Expression::FieldConstant(BigUint::from(
                                    42u32,
                                ))
                                .into()],
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
                ),
            }
            .into()],
            imports: vec![],
        };

        assert_eq!(absy::Module::from(ast), expected);
    }

    mod types {
        use super::*;

        /// Helper method to generate the ast for `def main(private {ty} a): return` which we use to check ty
        fn wrap(ty: UnresolvedType) -> absy::Module<'static> {
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
                            signature: UnresolvedSignature::new().inputs(vec![ty.mock()]),
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
                ("field", UnresolvedType::FieldElement),
                ("bool", UnresolvedType::Boolean),
                (
                    "field[2]",
                    UnresolvedType::Array(box UnresolvedType::FieldElement.mock(), 2),
                ),
                (
                    "field[2][3]",
                    UnresolvedType::Array(
                        box UnresolvedType::Array(box UnresolvedType::FieldElement.mock(), 3)
                            .mock(),
                        2,
                    ),
                ),
                (
                    "bool[2][3]",
                    UnresolvedType::Array(
                        box UnresolvedType::Array(box UnresolvedType::Boolean.mock(), 3).mock(),
                        2,
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
                            signature: UnresolvedSignature::new(),
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
                            absy::Expression::FieldConstant(BigUint::from(3u32)).into(),
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
                                absy::Expression::FieldConstant(BigUint::from(3u32)).into(),
                            )
                            .into(),
                        )
                        .into(),
                        box absy::RangeOrExpression::Expression(
                            absy::Expression::FieldConstant(BigUint::from(4u32)).into(),
                        )
                        .into(),
                    ),
                ),
                (
                    "a(3)[4]",
                    absy::Expression::Select(
                        box absy::Expression::FunctionCall(
                            "a",
                            vec![absy::Expression::FieldConstant(BigUint::from(3u32)).into()],
                        )
                        .into(),
                        box absy::RangeOrExpression::Expression(
                            absy::Expression::FieldConstant(BigUint::from(4u32)).into(),
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
                                vec![absy::Expression::FieldConstant(BigUint::from(3u32)).into()],
                            )
                            .into(),
                            box absy::RangeOrExpression::Expression(
                                absy::Expression::FieldConstant(BigUint::from(4u32)).into(),
                            )
                            .into(),
                        )
                        .into(),
                        box absy::RangeOrExpression::Expression(
                            absy::Expression::FieldConstant(BigUint::from(5u32)).into(),
                        )
                        .into(),
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
        #[should_panic]
        fn call_array_element() {
            // a call after an array access should be rejected
            let source = "def main(): return a[2](3)";
            let ast = pest::generate_ast(&source).unwrap();
            absy::Module::from(ast);
        }

        #[test]
        #[should_panic]
        fn call_call_result() {
            // a call after a call should be rejected
            let source = "def main(): return a(2)(3)";
            let ast = pest::generate_ast(&source).unwrap();
            absy::Module::from(ast);
        }
    }
    #[test]
    fn declarations() {
        use self::pest::Span;

        let span = Span::new(&"", 0, 0).unwrap();

        // For different definitions, we generate declarations
        // Case 1: `id = expr` where `expr` is not a function call
        // This is a simple assignment, doesn't implicitely declare a variable
        // A `Definition` is generatedm and no `Declaration`s

        let definition = pest::DefinitionStatement {
            lhs: vec![pest::OptionallyTypedAssignee {
                ty: None,
                a: pest::Assignee {
                    id: pest::IdentifierExpression {
                        value: String::from("a"),
                        span: span.clone(),
                    },
                    accesses: vec![],
                    span: span.clone(),
                },
                span: span.clone(),
            }],
            expression: pest::Expression::Constant(pest::ConstantExpression::DecimalNumber(
                pest::DecimalNumberExpression {
                    value: String::from("42"),
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
            lhs: vec![pest::OptionallyTypedAssignee {
                ty: None,
                a: pest::Assignee {
                    id: pest::IdentifierExpression {
                        value: String::from("a"),
                        span: span.clone(),
                    },
                    accesses: vec![],
                    span: span.clone(),
                },
                span: span.clone(),
            }],
            expression: pest::Expression::Postfix(pest::PostfixExpression {
                id: pest::IdentifierExpression {
                    value: String::from("foo"),
                    span: span.clone(),
                },
                accesses: vec![pest::Access::Call(pest::CallAccess {
                    expressions: vec![],
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
                pest::OptionallyTypedAssignee {
                    ty: Some(pest::Type::Basic(pest::BasicType::Field(pest::FieldType {
                        span: span.clone(),
                    }))),
                    a: pest::Assignee {
                        id: pest::IdentifierExpression {
                            value: String::from("a"),
                            span: span.clone(),
                        },
                        accesses: vec![],
                        span: span.clone(),
                    },
                    span: span.clone(),
                },
                pest::OptionallyTypedAssignee {
                    ty: None,
                    a: pest::Assignee {
                        id: pest::IdentifierExpression {
                            value: String::from("b"),
                            span: span.clone(),
                        },
                        accesses: vec![],
                        span: span.clone(),
                    },
                    span: span.clone(),
                },
            ],
            expression: pest::Expression::Postfix(pest::PostfixExpression {
                id: pest::IdentifierExpression {
                    value: String::from("foo"),
                    span: span.clone(),
                },
                accesses: vec![pest::Access::Call(pest::CallAccess {
                    expressions: vec![],
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
