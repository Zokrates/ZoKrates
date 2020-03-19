//! Module containing constant propagation for the typed AST
//!
//! On top of the usual behavior of removing statements which assign a constant to a variable (as the variable can simply be
//! substituted for the constant whenever used), we provide a `verbose` mode which does not remove such statements. This is done
//! as for partial passes which do not visit the whole program, the variables being defined may be be used in parts of the program
//! that are not visited. Keeping the statements is semantically equivalent and enables rebuilding the set of constants at the
//! next pass.
//!
//! @file propagation.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

use crate::typed_absy::folder::*;
use crate::typed_absy::*;
use std::collections::HashMap;
use std::convert::TryFrom;
use typed_absy::types::{StructMember, Type};
use zokrates_field::field::Field;

pub struct Propagator<'ast, T: Field> {
    // constants keeps track of constant expressions
    // we currently do not support partially constant expressions: `field [x, 1][1]` is not considered constant, `field [0, 1][1]` is
    constants: HashMap<TypedAssignee<'ast, T>, TypedExpression<'ast, T>>,
    // the verbose mode doesn't remove statements which assign constants to variables
    // it's required when using propagation in combination with unrolling
    verbose: bool,
}

impl<'ast, T: Field> Propagator<'ast, T> {
    fn verbose() -> Self {
        Propagator {
            constants: HashMap::new(),
            verbose: true,
        }
    }

    fn new() -> Self {
        Propagator {
            constants: HashMap::new(),
            verbose: false,
        }
    }

    pub fn propagate(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        Propagator::new().fold_program(p)
    }

    pub fn propagate_verbose(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        Propagator::verbose().fold_program(p)
    }
}

fn is_constant<'ast, T: Field>(e: &TypedExpression<'ast, T>) -> bool {
    match e {
        TypedExpression::FieldElement(FieldElementExpression::Number(..)) => true,
        TypedExpression::Boolean(BooleanExpression::Value(..)) => true,
        TypedExpression::Array(a) => match a.as_inner() {
            ArrayExpressionInner::Value(v) => v.iter().all(|e| is_constant(e)),
            _ => false,
        },
        TypedExpression::Struct(a) => match a.as_inner() {
            StructExpressionInner::Value(v) => v.iter().all(|e| is_constant(e)),
            _ => false,
        },
        _ => false,
    }
}

impl<'ast, T: Field> Folder<'ast, T> for Propagator<'ast, T> {
    fn fold_function(&mut self, f: TypedFunction<'ast, T>) -> TypedFunction<'ast, T> {
        self.constants = HashMap::new();
        fold_function(self, f)
    }

    fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        let res = match s {
            TypedStatement::Declaration(v) => Some(TypedStatement::Declaration(v)),
            TypedStatement::Return(expressions) => Some(TypedStatement::Return(
                expressions
                    .into_iter()
                    .map(|e| self.fold_expression(e))
                    .collect(),
            )),
            // propagation to the defined variable if rhs is a constant
            TypedStatement::Definition(TypedAssignee::Identifier(var), expr) => {
                let expr = self.fold_expression(expr);

                if is_constant(&expr) {
                    self.constants
                        .insert(TypedAssignee::Identifier(var.clone()), expr.clone());
                    match self.verbose {
                        true => Some(TypedStatement::Definition(
                            TypedAssignee::Identifier(var),
                            expr,
                        )),
                        false => None,
                    }
                } else {
                    Some(TypedStatement::Definition(
                        TypedAssignee::Identifier(var),
                        expr,
                    ))
                }
            }
            TypedStatement::Definition(TypedAssignee::Select(..), _) => {
                unreachable!("array updates should have been replaced with full array redef")
            }
            TypedStatement::Definition(TypedAssignee::Member(..), _) => {
                unreachable!("struct update should have been replaced with full struct redef")
            }
            // propagate lhs and rhs for conditions
            TypedStatement::Condition(e1, e2) => {
                // could stop execution here if condition is known to fail
                Some(TypedStatement::Condition(
                    self.fold_expression(e1),
                    self.fold_expression(e2),
                ))
            }
            // only loops with variable bounds are expected here
            // we stop propagation here as constants maybe be modified inside the loop body
            // which we do not visit
            TypedStatement::For(v, from, to, statements) => {
                let from = self.fold_field_expression(from);
                let to = self.fold_field_expression(to);

                // invalidate the constants map as any constant could be modified inside the loop body, which we don't visit
                self.constants.clear();

                Some(TypedStatement::For(v, from, to, statements))
            }
            TypedStatement::MultipleDefinition(variables, expression_list) => {
                let expression_list = self.fold_expression_list(expression_list);
                Some(TypedStatement::MultipleDefinition(
                    variables,
                    expression_list,
                ))
            }
        };

        // In verbose mode, we always return a statement
        assert!(res.is_some() || !self.verbose);

        match res {
            Some(v) => vec![v],
            None => vec![],
        }
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> FieldElementExpression<'ast, T> {
        match e {
            FieldElementExpression::Identifier(id) => {
                match self
                    .constants
                    .get(&TypedAssignee::Identifier(Variable::field_element(
                        id.clone(),
                    ))) {
                    Some(e) => match e {
                        TypedExpression::FieldElement(e) => e.clone(),
                        _ => unreachable!(
                            "constant stored for a field element should be a field element"
                        ),
                    },
                    None => FieldElementExpression::Identifier(id),
                }
            }
            FieldElementExpression::Add(box e1, box e2) => match (
                self.fold_field_expression(e1),
                self.fold_field_expression(e2),
            ) {
                (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                    FieldElementExpression::Number(n1 + n2)
                }
                (e1, e2) => FieldElementExpression::Add(box e1, box e2),
            },
            FieldElementExpression::Sub(box e1, box e2) => match (
                self.fold_field_expression(e1),
                self.fold_field_expression(e2),
            ) {
                (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                    FieldElementExpression::Number(n1 - n2)
                }
                (e1, e2) => FieldElementExpression::Sub(box e1, box e2),
            },
            FieldElementExpression::Mult(box e1, box e2) => match (
                self.fold_field_expression(e1),
                self.fold_field_expression(e2),
            ) {
                (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                    FieldElementExpression::Number(n1 * n2)
                }
                (e1, e2) => FieldElementExpression::Mult(box e1, box e2),
            },
            FieldElementExpression::Div(box e1, box e2) => match (
                self.fold_field_expression(e1),
                self.fold_field_expression(e2),
            ) {
                (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                    FieldElementExpression::Number(n1 / n2)
                }
                (e1, e2) => FieldElementExpression::Div(box e1, box e2),
            },
            FieldElementExpression::Pow(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1);
                let e2 = self.fold_field_expression(e2);
                match (e1, e2) {
                    (_, FieldElementExpression::Number(ref n2)) if *n2 == T::from(0) => {
                        FieldElementExpression::Number(T::from(1))
                    }
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        FieldElementExpression::Number(n1.pow(n2))
                    }
                    (e1, FieldElementExpression::Number(n2)) => {
                        FieldElementExpression::Pow(box e1, box FieldElementExpression::Number(n2))
                    }
                    (_, e2) => unreachable!(format!(
                        "non-constant exponent {} detected during static analysis",
                        e2
                    )),
                }
            }
            FieldElementExpression::IfElse(box condition, box consequence, box alternative) => {
                let consequence = self.fold_field_expression(consequence);
                let alternative = self.fold_field_expression(alternative);
                match self.fold_boolean_expression(condition) {
                    BooleanExpression::Value(true) => consequence,
                    BooleanExpression::Value(false) => alternative,
                    c => FieldElementExpression::IfElse(box c, box consequence, box alternative),
                }
            }
            FieldElementExpression::Select(box array, box index) => {
                let array = self.fold_array_expression(array);
                let index = self.fold_field_expression(index);

                let inner_type = array.inner_type().clone();
                let size = array.size();

                match (array.into_inner(), index) {
                    (ArrayExpressionInner::Value(v), FieldElementExpression::Number(n)) => {
                        let n_as_usize = n.to_dec_string().parse::<usize>().unwrap();
                        if n_as_usize < size {
                            FieldElementExpression::try_from(v[n_as_usize].clone()).unwrap()
                        } else {
                            unreachable!(
                                "out of bounds index ({} >= {}) found during static analysis",
                                n_as_usize, size
                            );
                        }
                    }
                    (ArrayExpressionInner::Identifier(id), FieldElementExpression::Number(n)) => {
                        match self.constants.get(&TypedAssignee::Select(
                            box TypedAssignee::Identifier(Variable::array(
                                id.clone(),
                                inner_type.clone(),
                                size,
                            )),
                            box FieldElementExpression::Number(n.clone()).into(),
                        )) {
                            Some(e) => match e {
                                TypedExpression::FieldElement(e) => e.clone(),
                                _ => unreachable!(""),
                            },
                            None => FieldElementExpression::Select(
                                box ArrayExpressionInner::Identifier(id).annotate(inner_type, size),
                                box FieldElementExpression::Number(n),
                            ),
                        }
                    }
                    (a, i) => {
                        FieldElementExpression::Select(box a.annotate(inner_type, size), box i)
                    }
                }
            }
            FieldElementExpression::Member(box s, m) => {
                let s = self.fold_struct_expression(s);

                let members = match s.get_type() {
                    Type::Struct(members) => members,
                    _ => unreachable!(),
                };

                match s.into_inner() {
                    StructExpressionInner::Value(v) => {
                        match members
                            .iter()
                            .zip(v)
                            .find(|(member, _)| member.id == m)
                            .unwrap()
                            .1
                        {
                            TypedExpression::FieldElement(s) => s,
                            _ => unreachable!(),
                        }
                    }
                    inner => FieldElementExpression::Member(box inner.annotate(members), m),
                }
            }
            e => fold_field_expression(self, e),
        }
    }

    fn fold_array_expression_inner(
        &mut self,
        ty: &Type,
        size: usize,
        e: ArrayExpressionInner<'ast, T>,
    ) -> ArrayExpressionInner<'ast, T> {
        match e {
            ArrayExpressionInner::Identifier(id) => {
                match self
                    .constants
                    .get(&TypedAssignee::Identifier(Variable::array(
                        id.clone(),
                        ty.clone(),
                        size,
                    ))) {
                    Some(e) => match e {
                        TypedExpression::Array(e) => e.as_inner().clone(),
                        _ => panic!("constant stored for an array should be an array"),
                    },
                    None => ArrayExpressionInner::Identifier(id),
                }
            }
            ArrayExpressionInner::Select(box array, box index) => {
                let array = self.fold_array_expression(array);
                let index = self.fold_field_expression(index);

                let inner_type = array.inner_type().clone();
                let size = array.size();

                match (array.into_inner(), index) {
                    (ArrayExpressionInner::Value(v), FieldElementExpression::Number(n)) => {
                        let n_as_usize = n.to_dec_string().parse::<usize>().unwrap();
                        if n_as_usize < size {
                            ArrayExpression::try_from(v[n_as_usize].clone())
                                .unwrap()
                                .into_inner()
                        } else {
                            unreachable!(
                                "out of bounds index ({} >= {}) found during static analysis",
                                n_as_usize, size
                            );
                        }
                    }
                    (ArrayExpressionInner::Identifier(id), FieldElementExpression::Number(n)) => {
                        match self.constants.get(&TypedAssignee::Select(
                            box TypedAssignee::Identifier(Variable::array(
                                id.clone(),
                                inner_type.clone(),
                                size,
                            )),
                            box FieldElementExpression::Number(n.clone()).into(),
                        )) {
                            Some(e) => match e {
                                TypedExpression::Array(e) => e.clone().into_inner(),
                                _ => unreachable!(""),
                            },
                            None => ArrayExpressionInner::Select(
                                box ArrayExpressionInner::Identifier(id).annotate(inner_type, size),
                                box FieldElementExpression::Number(n),
                            ),
                        }
                    }
                    (a, i) => ArrayExpressionInner::Select(box a.annotate(inner_type, size), box i),
                }
            }
            ArrayExpressionInner::IfElse(box condition, box consequence, box alternative) => {
                let consequence = self.fold_array_expression(consequence);
                let alternative = self.fold_array_expression(alternative);
                match self.fold_boolean_expression(condition) {
                    BooleanExpression::Value(true) => consequence.into_inner(),
                    BooleanExpression::Value(false) => alternative.into_inner(),
                    c => ArrayExpressionInner::IfElse(box c, box consequence, box alternative),
                }
            }
            ArrayExpressionInner::Member(box s, m) => {
                let s = self.fold_struct_expression(s);

                let members = match s.get_type() {
                    Type::Struct(members) => members,
                    _ => unreachable!(),
                };

                match s.into_inner() {
                    StructExpressionInner::Value(v) => {
                        match members
                            .iter()
                            .zip(v)
                            .find(|(member, _)| member.id == m)
                            .unwrap()
                            .1
                        {
                            TypedExpression::Array(a) => a.into_inner(),
                            _ => unreachable!(),
                        }
                    }
                    inner => ArrayExpressionInner::Member(box inner.annotate(members), m),
                }
            }
            e => fold_array_expression_inner(self, ty, size, e),
        }
    }

    fn fold_struct_expression_inner(
        &mut self,
        ty: &Vec<StructMember>,
        e: StructExpressionInner<'ast, T>,
    ) -> StructExpressionInner<'ast, T> {
        match e {
            StructExpressionInner::Identifier(id) => {
                match self
                    .constants
                    .get(&TypedAssignee::Identifier(Variable::struc(
                        id.clone(),
                        ty.clone(),
                    ))) {
                    Some(e) => match e {
                        TypedExpression::Struct(e) => e.as_inner().clone(),
                        _ => panic!("constant stored for an array should be an array"),
                    },
                    None => StructExpressionInner::Identifier(id),
                }
            }
            StructExpressionInner::Select(box array, box index) => {
                let array = self.fold_array_expression(array);
                let index = self.fold_field_expression(index);

                let inner_type = array.inner_type().clone();
                let size = array.size();

                match (array.into_inner(), index) {
                    (ArrayExpressionInner::Value(v), FieldElementExpression::Number(n)) => {
                        let n_as_usize = n.to_dec_string().parse::<usize>().unwrap();
                        if n_as_usize < size {
                            StructExpression::try_from(v[n_as_usize].clone())
                                .unwrap()
                                .into_inner()
                        } else {
                            unreachable!(
                                "out of bounds index ({} >= {}) found during static analysis",
                                n_as_usize, size
                            );
                        }
                    }
                    (ArrayExpressionInner::Identifier(id), FieldElementExpression::Number(n)) => {
                        match self.constants.get(&TypedAssignee::Select(
                            box TypedAssignee::Identifier(Variable::array(
                                id.clone(),
                                inner_type.clone(),
                                size,
                            )),
                            box FieldElementExpression::Number(n.clone()).into(),
                        )) {
                            Some(e) => match e {
                                TypedExpression::Struct(e) => e.clone().into_inner(),
                                _ => unreachable!(""),
                            },
                            None => StructExpressionInner::Select(
                                box ArrayExpressionInner::Identifier(id).annotate(inner_type, size),
                                box FieldElementExpression::Number(n),
                            ),
                        }
                    }
                    (a, i) => {
                        StructExpressionInner::Select(box a.annotate(inner_type, size), box i)
                    }
                }
            }
            StructExpressionInner::IfElse(box condition, box consequence, box alternative) => {
                let consequence = self.fold_struct_expression(consequence);
                let alternative = self.fold_struct_expression(alternative);
                match self.fold_boolean_expression(condition) {
                    BooleanExpression::Value(true) => consequence.into_inner(),
                    BooleanExpression::Value(false) => alternative.into_inner(),
                    c => StructExpressionInner::IfElse(box c, box consequence, box alternative),
                }
            }
            StructExpressionInner::Member(box s, m) => {
                let s = self.fold_struct_expression(s);

                let members = match s.get_type() {
                    Type::Struct(members) => members,
                    _ => unreachable!(),
                };

                match s.into_inner() {
                    StructExpressionInner::Value(v) => {
                        match members
                            .iter()
                            .zip(v)
                            .find(|(member, _)| member.id == m)
                            .unwrap()
                            .1
                        {
                            TypedExpression::Struct(s) => s.into_inner(),
                            _ => unreachable!(),
                        }
                    }
                    inner => StructExpressionInner::Member(box inner.annotate(members), m),
                }
            }
            e => fold_struct_expression_inner(self, ty, e),
        }
    }

    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> BooleanExpression<'ast, T> {
        match e {
            BooleanExpression::Identifier(id) => match self
                .constants
                .get(&TypedAssignee::Identifier(Variable::boolean(id.clone())))
            {
                Some(e) => match e {
                    TypedExpression::Boolean(e) => e.clone(),
                    _ => panic!("constant stored for a boolean should be a boolean"),
                },
                None => BooleanExpression::Identifier(id),
            },
            BooleanExpression::FieldEq(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1);
                let e2 = self.fold_field_expression(e2);

                match (e1, e2) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        BooleanExpression::Value(n1 == n2)
                    }
                    (e1, e2) => BooleanExpression::FieldEq(box e1, box e2),
                }
            }
            BooleanExpression::BoolEq(box e1, box e2) => {
                let e1 = self.fold_boolean_expression(e1);
                let e2 = self.fold_boolean_expression(e2);

                match (e1, e2) {
                    (BooleanExpression::Value(n1), BooleanExpression::Value(n2)) => {
                        BooleanExpression::Value(n1 == n2)
                    }
                    (e1, e2) => BooleanExpression::BoolEq(box e1, box e2),
                }
            }
            BooleanExpression::Lt(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1);
                let e2 = self.fold_field_expression(e2);

                match (e1, e2) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        BooleanExpression::Value(n1 < n2)
                    }
                    (e1, e2) => BooleanExpression::Lt(box e1, box e2),
                }
            }
            BooleanExpression::Le(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1);
                let e2 = self.fold_field_expression(e2);

                match (e1, e2) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        BooleanExpression::Value(n1 <= n2)
                    }
                    (e1, e2) => BooleanExpression::Le(box e1, box e2),
                }
            }
            BooleanExpression::Gt(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1);
                let e2 = self.fold_field_expression(e2);

                match (e1, e2) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        BooleanExpression::Value(n1 > n2)
                    }
                    (e1, e2) => BooleanExpression::Gt(box e1, box e2),
                }
            }
            BooleanExpression::Ge(box e1, box e2) => {
                let e1 = self.fold_field_expression(e1);
                let e2 = self.fold_field_expression(e2);

                match (e1, e2) {
                    (FieldElementExpression::Number(n1), FieldElementExpression::Number(n2)) => {
                        BooleanExpression::Value(n1 >= n2)
                    }
                    (e1, e2) => BooleanExpression::Ge(box e1, box e2),
                }
            }
            BooleanExpression::Or(box e1, box e2) => {
                let e1 = self.fold_boolean_expression(e1);
                let e2 = self.fold_boolean_expression(e2);

                match (e1, e2) {
                    // reduction of constants
                    (BooleanExpression::Value(v1), BooleanExpression::Value(v2)) => {
                        BooleanExpression::Value(v1 || v2)
                    }
                    // x || true == true
                    (_, BooleanExpression::Value(true)) | (BooleanExpression::Value(true), _) => {
                        BooleanExpression::Value(true)
                    }
                    // x || false == x
                    (e, BooleanExpression::Value(false)) | (BooleanExpression::Value(false), e) => {
                        e
                    }
                    (e1, e2) => BooleanExpression::Or(box e1, box e2),
                }
            }
            BooleanExpression::And(box e1, box e2) => {
                let e1 = self.fold_boolean_expression(e1);
                let e2 = self.fold_boolean_expression(e2);

                match (e1, e2) {
                    // reduction of constants
                    (BooleanExpression::Value(v1), BooleanExpression::Value(v2)) => {
                        BooleanExpression::Value(v1 && v2)
                    }
                    // x && true == x
                    (e, BooleanExpression::Value(true)) | (BooleanExpression::Value(true), e) => e,
                    // x && false == false
                    (_, BooleanExpression::Value(false)) | (BooleanExpression::Value(false), _) => {
                        BooleanExpression::Value(false)
                    }
                    (e1, e2) => BooleanExpression::And(box e1, box e2),
                }
            }
            BooleanExpression::Not(box e) => {
                let e = self.fold_boolean_expression(e);
                match e {
                    BooleanExpression::Value(v) => BooleanExpression::Value(!v),
                    e => BooleanExpression::Not(box e),
                }
            }
            BooleanExpression::IfElse(box condition, box consequence, box alternative) => {
                let consequence = self.fold_boolean_expression(consequence);
                let alternative = self.fold_boolean_expression(alternative);
                match self.fold_boolean_expression(condition) {
                    BooleanExpression::Value(true) => consequence,
                    BooleanExpression::Value(false) => alternative,
                    c => BooleanExpression::IfElse(box c, box consequence, box alternative),
                }
            }
            BooleanExpression::Member(box s, m) => {
                let s = self.fold_struct_expression(s);

                let members = match s.get_type() {
                    Type::Struct(members) => members,
                    _ => unreachable!(),
                };

                match s.into_inner() {
                    StructExpressionInner::Value(v) => {
                        match members
                            .iter()
                            .zip(v)
                            .find(|(member, _)| member.id == m)
                            .unwrap()
                            .1
                        {
                            TypedExpression::Boolean(s) => s,
                            _ => unreachable!(),
                        }
                    }
                    inner => BooleanExpression::Member(box inner.annotate(members), m),
                }
            }
            e => fold_boolean_expression(self, e),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    #[cfg(test)]
    mod expression {
        use super::*;

        #[cfg(test)]
        mod field {
            use super::*;

            #[test]
            fn add() {
                let e = FieldElementExpression::Add(
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                    box FieldElementExpression::Number(FieldPrime::from(3)),
                );

                assert_eq!(
                    Propagator::new().fold_field_expression(e),
                    FieldElementExpression::Number(FieldPrime::from(5))
                );
            }

            #[test]
            fn sub() {
                let e = FieldElementExpression::Sub(
                    box FieldElementExpression::Number(FieldPrime::from(3)),
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                );

                assert_eq!(
                    Propagator::new().fold_field_expression(e),
                    FieldElementExpression::Number(FieldPrime::from(1))
                );
            }

            #[test]
            fn mult() {
                let e = FieldElementExpression::Mult(
                    box FieldElementExpression::Number(FieldPrime::from(3)),
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                );

                assert_eq!(
                    Propagator::new().fold_field_expression(e),
                    FieldElementExpression::Number(FieldPrime::from(6))
                );
            }

            #[test]
            fn div() {
                let e = FieldElementExpression::Div(
                    box FieldElementExpression::Number(FieldPrime::from(6)),
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                );

                assert_eq!(
                    Propagator::new().fold_field_expression(e),
                    FieldElementExpression::Number(FieldPrime::from(3))
                );
            }

            #[test]
            fn pow() {
                let e = FieldElementExpression::Pow(
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                    box FieldElementExpression::Number(FieldPrime::from(3)),
                );

                assert_eq!(
                    Propagator::new().fold_field_expression(e),
                    FieldElementExpression::Number(FieldPrime::from(8))
                );
            }

            #[test]
            fn if_else_true() {
                let e = FieldElementExpression::IfElse(
                    box BooleanExpression::Value(true),
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                    box FieldElementExpression::Number(FieldPrime::from(3)),
                );

                assert_eq!(
                    Propagator::new().fold_field_expression(e),
                    FieldElementExpression::Number(FieldPrime::from(2))
                );
            }

            #[test]
            fn if_else_false() {
                let e = FieldElementExpression::IfElse(
                    box BooleanExpression::Value(false),
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                    box FieldElementExpression::Number(FieldPrime::from(3)),
                );

                assert_eq!(
                    Propagator::new().fold_field_expression(e),
                    FieldElementExpression::Number(FieldPrime::from(3))
                );
            }

            #[test]
            fn select() {
                let e = FieldElementExpression::Select(
                    box ArrayExpressionInner::Value(vec![
                        FieldElementExpression::Number(FieldPrime::from(1)).into(),
                        FieldElementExpression::Number(FieldPrime::from(2)).into(),
                        FieldElementExpression::Number(FieldPrime::from(3)).into(),
                    ])
                    .annotate(Type::FieldElement, 3),
                    box FieldElementExpression::Add(
                        box FieldElementExpression::Number(FieldPrime::from(1)),
                        box FieldElementExpression::Number(FieldPrime::from(1)),
                    ),
                );

                assert_eq!(
                    Propagator::new().fold_field_expression(e),
                    FieldElementExpression::Number(FieldPrime::from(3))
                );
            }
        }

        #[cfg(test)]
        mod boolean {
            use super::*;

            #[test]
            fn not() {
                let e_true: BooleanExpression<FieldPrime> =
                    BooleanExpression::Not(box BooleanExpression::Value(false));

                let e_false: BooleanExpression<FieldPrime> =
                    BooleanExpression::Not(box BooleanExpression::Value(true));

                let e_default: BooleanExpression<FieldPrime> =
                    BooleanExpression::Not(box BooleanExpression::Identifier("a".into()));

                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_true),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_false),
                    BooleanExpression::Value(false)
                );
                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_default.clone()),
                    e_default
                );
            }

            #[test]
            fn field_eq() {
                let e_true = BooleanExpression::FieldEq(
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                );

                let e_false = BooleanExpression::FieldEq(
                    box FieldElementExpression::Number(FieldPrime::from(4)),
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                );

                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_true),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_false),
                    BooleanExpression::Value(false)
                );
            }

            #[test]
            fn bool_eq() {
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(
                        BooleanExpression::BoolEq(
                            box BooleanExpression::Value(false),
                            box BooleanExpression::Value(false)
                        )
                    ),
                    BooleanExpression::Value(true)
                );

                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(
                        BooleanExpression::BoolEq(
                            box BooleanExpression::Value(true),
                            box BooleanExpression::Value(true)
                        )
                    ),
                    BooleanExpression::Value(true)
                );

                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(
                        BooleanExpression::BoolEq(
                            box BooleanExpression::Value(true),
                            box BooleanExpression::Value(false)
                        )
                    ),
                    BooleanExpression::Value(false)
                );

                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(
                        BooleanExpression::BoolEq(
                            box BooleanExpression::Value(false),
                            box BooleanExpression::Value(true)
                        )
                    ),
                    BooleanExpression::Value(false)
                );
            }

            #[test]
            fn lt() {
                let e_true = BooleanExpression::Lt(
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                    box FieldElementExpression::Number(FieldPrime::from(4)),
                );

                let e_false = BooleanExpression::Lt(
                    box FieldElementExpression::Number(FieldPrime::from(4)),
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                );

                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_true),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_false),
                    BooleanExpression::Value(false)
                );
            }

            #[test]
            fn le() {
                let e_true = BooleanExpression::Le(
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                );

                let e_false = BooleanExpression::Le(
                    box FieldElementExpression::Number(FieldPrime::from(4)),
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                );

                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_true),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_false),
                    BooleanExpression::Value(false)
                );
            }

            #[test]
            fn gt() {
                let e_true = BooleanExpression::Gt(
                    box FieldElementExpression::Number(FieldPrime::from(5)),
                    box FieldElementExpression::Number(FieldPrime::from(4)),
                );

                let e_false = BooleanExpression::Gt(
                    box FieldElementExpression::Number(FieldPrime::from(4)),
                    box FieldElementExpression::Number(FieldPrime::from(5)),
                );

                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_true),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_false),
                    BooleanExpression::Value(false)
                );
            }

            #[test]
            fn ge() {
                let e_true = BooleanExpression::Ge(
                    box FieldElementExpression::Number(FieldPrime::from(5)),
                    box FieldElementExpression::Number(FieldPrime::from(5)),
                );

                let e_false = BooleanExpression::Ge(
                    box FieldElementExpression::Number(FieldPrime::from(4)),
                    box FieldElementExpression::Number(FieldPrime::from(5)),
                );

                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_true),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::new().fold_boolean_expression(e_false),
                    BooleanExpression::Value(false)
                );
            }

            #[test]
            fn and() {
                let a_bool: Identifier = "a".into();

                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(
                        BooleanExpression::And(
                            box BooleanExpression::Value(true),
                            box BooleanExpression::Identifier(a_bool.clone())
                        )
                    ),
                    BooleanExpression::Identifier(a_bool.clone())
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(
                        BooleanExpression::And(
                            box BooleanExpression::Identifier(a_bool.clone()),
                            box BooleanExpression::Value(true),
                        )
                    ),
                    BooleanExpression::Identifier(a_bool.clone())
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(
                        BooleanExpression::And(
                            box BooleanExpression::Value(false),
                            box BooleanExpression::Identifier(a_bool.clone())
                        )
                    ),
                    BooleanExpression::Value(false)
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(
                        BooleanExpression::And(
                            box BooleanExpression::Identifier(a_bool.clone()),
                            box BooleanExpression::Value(false),
                        )
                    ),
                    BooleanExpression::Value(false)
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(
                        BooleanExpression::And(
                            box BooleanExpression::Value(true),
                            box BooleanExpression::Value(false),
                        )
                    ),
                    BooleanExpression::Value(false)
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(
                        BooleanExpression::And(
                            box BooleanExpression::Value(false),
                            box BooleanExpression::Value(true),
                        )
                    ),
                    BooleanExpression::Value(false)
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(
                        BooleanExpression::And(
                            box BooleanExpression::Value(true),
                            box BooleanExpression::Value(true),
                        )
                    ),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(
                        BooleanExpression::And(
                            box BooleanExpression::Value(false),
                            box BooleanExpression::Value(false),
                        )
                    ),
                    BooleanExpression::Value(false)
                );
            }

            #[test]
            fn or() {
                let a_bool: Identifier = "a".into();

                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(BooleanExpression::Or(
                        box BooleanExpression::Value(true),
                        box BooleanExpression::Identifier(a_bool.clone())
                    )),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(BooleanExpression::Or(
                        box BooleanExpression::Identifier(a_bool.clone()),
                        box BooleanExpression::Value(true),
                    )),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(BooleanExpression::Or(
                        box BooleanExpression::Value(false),
                        box BooleanExpression::Identifier(a_bool.clone())
                    )),
                    BooleanExpression::Identifier(a_bool.clone())
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(BooleanExpression::Or(
                        box BooleanExpression::Identifier(a_bool.clone()),
                        box BooleanExpression::Value(false),
                    )),
                    BooleanExpression::Identifier(a_bool.clone())
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(BooleanExpression::Or(
                        box BooleanExpression::Value(true),
                        box BooleanExpression::Value(false),
                    )),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(BooleanExpression::Or(
                        box BooleanExpression::Value(false),
                        box BooleanExpression::Value(true),
                    )),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(BooleanExpression::Or(
                        box BooleanExpression::Value(true),
                        box BooleanExpression::Value(true),
                    )),
                    BooleanExpression::Value(true)
                );
                assert_eq!(
                    Propagator::<FieldPrime>::new().fold_boolean_expression(BooleanExpression::Or(
                        box BooleanExpression::Value(false),
                        box BooleanExpression::Value(false),
                    )),
                    BooleanExpression::Value(false)
                );
            }
        }
    }
}
