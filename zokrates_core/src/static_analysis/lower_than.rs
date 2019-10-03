//! Module containing lower equal comparison of field elements
//!
//! @file lower_than.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @author Stefan Deml <stefandeml@gmail.com>
//! @date 2019

//! ## Algorithm Description:
//! Field elements `a,b` that are to be compared: `a<b`?
//! 
//! 1. Decomposition of `a`
//!     1. Declare 254 variables for the bit-representation of `a` and call directive 
//!        to assign bits in big-endian 
//!     2. Check that all variables that were assigned are Booelan, hence 1 or 0 
//!     3. Check that the two most significant bits are false (reason see below)
//!     4. Check that the decomposition is correct
//!         - sum = $\sum a_{bits}[i]*2^{i}$
//!         - assert(a == sum)
//!         
//! 2. Decomposition of `b` (same as `a`)
//!  
//! 3. Compute $d = 2*a-2*b$. 
//!     Intuition behind this: 
//!     -   $a,b$ are smaller $p/2$, since $p/2$ has 254 bits and a,b have 252 bits
//!     -   Hence:  
//! ```                             
//!              ** < p/2, a>=b 
//!   c = (a-b) *                
//!              ** > p/2, b>a   
//! ```          
//!    - If we multiply $c$ by 2, i.e. $d=2c=2a-2b$, we will overflow in the field 
//!      for values of $c > p/2$ and not overflow for values of $c < p/2$. 
//!    - Values of `d` where no overflow occured will be even, whereas an overflow 
//!      (causes  $a \, mod \, p$ operation) will be odd.
//!    - We can observe whether `d` is odd or even looking at `d`'s lowest bit: 
//! ```
//!                      ** 0, a>=b 
//!   d[bitwidth(p)-1] *                
//!                      ** > p/2, b>a 
//! ```     
//! 4. Decomposition of d
//!    1. Declare 254 variables for the bit-representation of `d` and call directive to 
//!       assign bits in big-endian 
//!     2. Check that all variables that were assigned are Booelan, hence 1 or 0 
//!     3. Check that the decomposition is correct
//!         - sum = $\sum d_{bits}[i]*2^{i}$
//!         - assert(d == sum)
//!     4. As we can overflow in the field, some values would not have a deterministic binary
//!        representation.  Hence we also require that the representation
//!        strictly exists "in the field" (i.e., a congruency is not allowed.)
//! 
//! 6. Return $d_{bits}[bitwidth(p)-1]$

use crate::typed_absy::folder::*;
use crate::typed_absy::*;
use types::{FunctionKey, Signature, Type};
use zokrates_field::field::Field;

pub struct LowerThan<'ast, T: Field> {
    statements: Vec<TypedStatement<'ast, T>>,
    counter: usize,
}

impl<'ast, T: Field> LowerThan<'ast, T> {
    fn new() -> Self {
        LowerThan {
            statements: vec![],
            counter: 0,
        }
    }

    pub fn reduce(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        LowerThan::new().fold_program(p)
    }

    // Compute $d = 2*a-2*b$ 
    fn compute_2diff(
        &mut self,
        left: FieldElementExpression<'ast, T>,
        right: FieldElementExpression<'ast, T>,
    ) -> ArrayExpression<'ast, T> {
        let left_bits = Identifier::internal("left_bits", self.counter);
        let right_bits = Identifier::internal("right_bits", self.counter);
        let diff_bits = Identifier::internal("diff_bits", self.counter);

        self.statements.extend(vec![
            // Decomposition of `a`
            TypedStatement::MultipleDefinition(
                vec![Variable::array(
                    left_bits.clone(),
                    Type::Boolean,
                    T::get_required_bits(),
                )],
                TypedExpressionList::FunctionCall(
                    FunctionKey::with_id("_UNPACK").signature(
                        Signature::new()
                            .inputs(vec![Type::FieldElement])
                            .outputs(vec![Type::array(Type::Boolean, T::get_required_bits())]),
                    ),
                    vec![left.clone().into()],
                    vec![Type::array(Type::Boolean, T::get_required_bits())],
                ),
            ),
            
            // Check that most significant bit is false
            TypedStatement::Condition(
                BooleanExpression::Select(
                    box ArrayExpressionInner::Identifier(left_bits.clone())
                        .annotate(Type::Boolean, T::get_required_bits()),
                    box FieldElementExpression::Number(T::from(0)),
                )
                .into(),
                BooleanExpression::Value(false).into(),
            ),

            // Check that second most significant bit is false
            TypedStatement::Condition(
                BooleanExpression::Select(
                    box ArrayExpressionInner::Identifier(left_bits.clone())
                        .annotate(Type::Boolean, T::get_required_bits()),
                    box FieldElementExpression::Number(T::from(1)),
                )
                .into(),
                BooleanExpression::Value(false).into(),
            ),
            TypedStatement::MultipleDefinition(
                vec![Variable::array(
                    right_bits.clone(),
                    Type::Boolean,
                    T::get_required_bits(),
                )],
                TypedExpressionList::FunctionCall(
                    FunctionKey::with_id("_UNPACK").signature(
                        Signature::new()
                            .inputs(vec![Type::FieldElement])
                            .outputs(vec![Type::array(Type::Boolean, T::get_required_bits())]),
                    ),
                    vec![right.clone().into()],
                    vec![Type::array(Type::Boolean, T::get_required_bits())],
                ),
            ),
            TypedStatement::Condition(
                BooleanExpression::Select(
                    box ArrayExpressionInner::Identifier(right_bits.clone())
                        .annotate(Type::Boolean, T::get_required_bits()),
                    box FieldElementExpression::Number(T::from(0)),
                )
                .into(),
                BooleanExpression::Value(false).into(),
            ),
            TypedStatement::Condition(
                BooleanExpression::Select(
                    box ArrayExpressionInner::Identifier(right_bits.clone())
                        .annotate(Type::Boolean, T::get_required_bits()),
                    box FieldElementExpression::Number(T::from(1)),
                )
                .into(),
                BooleanExpression::Value(false).into(),
            ),

            // Decomposition of $2a - 2b$ 
            TypedStatement::MultipleDefinition(
                vec![Variable::array(
                    diff_bits.clone(),
                    Type::Boolean,
                    T::get_required_bits(),
                )],
                TypedExpressionList::FunctionCall(
                    FunctionKey::with_id("_UNPACK").signature(
                        Signature::new()
                            .inputs(vec![Type::FieldElement])
                            .outputs(vec![Type::array(Type::Boolean, T::get_required_bits())]),
                    ),
                    // 2a - 2b
                    vec![FieldElementExpression::Sub(
                        box FieldElementExpression::Mult(
                            box left,
                            box FieldElementExpression::Number(T::from(2)),
                        ),
                        box FieldElementExpression::Mult(
                            box right,
                            box FieldElementExpression::Number(T::from(2)),
                        ),
                    )
                    .into()],
                    vec![Type::array(Type::Boolean, T::get_required_bits())],
                ),
            ),
        ]);
        ArrayExpressionInner::Identifier(diff_bits.clone())
            .annotate(Type::Boolean, T::get_required_bits())
    }

    // Let's assume b = [1, 1, 1, 0]
    // 
    // 1. Init `sizeUnknown = true`
    //    As long as `sizeUnknown` is `true` we don't yet know if a is <= than b. 
    // 2. Loop over `b`:
    //     * b[0] = 1 
    //       when `b` is 1 we check wether `a` is 0 in that particular run and update
    //       `sizeUnknown` accordingly:
    //       `sizeUnknown = sizeUnknown && a[0]`
    //     * b[1] = 1 
    //       `sizrUnknown = sizeUnknown && a[1]`
    //     * b[2] = 1 
    //       `sizeUnknown = sizeUnknown && a[2]`
    //     * b[3] = 0 
    //       we need to enforce that `a` is 0 in case `sizeUnknown`is still `true`,
    //       otherwise `a` can be {0,1}:
    //      `true == (!sizeUnknown || !a[3])`
    //      ```
    //                     **true => a -> 0     
    //         sizeUnkown *                     
    //                     **false => a -> {0,1}
    //      ```
    fn strict_le_check(&mut self, b: &[bool], a: ArrayExpression<'ast, T>) {
        let len = b.len();
        assert_eq!(a.get_type(), Type::array(Type::Boolean, len));

        let mut is_not_smaller_run = vec![];
        let mut size_unknown = vec![];
        for _i in 0..len {
            is_not_smaller_run.push(Identifier::internal("isNotSmallerRun", self.counter));
            size_unknown.push(Identifier::internal("sizeUnknown", self.counter));
            self.counter += 1;
        }

        // init size_unknown = true
        self.statements.push(TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::boolean(size_unknown[0].clone())),
            TypedExpression::Boolean(BooleanExpression::Value(true)),
        ));

        for (i, b) in b.iter().enumerate() {
            if *b {
                self.statements.push(TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::boolean(is_not_smaller_run[i].clone())),
                    BooleanExpression::Select(
                        box a.clone(),
                        box FieldElementExpression::Number(T::from(i)),
                    )
                    .into(),
                ));

                // don't need to update size_unknown in the last round
                if i < len - 1 {
                    self.statements.push(TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::boolean(size_unknown[i + 1].clone())),
                        BooleanExpression::And(
                            box BooleanExpression::Identifier(
                                Variable::boolean(size_unknown[i].clone()).id,
                            ),
                            box BooleanExpression::Identifier(
                                Variable::boolean(is_not_smaller_run[i].clone()).id,
                            ),
                        )
                        .into(),
                    ));
                }
            } else {
                // don't need to update size_unknown in the last round
                if i < len - 1 {
                    self.statements.push(
                        // sizeUnknown is not changing in this case
                        // We sill have to assign the old value to the variable of the current run
                        // This trivial definition will later be removed by the optimiser
                        TypedStatement::Definition(
                            TypedAssignee::Identifier(Variable::boolean(
                                size_unknown[i + 1].clone(),
                            )),
                            BooleanExpression::Identifier(
                                Variable::boolean(size_unknown[i].clone()).id,
                            )
                            .into(),
                        ),
                    );
                }
                self.statements.push(TypedStatement::Condition(
                    TypedExpression::Boolean(BooleanExpression::Value(true)),
                    BooleanExpression::Or(
                        box BooleanExpression::Not(box BooleanExpression::Identifier(
                            Variable::boolean(size_unknown[i].clone()).id,
                        )),
                        box BooleanExpression::Not(box BooleanExpression::Select(
                            box a.clone(),
                            box FieldElementExpression::Number(T::from(i)),
                        )),
                    )
                    .into(),
                ));
            }
        }
    }
}
impl<'ast, T: Field> Folder<'ast, T> for LowerThan<'ast, T> {
    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> BooleanExpression<'ast, T> {
        match e {
            // swap
            BooleanExpression::Gt(box left, box right) => {
                self.fold_boolean_expression(BooleanExpression::Lt(box right, box left))
            }
            BooleanExpression::Ge(box left, box right) => {
                self.fold_boolean_expression(BooleanExpression::Le(box right, box left))
            }
            // reduce ´<=´ to ´< || ==´
            BooleanExpression::Le(box left, box right) => {
                self.fold_boolean_expression(BooleanExpression::Or(
                    box BooleanExpression::Lt(box left.clone(), box right.clone()),
                    box BooleanExpression::Eq(box left, box right),
                ))
            }
            BooleanExpression::Lt(box left, box right) => {
                let diff_bits = self.compute_2diff(left, right);

                self.statements.push(TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::array("a".into(), Type::Boolean, 4)),
                    ArrayExpressionInner::Value(vec![
                        BooleanExpression::Value(true).into(),
                        BooleanExpression::Value(true).into(),
                        BooleanExpression::Value(false).into(),
                        BooleanExpression::Value(true).into(),
                    ])
                    .annotate(Type::Boolean, 4)
                    .into(),
                ));


                // we need to check that the binary representation of `diff_bits` is
                // "in the field", hence we check if diff_ bits < p
                // We check diff_bits <= p - 1 
                // get max value of the field, p,  as big-endian bit vector
                let field_bits_be = T::max_value_bit_vector_be();
                // drop the two most significant bits (bitwidth of p is just 254 bits)
                let field_bits_be = &field_bits_be[2..];
                //TODO: !!! We need to subtract 1 here !!!
                self.strict_le_check(field_bits_be, diff_bits.clone());

                self.counter += 1;

                // return least significant bit to check for overflow
                BooleanExpression::Select(
                    box diff_bits,
                    box FieldElementExpression::Number(T::from(T::get_required_bits() - 1)),
                )
            }
            e => fold_boolean_expression(self, e),
        }
    }

    fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        let s = fold_statement(self, s);
        self.statements.drain(..).chain(s.into_iter()).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    // define boolean array:
    // self.statements.push(TypedStatement::Definition(
    //                 TypedAssignee::Identifier(Variable::array("a".into(), Type::Boolean, 4)),
    //                 ArrayExpressionInner::Value(vec![
    //                     BooleanExpression::Value(true).into(),
    //                     BooleanExpression::Value(true).into(),
    //                     BooleanExpression::Value(false).into(),
    //                     BooleanExpression::Value(true).into(),
    //                 ])
    //                 .annotate(Type::Boolean, 4)
    //                 .into(),
    //             ));

    // then different cases
    //    self.strict_le_check(
    //         vec![true, true, true, false],
    //         Variable::array("a".into(), Type::Boolean, 4).id.clone(),
    //     );
}
