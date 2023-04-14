//! Module containing the `Flattener` to process a program that is R1CS-able.
//!
//! @file flatten.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

mod utils;

use self::utils::flat_expression_from_bits;
use zokrates_ast::{
    common::{expressions::ValueExpression, Span},
    zir::{
        canonicalizer::ZirCanonicalizer, ConditionalExpression, Expr, Folder, SelectExpression,
        ShouldReduce, UMetadata, ZirAssemblyStatement, ZirExpressionList, ZirProgram,
    },
};
use zokrates_interpreter::Interpreter;

use std::collections::{
    hash_map::{Entry, HashMap},
    VecDeque,
};
use std::ops::*;
use zokrates_ast::common::embed::*;
use zokrates_ast::common::FlatEmbed;
use zokrates_ast::common::WithSpan;
use zokrates_ast::common::{flat::Variable, RuntimeError};
use zokrates_ast::flat::*;
use zokrates_ast::ir::Solver;
use zokrates_ast::zir::types::{Type, UBitwidth};
use zokrates_ast::zir::{
    BooleanExpression, Conditional, FieldElementExpression, Identifier, Parameter as ZirParameter,
    UExpression, UExpressionInner, Variable as ZirVariable, ZirExpression, ZirStatement,
};
use zokrates_common::CompileConfig;
use zokrates_field::Field;

/// A container for statements produced during code generation
/// New statements are registered with the span set in the container
#[derive(Default)]
pub struct FlatStatements<'ast, T> {
    span: Option<Span>,
    buffer: VecDeque<FlatStatement<'ast, T>>,
}

impl<'ast, T> FlatStatements<'ast, T> {
    fn push_back(&mut self, s: FlatStatement<'ast, T>) {
        self.buffer.push_back(s.span(self.span))
    }

    fn pop_front(&mut self) -> Option<FlatStatement<'ast, T>> {
        self.buffer.pop_front()
    }

    fn extend(&mut self, i: impl IntoIterator<Item = FlatStatement<'ast, T>>) {
        self.buffer.extend(i.into_iter().map(|s| s.span(self.span)))
    }

    fn set_span(&mut self, span: Option<Span>) {
        self.span = span;
    }

    fn is_empty(&self) -> bool {
        self.buffer.is_empty()
    }
}

impl<'ast, T> IntoIterator for FlatStatements<'ast, T> {
    type Item = FlatStatement<'ast, T>;

    type IntoIter = std::collections::vec_deque::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.buffer.into_iter()
    }
}

/// Flattens a function
///
/// # Arguments
/// * `funct` - `ZirFunction` that will be flattened
pub fn from_program_and_config<T: Field>(
    prog: ZirProgram<T>,
    config: CompileConfig,
) -> FlattenerIterator<T> {
    let funct = prog.main;

    let mut flattener = Flattener::new(config);
    let mut statements_flattened = FlatStatements::default();
    // push parameters
    let arguments_flattened = funct
        .arguments
        .into_iter()
        .map(|p| flattener.use_parameter(&p, &mut statements_flattened))
        .collect();

    FlattenerIterator {
        arguments: arguments_flattened,
        statements: FlattenerIteratorInner {
            statements: funct.statements.into(),
            statements_flattened,
            flattener,
        },
        return_count: funct.signature.outputs.len(),
        module_map: prog.module_map,
    }
}

pub struct FlattenerIteratorInner<'ast, T> {
    pub statements: VecDeque<ZirStatement<'ast, T>>,
    pub statements_flattened: FlatStatements<'ast, T>,
    pub flattener: Flattener<'ast, T>,
}

pub type FlattenerIterator<'ast, T> = FlatProgIterator<'ast, T, FlattenerIteratorInner<'ast, T>>;

impl<'ast, T: Field> Iterator for FlattenerIteratorInner<'ast, T> {
    type Item = FlatStatement<'ast, T>;

    fn next(&mut self) -> Option<Self::Item> {
        while self.statements_flattened.is_empty() {
            match self.statements.pop_front() {
                Some(s) => {
                    self.flattener
                        .flatten_statement(&mut self.statements_flattened, s);
                }
                None => {
                    break;
                }
            }
        }
        self.statements_flattened.pop_front()
    }
}

/// Flattener, computes flattened program.
#[derive(Debug)]
pub struct Flattener<'ast, T> {
    config: CompileConfig,
    /// Index of the next introduced variable while processing the program.
    next_var_idx: usize,
    /// `Variable`s corresponding to each `Identifier`
    layout: HashMap<Identifier<'ast>, Variable>,
    /// Cached bit decompositions to avoid re-generating them
    bits_cache: HashMap<FlatExpression<T>, Vec<FlatExpression<T>>>,
}

trait FlattenOutput<T: Field>: Sized {
    fn flat(self) -> FlatExpression<T>;
}

impl<T: Field> FlattenOutput<T> for FlatExpression<T> {
    fn flat(self) -> FlatExpression<T> {
        self
    }
}

impl<T: Field> FlattenOutput<T> for FlatUExpression<T> {
    fn flat(self) -> FlatExpression<T> {
        self.get_field_unchecked()
    }
}

// We introduce a trait in order to make it possible to make flattening `e` generic over the type of `e`

trait Flatten<'ast, T: Field>: From<ZirExpression<'ast, T>> + Conditional<'ast, T> {
    type Output: FlattenOutput<T>;

    fn flatten(
        self,
        flattener: &mut Flattener<'ast, T>,
        statements_flattened: &mut FlatStatements<'ast, T>,
    ) -> Self::Output;
}

impl<'ast, T: Field> Flatten<'ast, T> for FieldElementExpression<'ast, T> {
    type Output = FlatExpression<T>;

    fn flatten(
        self,
        flattener: &mut Flattener<'ast, T>,
        statements_flattened: &mut FlatStatements<'ast, T>,
    ) -> Self::Output {
        flattener.flatten_field_expression(statements_flattened, self)
    }
}

impl<'ast, T: Field> Flatten<'ast, T> for UExpression<'ast, T> {
    type Output = FlatUExpression<T>;

    fn flatten(
        self,
        flattener: &mut Flattener<'ast, T>,
        statements_flattened: &mut FlatStatements<'ast, T>,
    ) -> Self::Output {
        flattener.flatten_uint_expression(statements_flattened, self)
    }
}

impl<'ast, T: Field> Flatten<'ast, T> for BooleanExpression<'ast, T> {
    type Output = FlatExpression<T>;

    fn flatten(
        self,
        flattener: &mut Flattener<'ast, T>,
        statements_flattened: &mut FlatStatements<'ast, T>,
    ) -> Self::Output {
        flattener.flatten_boolean_expression(statements_flattened, self)
    }
}

#[derive(Clone, Debug)]
struct FlatUExpression<T> {
    field: Option<FlatExpression<T>>,
    bits: Option<Vec<FlatExpression<T>>>,
}

impl<T> WithSpan for FlatUExpression<T> {
    fn span(self, span: Option<Span>) -> Self {
        Self {
            field: self.field.map(|e| e.span(span)),
            bits: self
                .bits
                .map(|bits| bits.into_iter().map(|b| b.span(span)).collect()),
        }
    }

    fn get_span(&self) -> Option<Span> {
        let field_span = self.field.as_ref().map(|f| f.get_span());
        field_span.unwrap_or_else(|| unimplemented!())
    }
}

impl<T> FlatUExpression<T> {
    fn default() -> Self {
        FlatUExpression {
            field: None,
            bits: None,
        }
    }
}

impl<T> FlatUExpression<T> {
    fn field<U: Into<Option<FlatExpression<T>>>>(mut self, e: U) -> Self {
        self.field = e.into();
        self
    }

    fn bits<U: Into<Option<Vec<FlatExpression<T>>>>>(mut self, e: U) -> Self {
        self.bits = e.into();
        self
    }

    fn with_field<U: Into<Option<FlatExpression<T>>>>(e: U) -> Self {
        Self::default().field(e)
    }

    fn with_bits<U: Into<Option<Vec<FlatExpression<T>>>>>(e: U) -> Self {
        Self::default().bits(e)
    }
}

impl<T: Field> FlatUExpression<T> {
    fn get_field_unchecked(self) -> FlatExpression<T> {
        match self.field {
            Some(f) => f,
            None => match self.bits {
                Some(bits) => flat_expression_from_bits(bits),
                None => unreachable!(),
            },
        }
    }
}

impl<'ast, T: Field> Flattener<'ast, T> {
    /// Returns a `Flattener` with fresh `layout`.
    fn new(config: CompileConfig) -> Flattener<'ast, T> {
        Flattener {
            config,
            next_var_idx: 0,
            layout: HashMap::new(),
            bits_cache: HashMap::new(),
        }
    }

    /// Flattens a definition, trying to avoid creating redundant variables
    fn define(
        &mut self,
        e: FlatExpression<T>,
        statements_flattened: &mut FlatStatements<'ast, T>,
    ) -> Variable {
        match e {
            FlatExpression::Identifier(id) => id.id,
            e => {
                let res = self.use_sym();
                statements_flattened.push_back(FlatStatement::definition(res, e));
                res
            }
        }
    }

    /// Compute a range check between the bid endian decomposition of an expression and the
    /// big endian decomposition of a constant
    ///
    /// # Arguments
    /// * `a` - the big-endian bit decomposition of the expression to check against the range
    /// * `b` - the big-endian bit decomposition of the upper bound we're checking against
    ///
    /// # Returns
    /// * a vector of FlatExpression which all evaluate to `1` if `a <= b` and `0` otherwise
    ///
    /// # Notes
    ///
    /// Algorithm from [the sapling spec](https://github.com/zcash/zips/blob/master/protocol/sapling.pdf) A.3.2.2
    ///
    /// Let's assume b = [1, 1, 1, 0]
    ///
    /// 1. Init `sizeUnknown = true`
    ///    As long as `sizeUnknown` is `true` we don't yet know if a is <= than b.
    /// 2. Loop over `b`:
    ///     * b[0] = 1
    ///       when `b` is 1 we check whether `a` is 0 in that particular run and update
    ///       `sizeUnknown` accordingly:
    ///       `sizeUnknown = sizeUnknown && a[0]`
    ///     * b[1] = 1
    ///       `sizeUnknown = sizeUnknown && a[1]`
    ///     * b[2] = 1
    ///       `sizeUnknown = sizeUnknown && a[2]`
    ///     * b[3] = 0
    ///       we need to enforce that `a` is 0 in case `sizeUnknown`is still `true`,
    ///       otherwise `a` can be {0,1}:
    ///      `true == (!sizeUnknown || !a[3])`
    ///                   **true => a -> 0
    ///      sizeUnkown *
    ///                   **false => a -> {0,1}
    #[must_use]
    fn constant_le_check(
        &mut self,
        statements_flattened: &mut FlatStatements<'ast, T>,
        a: &[FlatExpression<T>],
        b: &[bool],
    ) -> Vec<FlatExpression<T>> {
        assert_eq!(a.len(), b.len());

        let is_power_of_two_minus_one = b.iter().all(|b| *b);

        // if `b` is all ones, then the check is always verified because that's the maximum possible value
        if is_power_of_two_minus_one {
            let statements: Vec<_> = a
                .iter()
                .map(|e| {
                    let e_id = self.define(e.clone(), statements_flattened);
                    FlatStatement::condition(
                        e_id.into(),
                        FlatExpression::mul(e_id.into(), e_id.into()),
                        RuntimeError::Bitness,
                    )
                })
                .collect();
            statements_flattened.extend(statements);
            return vec![];
        }

        let len = b.len();

        let mut is_not_smaller_run = vec![];
        let mut size_unknown = vec![];

        for _ in 0..len {
            is_not_smaller_run.push(self.use_sym());
            size_unknown.push(self.use_sym());
        }

        // init size_unknown = true
        statements_flattened.push_back(FlatStatement::definition(
            size_unknown[0],
            FlatExpression::value(T::from(1)),
        ));

        let mut res = vec![];

        for (i, b) in b.iter().enumerate() {
            if *b {
                statements_flattened.push_back(FlatStatement::definition(
                    is_not_smaller_run[i],
                    a[i].clone(),
                ));

                // don't need to update size_unknown in the last round
                if i < len - 1 {
                    statements_flattened.push_back(FlatStatement::definition(
                        size_unknown[i + 1],
                        FlatExpression::mul(size_unknown[i].into(), is_not_smaller_run[i].into()),
                    ));
                }
            } else {
                // don't need to update size_unknown in the last round
                if i < len - 1 {
                    statements_flattened.push_back(
                        // sizeUnknown is not changing in this case
                        // We sill have to assign the old value to the variable of the current run
                        // This trivial definition will later be removed by the optimiser
                        FlatStatement::definition(size_unknown[i + 1], size_unknown[i].into()),
                    );
                }

                let or_left =
                    FlatExpression::sub(FlatExpression::value(T::from(1)), size_unknown[i].into());
                let or_right: FlatExpression<_> =
                    FlatExpression::sub(FlatExpression::value(T::from(1)), a[i].clone());

                let and_name = self.use_sym();
                let and = FlatExpression::mul(or_left.clone(), or_right.clone());
                statements_flattened.push_back(FlatStatement::definition(and_name, and));
                let or =
                    FlatExpression::sub(FlatExpression::add(or_left, or_right), and_name.into());

                res.push(or);
            }
        }

        res
    }

    /// Compute an equality check between two expressions
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `left - the first `FlatExpression`
    /// * `right` - the second `FlatExpression`
    ///
    /// # Returns
    /// * A FlatExpression which evaluates to `1` if `left == right`, `0` otherwise
    fn eq_check(
        &mut self,
        statements_flattened: &mut FlatStatements<'ast, T>,
        left: FlatExpression<T>,
        right: FlatExpression<T>,
    ) -> FlatExpression<T> {
        let left = self.define(left, statements_flattened);
        let right = self.define(right, statements_flattened);

        // Wanted: (Y = (X != 0) ? 1 : 0)
        // X = a - b
        // # Y = if X == 0 then 0 else 1 fi
        // # M = if X == 0 then 1 else 1/X fi
        // Y == X * M
        // 0 == (1-Y) * X

        let x = FlatExpression::sub(left.into(), right.into());

        let name_y = self.use_sym();
        let name_m = self.use_sym();

        statements_flattened.push_back(FlatStatement::directive(
            vec![name_y, name_m],
            Solver::ConditionEq,
            vec![x.clone()],
        ));
        statements_flattened.push_back(FlatStatement::condition(
            FlatExpression::identifier(name_y),
            FlatExpression::mul(x.clone(), FlatExpression::identifier(name_m)),
            RuntimeError::Equal,
        ));

        let res = FlatExpression::sub(
            FlatExpression::value(T::one()),
            FlatExpression::identifier(name_y),
        );

        statements_flattened.push_back(FlatStatement::condition(
            FlatExpression::value(T::zero()),
            FlatExpression::mul(res.clone(), x),
            RuntimeError::Equal,
        ));

        res
    }

    /// Enforce a range check against a constant: the range check isn't verified iff a constraint will fail
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `a` - the big-endian bit decomposition of the expression we enforce to be in range
    /// * `b` - the big-endian bit decomposition of the upper bound of the range
    fn enforce_constant_le_check_bits(
        &mut self,
        statements_flattened: &mut FlatStatements<'ast, T>,
        a: &[FlatExpression<T>],
        c: &[bool],
        error: RuntimeError,
    ) {
        let conditions = self.constant_le_check(statements_flattened, a, c);

        let conditions_count = conditions.len();

        let conditions_sum = conditions
            .into_iter()
            .fold(FlatExpression::from(T::zero()), |acc, e| {
                FlatExpression::add(acc, e)
            });
        statements_flattened.push_back(FlatStatement::condition(
            FlatExpression::value(T::from(0)),
            FlatExpression::sub(conditions_sum, T::from(conditions_count).into()),
            error,
        ));
    }

    /// Enforce a range check against a constant: the range check isn't verified iff a constraint will fail
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `e` - the expression we enforce to be in range
    /// * `c` - the constant upper bound of the range
    fn enforce_constant_le_check(
        &mut self,
        statements_flattened: &mut FlatStatements<'ast, T>,
        e: FlatExpression<T>,
        c: T,
        error: RuntimeError,
    ) {
        let c_bit_width = c.bits() as usize;
        let c_bits_be = c.to_bits_be();

        // we reduce e `n` bits with `n` the bitwidth of `c`
        // if `e` does not fit in `n` bits, this will fail
        // but as we are asserting `e < c`, `e` not fitting in `n` bits should indeed lead to an unsatisfied constraint
        let e_bits_be = self.get_bits_unchecked(
            &FlatUExpression::with_field(e),
            c_bit_width,
            c_bit_width,
            statements_flattened,
            error.clone(),
        );

        self.enforce_constant_le_check_bits(
            statements_flattened,
            &e_bits_be,
            &c_bits_be[T::get_required_bits() - c_bit_width..],
            error,
        );
    }

    /// Enforce a range check against a constant: the range check isn't verified iff a constraint will fail
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `e` - the expression we enforce to be in range
    /// * `c` - the constant upper bound of the range
    fn enforce_constant_lt_check(
        &mut self,
        statements_flattened: &mut FlatStatements<'ast, T>,
        e: FlatExpression<T>,
        c: T,
        error: RuntimeError,
    ) {
        // `e < 0` will always result in false value, so we constrain `0 == 1`
        if c == T::zero() {
            statements_flattened.push_back(FlatStatement::condition(
                T::zero().into(),
                T::one().into(),
                error,
            ));
        } else {
            self.enforce_constant_le_check(statements_flattened, e, c - T::one(), error)
        }
    }

    fn make_conditional(
        &mut self,
        statements: FlatStatements<'ast, T>,
        condition: FlatExpression<T>,
    ) -> FlatStatements<'ast, T> {
        statements
            .into_iter()
            .flat_map(|s| match s {
                FlatStatement::Condition(s) => {
                    let span = s.get_span();

                    let mut output = FlatStatements::default();

                    output.set_span(span);

                    // we transform (a == b) into (c => (a == b)) which is (!c || (a == b))

                    // let's introduce new variables to make sure everything is linear
                    let name_lin = self.define(s.lin, &mut output);
                    let name_quad = self.define(s.quad, &mut output);

                    // let's introduce an expression which is 1 iff `a == b`
                    let y = FlatExpression::add(
                        FlatExpression::sub(name_lin.into(), name_quad.into()),
                        T::one().into(),
                    ); // let's introduce !c
                    let x = FlatExpression::sub(T::one().into(), condition.clone());
                    assert!(x.is_linear() && y.is_linear());
                    let name_x_or_y = self.use_sym();
                    output.push_back(FlatStatement::directive(
                        vec![name_x_or_y],
                        Solver::Or,
                        vec![x.clone(), y.clone()],
                    ));
                    output.push_back(FlatStatement::condition(
                        FlatExpression::add(
                            x.clone(),
                            FlatExpression::sub(y.clone(), name_x_or_y.into()),
                        ),
                        FlatExpression::mul(x, y),
                        RuntimeError::BranchIsolation,
                    ));
                    output.push_back(FlatStatement::condition(
                        name_x_or_y.into(),
                        T::one().into(),
                        s.error,
                    ));

                    output
                }
                s => {
                    let mut v = FlatStatements::default();
                    v.push_back(s);
                    v
                }
            })
            .fold(FlatStatements::default(), |mut acc, s| {
                acc.push_back(s);
                acc
            })
    }

    /// Flatten an if/else expression
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `condition` - the condition as a `BooleanExpression`.
    /// * `consequence` - the consequence of type U.
    /// * `alternative` - the alternative of type U.
    /// # Remarks
    /// * U is the type of the expression
    fn flatten_conditional_expression<U: Flatten<'ast, T>>(
        &mut self,
        statements_flattened: &mut FlatStatements<'ast, T>,
        e: ConditionalExpression<'ast, T, U>,
    ) -> FlatUExpression<T> {
        let condition = *e.condition;
        let consequence = *e.consequence;
        let alternative = *e.alternative;

        let condition_flat =
            self.flatten_boolean_expression(statements_flattened, condition.clone());

        let condition_id = self.use_sym();
        statements_flattened.push_back(FlatStatement::definition(condition_id, condition_flat));

        let (consequence, alternative) = if self.config.isolate_branches {
            let mut consequence_statements = FlatStatements::default();

            let consequence = consequence.flatten(self, &mut consequence_statements);

            let mut alternative_statements = FlatStatements::default();

            let alternative = alternative.flatten(self, &mut alternative_statements);

            let consequence_statements =
                self.make_conditional(consequence_statements, condition_id.into());
            let alternative_statements = self.make_conditional(
                alternative_statements,
                FlatExpression::sub(FlatExpression::value(T::one()), condition_id.into()),
            );

            statements_flattened.extend(consequence_statements);
            statements_flattened.extend(alternative_statements);

            (consequence, alternative)
        } else {
            (
                consequence.flatten(self, statements_flattened),
                alternative.flatten(self, statements_flattened),
            )
        };

        let consequence = consequence.flat();
        let alternative = alternative.flat();

        let consequence_id = self.use_sym();
        statements_flattened.push_back(FlatStatement::definition(consequence_id, consequence));

        let alternative_id = self.use_sym();
        statements_flattened.push_back(FlatStatement::definition(alternative_id, alternative));

        let term0_id = self.use_sym();
        statements_flattened.push_back(FlatStatement::definition(
            term0_id,
            FlatExpression::mul(condition_id.into(), FlatExpression::from(consequence_id)),
        ));

        let term1_id = self.use_sym();
        statements_flattened.push_back(FlatStatement::definition(
            term1_id,
            FlatExpression::mul(
                FlatExpression::sub(FlatExpression::value(T::one()), condition_id.into()),
                FlatExpression::from(alternative_id),
            ),
        ));

        let res = self.use_sym();
        statements_flattened.push_back(FlatStatement::definition(
            res,
            FlatExpression::add(
                FlatExpression::from(term0_id),
                FlatExpression::from(term1_id),
            ),
        ));

        FlatUExpression {
            field: Some(FlatExpression::identifier(res)),
            bits: None,
        }
    }

    /// Compute a strict check against a constant
    /// # Arguments
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `e` - the `FlatExpression` that's being checked against the range.
    /// * `c` - the constant strict upper bound of the range
    ///
    /// # Returns
    /// * a `FlatExpression` which evaluates to `1` if `0 <= e < c`, and to `0` otherwise
    fn constant_lt_check(
        &mut self,
        statements_flattened: &mut FlatStatements<'ast, T>,
        e: FlatExpression<T>,
        c: T,
    ) -> FlatExpression<T> {
        if c == T::zero() {
            // this is the case c == 0, we return 0, aka false
            return T::zero().into();
        }

        self.constant_field_le_check(statements_flattened, e, c - T::one())
    }

    /// Compute a range check against a constant
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `e` - the `FlatExpression` that's being checked against the range.
    /// * `c` - the constant upper bound of the range
    ///
    /// # Returns
    /// * a `FlatExpression` which evaluates to `1` if `0 <= e <= c`, and to `0` otherwise
    fn constant_field_le_check(
        &mut self,
        statements_flattened: &mut FlatStatements<'ast, T>,
        e: FlatExpression<T>,
        c: T,
    ) -> FlatExpression<T> {
        let bitwidth = T::get_required_bits();

        // we want to reduce `e <= c` to 0 or 1, without ever throwing. We know the bitwidth of `c` and want to minimize the bitwidth we reduce `e` to.
        // we must use the maximum bitwidth, as otherwise, large enough values of `e` would lead `get_bits` to throw.
        let e_bits_be = self.get_bits_unchecked(
            &FlatUExpression::with_field(e),
            bitwidth,
            bitwidth,
            statements_flattened,
            RuntimeError::ConstantLtSum,
        );

        // check that this decomposition does not overflow the field
        self.enforce_constant_le_check_bits(
            statements_flattened,
            &e_bits_be,
            &T::max_value().to_bits_be(),
            RuntimeError::Le,
        );

        let conditions = self.constant_le_check(statements_flattened, &e_bits_be, &c.to_bits_be());

        // return `len(conditions) == sum(conditions)`
        self.eq_check(
            statements_flattened,
            T::from(conditions.len()).into(),
            conditions
                .into_iter()
                .fold(FlatExpression::value(T::zero()), |acc, e| {
                    FlatExpression::add(acc, e)
                }),
        )
    }

    #[must_use]
    fn le_check(
        &mut self,
        statements_flattened: &mut FlatStatements<'ast, T>,
        lhs_flattened: FlatExpression<T>,
        rhs_flattened: FlatExpression<T>,
        bit_width: usize,
    ) -> FlatExpression<T> {
        FlatExpression::add(
            self.eq_check(
                statements_flattened,
                lhs_flattened.clone(),
                rhs_flattened.clone(),
            ),
            self.lt_check(
                statements_flattened,
                lhs_flattened,
                rhs_flattened,
                bit_width,
            ),
        )
    }

    #[must_use]
    fn lt_check(
        &mut self,
        statements_flattened: &mut FlatStatements<'ast, T>,
        lhs_flattened: FlatExpression<T>,
        rhs_flattened: FlatExpression<T>,
        bit_width: usize,
    ) -> FlatExpression<T> {
        match (lhs_flattened, rhs_flattened) {
            (x, FlatExpression::Value(constant)) => {
                self.constant_lt_check(statements_flattened, x, constant.value)
            }
            // (c < x <= p - 1) <=> (0 <= p - 1 - x < p - 1 - c)
            (FlatExpression::Value(constant), x) => self.constant_lt_check(
                statements_flattened,
                FlatExpression::sub(T::max_value().into(), x),
                T::max_value() - constant.value,
            ),
            (lhs_flattened, rhs_flattened) => {
                let lhs_id = self.define(lhs_flattened, statements_flattened);
                let rhs_id = self.define(rhs_flattened, statements_flattened);

                // shifted_sub := 2**safe_width + lhs - rhs
                let shifted_sub = FlatExpression::add(
                    FlatExpression::value(T::from(2).pow(bit_width)),
                    FlatExpression::sub(
                        FlatExpression::identifier(lhs_id),
                        FlatExpression::identifier(rhs_id),
                    ),
                );

                let sub_width = bit_width + 1;

                let shifted_sub_bits_be = self.get_bits_unchecked(
                    &FlatUExpression::with_field(shifted_sub),
                    sub_width,
                    sub_width,
                    statements_flattened,
                    RuntimeError::IncompleteDynamicRange,
                );

                FlatExpression::sub(
                    FlatExpression::value(T::one()),
                    shifted_sub_bits_be[0].clone(),
                )
            }
        }
    }

    /// Flattens a boolean expression
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `expression` - `BooleanExpression` that will be flattened.
    ///
    /// # Postconditions
    ///
    /// * `flatten_boolean_expressions` always returns a linear expression,
    /// * in order to preserve composability.
    fn flatten_boolean_expression(
        &mut self,
        statements_flattened: &mut FlatStatements<'ast, T>,
        expression: BooleanExpression<'ast, T>,
    ) -> FlatExpression<T> {
        let span = expression.get_span();

        let span_backup = statements_flattened.span;

        statements_flattened.set_span(span);

        let res = match expression {
            BooleanExpression::Identifier(x) => {
                FlatExpression::identifier(*self.layout.get(&x.id).unwrap())
            }
            BooleanExpression::Select(e) => self
                .flatten_select_expression(statements_flattened, e)
                .get_field_unchecked(),
            BooleanExpression::FieldLt(e) => {
                // Get the bit width to know the size of the binary decompositions for this Field
                let bit_width = T::get_required_bits();

                let safe_width = bit_width - 2; // dynamic comparison is not complete, it only applies to field elements whose difference is strictly smaller than 2**(bitwidth - 2)

                let lhs_flattened = self.flatten_field_expression(statements_flattened, *e.left);
                let rhs_flattened = self.flatten_field_expression(statements_flattened, *e.right);
                self.lt_check(
                    statements_flattened,
                    lhs_flattened,
                    rhs_flattened,
                    safe_width,
                )
            }
            BooleanExpression::BoolEq(e) => {
                // lhs and rhs are booleans, they flatten to 0 or 1
                let x = self.flatten_boolean_expression(statements_flattened, *e.left);
                let y = self.flatten_boolean_expression(statements_flattened, *e.right);
                // Wanted: Not(X - Y)**2 which is an XNOR
                // We know that X and Y are [0, 1]
                // (X - Y) can become a negative values, which is why squaring the result is needed
                // Negating this returns correct result

                // Non-binary Truth table for logic of operation
                // +---+---+-------+---------------+
                // | X | Y | X - Y | Not(X - Y)**2 |
                // +---+---+-------+---------------+
                // | 1 | 1 |     0 |             1 |
                // | 1 | 0 |     1 |             0 |
                // | 0 | 1 |    -1 |             0 |
                // | 0 | 0 |     0 |             1 |
                // +---+---+-------+---------------+

                let x_sub_y = FlatExpression::sub(x, y);
                let name_x_mult_x = self.use_sym();

                statements_flattened.push_back(FlatStatement::definition(
                    name_x_mult_x,
                    FlatExpression::mul(x_sub_y.clone(), x_sub_y),
                ));

                FlatExpression::sub(
                    FlatExpression::value(T::one()),
                    FlatExpression::identifier(name_x_mult_x),
                )
            }
            BooleanExpression::FieldEq(e) => {
                let lhs = self.flatten_field_expression(statements_flattened, *e.left);

                let rhs = self.flatten_field_expression(statements_flattened, *e.right);

                self.eq_check(statements_flattened, lhs, rhs)
            }
            BooleanExpression::UintEq(e) => {
                // We reduce each side into range and apply the same approach as for field elements

                // Wanted: (Y = (X != 0) ? 1 : 0)
                // X = a - b
                // # Y = if X == 0 then 0 else 1 fi
                // # M = if X == 0 then 1 else 1/X fi
                // Y == X * M
                // 0 == (1-Y) * X

                assert!(e.left.metadata.as_ref().unwrap().should_reduce.to_bool());
                assert!(e.right.metadata.as_ref().unwrap().should_reduce.to_bool());

                let lhs = self
                    .flatten_uint_expression(statements_flattened, *e.left)
                    .get_field_unchecked();
                let rhs = self
                    .flatten_uint_expression(statements_flattened, *e.right)
                    .get_field_unchecked();

                self.eq_check(statements_flattened, lhs, rhs)
            }
            BooleanExpression::FieldLe(e) => {
                let lt = self.flatten_boolean_expression(
                    statements_flattened,
                    BooleanExpression::field_lt(*e.left.clone(), *e.right.clone()).span(span),
                );

                let eq = self.flatten_boolean_expression(
                    statements_flattened,
                    BooleanExpression::field_eq(*e.left, *e.right).span(span),
                );

                FlatExpression::add(eq, lt)
            }
            BooleanExpression::UintLt(e) => {
                let bit_width = e.left.bitwidth.to_usize();
                assert!(e.left.metadata.as_ref().unwrap().should_reduce.to_bool());
                assert!(e.right.metadata.as_ref().unwrap().should_reduce.to_bool());

                let lhs_flattened = self
                    .flatten_uint_expression(statements_flattened, *e.left)
                    .get_field_unchecked();
                let rhs_flattened = self
                    .flatten_uint_expression(statements_flattened, *e.right)
                    .get_field_unchecked();

                self.lt_check(
                    statements_flattened,
                    lhs_flattened,
                    rhs_flattened,
                    bit_width,
                )
            }
            BooleanExpression::UintLe(e) => {
                let lt = self.flatten_boolean_expression(
                    statements_flattened,
                    BooleanExpression::uint_lt(*e.left.clone(), *e.right.clone()).span(span),
                );
                let eq = self.flatten_boolean_expression(
                    statements_flattened,
                    BooleanExpression::uint_eq(*e.left, *e.right).span(span),
                );
                FlatExpression::add(eq, lt)
            }
            BooleanExpression::Or(e) => {
                let x = self.flatten_boolean_expression(statements_flattened, *e.left);
                let y = self.flatten_boolean_expression(statements_flattened, *e.right);
                assert!(x.is_linear() && y.is_linear());
                let name_x_or_y = self.use_sym();
                statements_flattened.push_back(FlatStatement::directive(
                    vec![name_x_or_y],
                    Solver::Or,
                    vec![x.clone(), y.clone()],
                ));
                statements_flattened.push_back(FlatStatement::condition(
                    FlatExpression::add(
                        x.clone(),
                        FlatExpression::sub(y.clone(), name_x_or_y.into()),
                    ),
                    FlatExpression::mul(x, y),
                    RuntimeError::Or,
                ));
                name_x_or_y.into()
            }
            BooleanExpression::And(e) => {
                let x = self.flatten_boolean_expression(statements_flattened, *e.left);
                let y = self.flatten_boolean_expression(statements_flattened, *e.right);

                let name_x_and_y = self.use_sym();
                assert!(x.is_linear() && y.is_linear());
                statements_flattened.push_back(FlatStatement::definition(
                    name_x_and_y,
                    FlatExpression::mul(x, y),
                ));

                FlatExpression::identifier(name_x_and_y)
            }
            BooleanExpression::Not(e) => {
                let x = self.flatten_boolean_expression(statements_flattened, *e.inner);
                FlatExpression::sub(FlatExpression::value(T::one()), x)
            }
            BooleanExpression::Value(b) => FlatExpression::value(match b.value {
                true => T::from(1),
                false => T::from(0),
            }),
            BooleanExpression::Conditional(e) => self
                .flatten_conditional_expression(statements_flattened, e)
                .get_field_unchecked(),
        }
        .span(span);

        statements_flattened.set_span(span_backup);

        res
    }

    fn u_to_bits(
        &mut self,
        expression: FlatUExpression<T>,
        bitwidth: UBitwidth,
    ) -> Vec<FlatUExpression<T>> {
        let bits = expression.bits.unwrap();
        assert_eq!(bits.len(), bitwidth.to_usize());

        bits.into_iter().map(FlatUExpression::with_field).collect()
    }

    fn bits_to_u(
        &mut self,
        bits: Vec<FlatUExpression<T>>,
        bitwidth: UBitwidth,
    ) -> FlatUExpression<T> {
        let bits: Vec<_> = bits.into_iter().map(|e| e.get_field_unchecked()).collect();
        assert_eq!(bits.len(), bitwidth.to_usize());

        FlatUExpression::with_bits(bits)
    }

    /// Flattens a function call
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `id` - `Identifier of the function.
    /// * `return_types` - Types of the return values of the function
    /// * `param_expressions` - Arguments of this call
    fn flatten_embed_call(
        &mut self,
        statements_flattened: &mut FlatStatements<'ast, T>,
        embed: FlatEmbed,
        generics: Vec<u32>,
        param_expressions: Vec<ZirExpression<'ast, T>>,
    ) -> Vec<FlatUExpression<T>> {
        let mut params: Vec<_> = param_expressions
            .into_iter()
            .map(|p| {
                if let ZirExpression::Uint(e) = &p {
                    assert!(e.metadata.as_ref().unwrap().should_reduce.is_true());
                }
                self.flatten_expression(statements_flattened, p)
            })
            .collect();

        match embed {
            FlatEmbed::FieldToBoolUnsafe => vec![params.pop().unwrap()],
            FlatEmbed::U8ToBits => self.u_to_bits(params.pop().unwrap(), 8.into()),
            FlatEmbed::U16ToBits => self.u_to_bits(params.pop().unwrap(), 16.into()),
            FlatEmbed::U32ToBits => self.u_to_bits(params.pop().unwrap(), 32.into()),
            FlatEmbed::U64ToBits => self.u_to_bits(params.pop().unwrap(), 64.into()),
            FlatEmbed::U8FromBits => {
                vec![self.bits_to_u(params, 8.into())]
            }
            FlatEmbed::U16FromBits => {
                vec![self.bits_to_u(params, 16.into())]
            }
            FlatEmbed::U32FromBits => {
                vec![self.bits_to_u(params, 32.into())]
            }
            FlatEmbed::U64FromBits => {
                vec![self.bits_to_u(params, 64.into())]
            }
            FlatEmbed::BitArrayLe => {
                // get the length of the bit arrays
                let len = generics[0];

                // split the arguments into the two bit arrays of size `len`
                let (expressions, constants) = (
                    params[..len as usize].to_vec(),
                    params[len as usize..].to_vec(),
                );

                // define variables for the variable bits
                let variables: Vec<_> = expressions
                    .into_iter()
                    .map(|e| {
                        self.define(e.get_field_unchecked(), statements_flattened)
                            .into()
                    })
                    .collect();

                // get constants for the constant bits
                let constants: Vec<_> = constants
                    .into_iter()
                    .map(|e| match e.get_field_unchecked() {
                        FlatExpression::Value(n) if n.value == T::one() => true,
                        FlatExpression::Value(n) if n.value == T::zero() => false,
                        _ => unreachable!(),
                    })
                    .collect();

                // get the list of conditions which must hold iff the `<=` relation holds
                let conditions =
                    self.constant_le_check(statements_flattened, &variables, &constants);

                // return `len(conditions) == sum(conditions)`
                vec![FlatUExpression::with_field(
                    self.eq_check(
                        statements_flattened,
                        T::from(conditions.len()).into(),
                        conditions
                            .into_iter()
                            .fold(FlatExpression::value(T::zero()), |acc, e| {
                                FlatExpression::add(acc, e)
                            }),
                    ),
                )]
            }
            funct => match funct {
                FlatEmbed::Unpack => self.flatten_embed_call_aux(
                    statements_flattened,
                    params,
                    unpack_to_bitwidth(generics[0] as usize),
                ),
                #[cfg(feature = "bellman")]
                FlatEmbed::Sha256Round => {
                    self.flatten_embed_call_aux(statements_flattened, params, sha256_round())
                }
                #[cfg(feature = "ark")]
                FlatEmbed::SnarkVerifyBls12377 => self.flatten_embed_call_aux(
                    statements_flattened,
                    params,
                    snark_verify_bls12_377::<T>(generics[0] as usize),
                ),
                _ => unreachable!(),
            },
        }
    }

    fn flatten_embed_call_aux(
        &mut self,
        statements_flattened: &mut FlatStatements<'ast, T>,
        params: Vec<FlatUExpression<T>>,
        funct: FlatFunctionIterator<'ast, T, impl IntoIterator<Item = FlatStatement<'ast, T>>>,
    ) -> Vec<FlatUExpression<T>> {
        let mut replacement_map = HashMap::new();

        // Handle complex parameters and assign values:
        // Rename Parameters, assign them to values in call. Resolve complex expressions with definitions
        let params_flattened = params.into_iter().map(|e| e.get_field_unchecked());

        let return_values = (0..funct.return_count).map(Variable::public);

        for (concrete_argument, formal_argument) in params_flattened.zip(funct.arguments) {
            let new_var = self.define(concrete_argument, statements_flattened);
            replacement_map.insert(formal_argument.id, new_var);
        }

        // Ensure renaming and correct returns:
        // add all flattened statements, adapt return statements

        let statements = funct.statements.into_iter().map(|stat| match stat {
            FlatStatement::Block(..) => unreachable!(),
            FlatStatement::Definition(s) => {
                let new_var = self.use_sym();
                replacement_map.insert(s.assignee, new_var);
                let new_rhs = s.rhs.apply_substitution(&replacement_map);
                FlatStatement::definition(new_var, new_rhs)
            }
            FlatStatement::Condition(s) => {
                let new_quad = s.quad.apply_substitution(&replacement_map);
                let new_lin = s.lin.apply_substitution(&replacement_map);
                FlatStatement::condition(new_lin, new_quad, s.error)
            }
            FlatStatement::Directive(d) => {
                let new_outputs = d
                    .outputs
                    .into_iter()
                    .map(|o| {
                        let new_o = self.use_sym();
                        replacement_map.insert(o, new_o);
                        new_o
                    })
                    .collect();
                let new_inputs = d
                    .inputs
                    .into_iter()
                    .map(|i| i.apply_substitution(&replacement_map))
                    .collect();
                FlatStatement::directive(new_outputs, d.solver, new_inputs)
            }
            FlatStatement::Log(s) => FlatStatement::Log(LogStatement::new(
                s.format_string,
                s.expressions
                    .into_iter()
                    .map(|(t, e)| {
                        (
                            t,
                            e.into_iter()
                                .map(|e| e.apply_substitution(&replacement_map))
                                .collect(),
                        )
                    })
                    .collect(),
            )),
        });

        statements_flattened.extend(statements);

        return_values
            .map(|x| FlatExpression::from(x).apply_substitution(&replacement_map))
            .map(FlatUExpression::with_field)
            .collect()
    }

    /// Flattens an expression
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `expr` - `ZirExpression` that will be flattened.
    fn flatten_expression(
        &mut self,
        statements_flattened: &mut FlatStatements<'ast, T>,
        expr: ZirExpression<'ast, T>,
    ) -> FlatUExpression<T> {
        match expr {
            ZirExpression::FieldElement(e) => {
                FlatUExpression::with_field(self.flatten_field_expression(statements_flattened, e))
            }
            ZirExpression::Boolean(e) => FlatUExpression::with_field(
                self.flatten_boolean_expression(statements_flattened, e),
            ),
            ZirExpression::Uint(e) => self.flatten_uint_expression(statements_flattened, e),
        }
    }

    fn default_xor(
        &mut self,
        statements_flattened: &mut FlatStatements<'ast, T>,
        left: UExpression<'ast, T>,
        right: UExpression<'ast, T>,
    ) -> FlatUExpression<T> {
        let left_flattened = self.flatten_uint_expression(statements_flattened, left);
        let right_flattened = self.flatten_uint_expression(statements_flattened, right);

        // `left` and `right` were reduced to the target bitwidth, hence their bits are available

        let left_bits = left_flattened.bits.unwrap();
        let right_bits = right_flattened.bits.unwrap();

        let xor: Vec<FlatExpression<T>> = left_bits
            .into_iter()
            .zip(right_bits.into_iter())
            .map(|(x, y)| match (x, y) {
                (FlatExpression::Value(n), e) | (e, FlatExpression::Value(n)) => {
                    if n.value == T::from(0) {
                        self.define(e, statements_flattened).into()
                    } else if n.value == T::from(1) {
                        self.define(
                            FlatExpression::sub(FlatExpression::value(T::from(1)), e),
                            statements_flattened,
                        )
                        .into()
                    } else {
                        unreachable!()
                    }
                }
                (x, y) => {
                    let name = self.use_sym();

                    statements_flattened.extend(vec![
                        FlatStatement::directive(
                            vec![name],
                            Solver::Xor,
                            vec![x.clone(), y.clone()],
                        ),
                        FlatStatement::condition(
                            FlatExpression::add(
                                x.clone(),
                                FlatExpression::sub(y.clone(), name.into()),
                            ),
                            FlatExpression::mul(FlatExpression::add(x.clone(), x), y),
                            RuntimeError::Xor,
                        ),
                    ]);

                    name.into()
                }
            })
            .collect();

        FlatUExpression::with_bits(xor)
    }

    fn euclidean_division(
        &mut self,
        statements_flattened: &mut FlatStatements<'ast, T>,
        target_bitwidth: UBitwidth,
        left: UExpression<'ast, T>,
        right: UExpression<'ast, T>,
    ) -> (FlatExpression<T>, FlatExpression<T>) {
        let left_flattened = self
            .flatten_uint_expression(statements_flattened, left)
            .get_field_unchecked();
        let right_flattened = self
            .flatten_uint_expression(statements_flattened, right)
            .get_field_unchecked();
        let n = if left_flattened.is_linear() {
            left_flattened
        } else {
            let id = self.use_sym();
            statements_flattened.push_back(FlatStatement::definition(id, left_flattened));
            FlatExpression::identifier(id)
        };
        let d = if right_flattened.is_linear() {
            right_flattened
        } else {
            let id = self.use_sym();
            statements_flattened.push_back(FlatStatement::definition(id, right_flattened));
            FlatExpression::identifier(id)
        };

        // introduce the quotient and remainder
        let q = self.use_sym();
        let r = self.use_sym();

        statements_flattened.push_back(FlatStatement::directive(
            vec![q, r],
            Solver::EuclideanDiv,
            vec![n.clone(), d.clone()],
        ));

        let target_bitwidth = target_bitwidth.to_usize();

        // q in range
        let _ = self.get_bits_unchecked(
            &FlatUExpression::with_field(FlatExpression::from(q)),
            target_bitwidth,
            target_bitwidth,
            statements_flattened,
            RuntimeError::Sum,
        );

        // r in range
        let _ = self.get_bits_unchecked(
            &FlatUExpression::with_field(FlatExpression::from(r)),
            target_bitwidth,
            target_bitwidth,
            statements_flattened,
            RuntimeError::Sum,
        );

        // r < d <=> r - d + 2**w < 2**w
        let _ = self.get_bits_unchecked(
            &FlatUExpression::with_field(FlatExpression::add(
                FlatExpression::sub(r.into(), d.clone()),
                FlatExpression::value(T::from(2_u128.pow(target_bitwidth as u32))),
            )),
            target_bitwidth,
            target_bitwidth,
            statements_flattened,
            RuntimeError::Sum,
        );

        // q*d == n - r
        statements_flattened.push_back(FlatStatement::condition(
            FlatExpression::sub(n, r.into()),
            FlatExpression::mul(q.into(), d),
            RuntimeError::Euclidean,
        ));

        (q.into(), r.into())
    }

    /// Flattens a uint expression
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `expr` - `UExpression` that will be flattened.
    fn flatten_uint_expression(
        &mut self,
        statements_flattened: &mut FlatStatements<'ast, T>,
        expr: UExpression<'ast, T>,
    ) -> FlatUExpression<T> {
        let span = expr.as_inner().get_span();

        let span_backup = statements_flattened.span;

        statements_flattened.set_span(span);

        // the bitwidth for this type of uint (8, 16 or 32)
        let target_bitwidth = expr.bitwidth;

        let metadata = expr.metadata.clone().unwrap();

        // the bitwidth on which this value is currently represented
        let actual_bitwidth = metadata.bitwidth() as usize;

        // whether this value should be reduced, for example if it is then used in a bitwidth operation
        let should_reduce = metadata.should_reduce;

        let should_reduce = should_reduce.to_bool();

        let res = match expr.into_inner() {
            UExpressionInner::Value(x) => {
                FlatUExpression::with_field(FlatExpression::value(T::from(x.value)))
            } // force to be a field element
            UExpressionInner::Identifier(x) => {
                let field = FlatExpression::identifier(*self.layout.get(&x.id).unwrap());
                let bits = self.bits_cache.get(&field).map(|bits| {
                    assert_eq!(bits.len(), target_bitwidth.to_usize());
                    bits.clone()
                });
                FlatUExpression::with_field(field).bits(bits)
            }
            UExpressionInner::Select(e) => self.flatten_select_expression(statements_flattened, e),
            UExpressionInner::Not(e) => {
                let e = self.flatten_uint_expression(statements_flattened, *e.inner);

                let e_bits = e.bits.unwrap();

                assert_eq!(e_bits.len(), target_bitwidth.to_usize());

                let name_not: Vec<_> = e_bits
                    .into_iter()
                    .map(|bit| {
                        self.define(
                            FlatExpression::sub(FlatExpression::value(T::from(1)), bit),
                            statements_flattened,
                        )
                        .into()
                    })
                    .collect();

                FlatUExpression::with_bits(name_not)
            }
            UExpressionInner::Add(e) => {
                let left_flattened = self
                    .flatten_uint_expression(statements_flattened, *e.left)
                    .get_field_unchecked();

                let right_flattened = self
                    .flatten_uint_expression(statements_flattened, *e.right)
                    .get_field_unchecked();

                let new_left = if left_flattened.is_linear() {
                    left_flattened
                } else {
                    let id = self.use_sym();
                    statements_flattened.push_back(FlatStatement::definition(id, left_flattened));
                    FlatExpression::identifier(id)
                };
                let new_right = if right_flattened.is_linear() {
                    right_flattened
                } else {
                    let id = self.use_sym();
                    statements_flattened.push_back(FlatStatement::definition(id, right_flattened));
                    FlatExpression::identifier(id)
                };

                FlatUExpression::with_field(FlatExpression::add(new_left, new_right))
            }
            UExpressionInner::Sub(e) => {
                // see uint optimizer for the reasoning here
                let offset = FlatExpression::value(T::from(2).pow(std::cmp::max(
                    e.right.metadata.as_ref().unwrap().bitwidth() as usize,
                    target_bitwidth as usize,
                )));

                let left_flattened = self
                    .flatten_uint_expression(statements_flattened, *e.left)
                    .get_field_unchecked();
                let right_flattened = self
                    .flatten_uint_expression(statements_flattened, *e.right)
                    .get_field_unchecked();
                let new_left = if left_flattened.is_linear() {
                    left_flattened
                } else {
                    let id = self.use_sym();
                    statements_flattened.push_back(FlatStatement::definition(id, left_flattened));
                    FlatExpression::identifier(id)
                };
                let new_right = if right_flattened.is_linear() {
                    right_flattened
                } else {
                    let id = self.use_sym();
                    statements_flattened.push_back(FlatStatement::definition(id, right_flattened));
                    FlatExpression::identifier(id)
                };

                FlatUExpression::with_field(FlatExpression::add(
                    offset,
                    FlatExpression::sub(new_left, new_right),
                ))
            }
            UExpressionInner::LeftShift(e) => {
                let by = match e.right.into_inner() {
                    UExpressionInner::Value(v) => v.value as u32,
                    _ => unreachable!(),
                };

                let e = *e.left;

                let e = self.flatten_uint_expression(statements_flattened, e);

                let e_bits = e.bits.unwrap();

                assert_eq!(e_bits.len(), target_bitwidth.to_usize());

                FlatUExpression::with_bits(
                    e_bits
                        .into_iter()
                        .skip(by as usize)
                        .chain(
                            (0..std::cmp::min(by as usize, target_bitwidth.to_usize()))
                                .map(|_| FlatExpression::value(T::from(0))),
                        )
                        .collect::<Vec<_>>(),
                )
            }
            UExpressionInner::RightShift(e) => {
                let by = match e.right.into_inner() {
                    UExpressionInner::Value(v) => v.value as u32,
                    _ => unreachable!(),
                };

                let e = *e.left;

                let e = self.flatten_uint_expression(statements_flattened, e);

                let e_bits = e.bits.unwrap();

                assert_eq!(e_bits.len(), target_bitwidth.to_usize());

                FlatUExpression::with_bits(
                    (0..std::cmp::min(by as usize, target_bitwidth.to_usize()))
                        .map(|_| FlatExpression::value(T::from(0)))
                        .chain(e_bits.into_iter().take(
                            target_bitwidth.to_usize()
                                - std::cmp::min(by as usize, target_bitwidth.to_usize()),
                        ))
                        .collect::<Vec<_>>(),
                )
            }
            UExpressionInner::Mult(e) => {
                let left_flattened = self
                    .flatten_uint_expression(statements_flattened, *e.left)
                    .get_field_unchecked();
                let right_flattened = self
                    .flatten_uint_expression(statements_flattened, *e.right)
                    .get_field_unchecked();
                let new_left = if left_flattened.is_linear() {
                    left_flattened
                } else {
                    let id = self.use_sym();
                    statements_flattened.push_back(FlatStatement::definition(id, left_flattened));
                    FlatExpression::identifier(id)
                };
                let new_right = if right_flattened.is_linear() {
                    right_flattened
                } else {
                    let id = self.use_sym();
                    statements_flattened.push_back(FlatStatement::definition(id, right_flattened));
                    FlatExpression::identifier(id)
                };

                let res = self.use_sym();

                statements_flattened.push_back(FlatStatement::definition(
                    res,
                    FlatExpression::mul(new_left, new_right),
                ));

                FlatUExpression::with_field(FlatExpression::identifier(res))
            }
            UExpressionInner::Div(e) => {
                let (q, _) = self.euclidean_division(
                    statements_flattened,
                    target_bitwidth,
                    *e.left,
                    *e.right,
                );

                FlatUExpression::with_field(q)
            }
            UExpressionInner::Rem(e) => {
                let (_, r) = self.euclidean_division(
                    statements_flattened,
                    target_bitwidth,
                    *e.left,
                    *e.right,
                );

                FlatUExpression::with_field(r)
            }
            UExpressionInner::Conditional(e) => {
                self.flatten_conditional_expression(statements_flattened, e)
            }
            UExpressionInner::Xor(e) => {
                let left_metadata = e.left.metadata.clone().unwrap();
                let right_metadata = e.right.metadata.clone().unwrap();

                let left_span = e.left.get_span();
                let right_span = e.right.get_span();

                match (e.left.into_inner(), e.right.into_inner()) {
                    (UExpressionInner::And(e), UExpressionInner::And(ee)) => {
                        let a = *e.left;
                        let b = *e.right;
                        let aa = *ee.left;
                        let c = *ee.right;

                        if aa.as_inner() == UExpression::not(a.clone()).as_inner() {
                            let a_flattened = self.flatten_uint_expression(statements_flattened, a);
                            let b_flattened = self.flatten_uint_expression(statements_flattened, b);
                            let c_flattened = self.flatten_uint_expression(statements_flattened, c);

                            let a_bits = a_flattened.bits.unwrap();
                            let b_bits = b_flattened.bits.unwrap();
                            let c_bits = c_flattened.bits.unwrap();

                            let res: Vec<FlatExpression<T>> = a_bits
                                .into_iter()
                                .zip(b_bits.into_iter())
                                .zip(c_bits.into_iter())
                                .map(|((a, b), c)| {
                                    // a(b - c) = ch - c

                                    let ch = self.use_sym();

                                    statements_flattened.extend(vec![
                                        FlatStatement::directive(
                                            vec![ch],
                                            Solver::ShaCh,
                                            vec![a.clone(), b.clone(), c.clone()],
                                        ),
                                        FlatStatement::condition(
                                            FlatExpression::sub(ch.into(), c.clone()),
                                            a * (b - c),
                                            RuntimeError::ShaXor,
                                        ),
                                    ]);
                                    ch.into()
                                })
                                .collect();

                            FlatUExpression::with_bits(res)
                        } else {
                            self.default_xor(
                                statements_flattened,
                                UExpression::and(a, b).metadata(left_metadata),
                                UExpression::and(aa, c).metadata(right_metadata),
                            )
                        }
                    }
                    (UExpressionInner::Xor(e), c) => {
                        let a_metadata = e.left.metadata.clone().unwrap();
                        let b_metadata = e.right.metadata.clone().unwrap();

                        let a_span = e.left.get_span();
                        let b_span = e.right.get_span();
                        let c_span = right_span;

                        match (e.left.into_inner(), e.right.into_inner(), c) {
                            (
                                UExpressionInner::And(e0),
                                UExpressionInner::And(e1),
                                UExpressionInner::And(e2),
                            ) => {
                                let a = *e0.left;
                                let b = *e0.right;
                                let aa = *e1.left;
                                let c = *e1.right;
                                let bb = *e2.left;
                                let cc = *e2.right;

                                if (aa == a) && (bb == b) && (cc == c) {
                                    let a_flattened =
                                        self.flatten_uint_expression(statements_flattened, a);
                                    let b_flattened =
                                        self.flatten_uint_expression(statements_flattened, b);
                                    let c_flattened =
                                        self.flatten_uint_expression(statements_flattened, c);

                                    let a_bits = a_flattened.bits.unwrap();
                                    let b_bits = b_flattened.bits.unwrap();
                                    let c_bits = c_flattened.bits.unwrap();

                                    let res: Vec<FlatExpression<T>> = a_bits
                                        .into_iter()
                                        .zip(b_bits.into_iter())
                                        .zip(c_bits.into_iter())
                                        .map(|((a, b), c)| {
                                            // (b) * (c) = (bc)
                                            // (2bc - b - c) * (a) = bc - maj

                                            let maj = self.use_sym();
                                            let bc = self.use_sym();

                                            statements_flattened.extend(vec![
                                                FlatStatement::directive(
                                                    vec![maj],
                                                    Solver::ShaAndXorAndXorAnd,
                                                    vec![a.clone(), b.clone(), c.clone()],
                                                ),
                                                FlatStatement::condition(
                                                    bc.into(),
                                                    FlatExpression::mul(b.clone(), c.clone()),
                                                    RuntimeError::ShaXor,
                                                ),
                                                FlatStatement::condition(
                                                    FlatExpression::sub(bc.into(), maj.into()),
                                                    FlatExpression::mul(
                                                        FlatExpression::sub(
                                                            FlatExpression::add(
                                                                bc.into(),
                                                                bc.into(),
                                                            ),
                                                            FlatExpression::add(b, c),
                                                        ),
                                                        a,
                                                    ),
                                                    RuntimeError::ShaXor,
                                                ),
                                            ]);
                                            maj.into()
                                        })
                                        .collect();

                                    FlatUExpression::with_bits(res)
                                } else {
                                    self.default_xor(
                                        statements_flattened,
                                        UExpression::xor(
                                            UExpression::and(a, b)
                                                .metadata(a_metadata)
                                                .span(a_span),
                                            UExpression::and(aa, c)
                                                .metadata(b_metadata)
                                                .span(b_span),
                                        )
                                        .metadata(left_metadata)
                                        .span(left_span),
                                        UExpression::and(bb, cc)
                                            .metadata(right_metadata)
                                            .span(c_span),
                                    )
                                }
                            }
                            (a, b, c) => self.default_xor(
                                statements_flattened,
                                UExpression::xor(
                                    a.annotate(target_bitwidth)
                                        .metadata(a_metadata)
                                        .span(a_span),
                                    b.annotate(target_bitwidth)
                                        .metadata(b_metadata)
                                        .span(b_span),
                                )
                                .metadata(left_metadata)
                                .span(left_span),
                                c.annotate(target_bitwidth)
                                    .metadata(right_metadata)
                                    .span(c_span),
                            ),
                        }
                    }
                    (left_i, right_i) => self.default_xor(
                        statements_flattened,
                        left_i
                            .annotate(target_bitwidth)
                            .metadata(left_metadata)
                            .span(left_span),
                        right_i
                            .annotate(target_bitwidth)
                            .metadata(right_metadata)
                            .span(right_span),
                    ),
                }
            }
            UExpressionInner::And(e) => {
                let left_flattened = self.flatten_uint_expression(statements_flattened, *e.left);

                let right_flattened = self.flatten_uint_expression(statements_flattened, *e.right);

                let left_bits = left_flattened.bits.unwrap();
                let right_bits = right_flattened.bits.unwrap();

                assert_eq!(left_bits.len(), target_bitwidth.to_usize());
                assert_eq!(right_bits.len(), target_bitwidth.to_usize());

                let and: Vec<_> = left_bits
                    .into_iter()
                    .zip(right_bits.into_iter())
                    .map(|(x, y)| match (x, y) {
                        (FlatExpression::Value(n), e) | (e, FlatExpression::Value(n)) => {
                            if n.value == T::from(0) {
                                FlatExpression::value(T::from(0))
                            } else if n.value == T::from(1) {
                                e
                            } else {
                                unreachable!();
                            }
                        }
                        (x, y) => self
                            .define(FlatExpression::mul(x, y), statements_flattened)
                            .into(),
                    })
                    .collect();

                FlatUExpression::with_bits(and)
            }
            UExpressionInner::Or(e) => {
                let left_flattened = self.flatten_uint_expression(statements_flattened, *e.left);
                let right_flattened = self.flatten_uint_expression(statements_flattened, *e.right);

                let left_bits = left_flattened.bits.unwrap();
                let right_bits = right_flattened.bits.unwrap();

                assert_eq!(left_bits.len(), target_bitwidth.to_usize());
                assert_eq!(right_bits.len(), target_bitwidth.to_usize());

                assert_eq!(left_bits.len(), target_bitwidth.to_usize());
                assert_eq!(right_bits.len(), target_bitwidth.to_usize());

                let or: Vec<FlatExpression<T>> = left_bits
                    .into_iter()
                    .zip(right_bits.into_iter())
                    .map(|(x, y)| match (x, y) {
                        (FlatExpression::Value(n), e) | (e, FlatExpression::Value(n)) => {
                            if n.value == T::from(0) {
                                self.define(e, statements_flattened).into()
                            } else if n.value == T::from(1) {
                                FlatExpression::value(T::from(1))
                            } else {
                                unreachable!()
                            }
                        }
                        (x, y) => {
                            let name = self.use_sym();

                            statements_flattened.extend(vec![
                                FlatStatement::directive(
                                    vec![name],
                                    Solver::Or,
                                    vec![x.clone(), y.clone()],
                                ),
                                FlatStatement::condition(
                                    FlatExpression::add(
                                        x.clone(),
                                        FlatExpression::sub(y.clone(), name.into()),
                                    ),
                                    FlatExpression::mul(x, y),
                                    RuntimeError::Or,
                                ),
                            ]);
                            name.into()
                        }
                    })
                    .collect();

                FlatUExpression::with_bits(or)
            }
        }
        .span(span);

        let res = match should_reduce {
            true => {
                let bits = self.get_bits_unchecked(
                    &res,
                    actual_bitwidth,
                    target_bitwidth.to_usize(),
                    statements_flattened,
                    RuntimeError::Sum,
                );

                let field = if actual_bitwidth > target_bitwidth.to_usize() {
                    bits.iter().enumerate().fold(
                        FlatExpression::value(T::from(0)),
                        |acc, (index, bit)| {
                            FlatExpression::add(
                                acc,
                                FlatExpression::mul(
                                    FlatExpression::value(
                                        T::from(2).pow(target_bitwidth.to_usize() - index - 1),
                                    ),
                                    bit.clone(),
                                ),
                            )
                        },
                    )
                } else {
                    res.get_field_unchecked()
                };

                FlatUExpression::with_bits(bits).field(field)
            }
            false => res,
        };

        statements_flattened.set_span(span_backup);

        res
    }

    /// Get the bits for a FlatUExpression
    ///
    /// # Arguments
    ///
    /// * `e` - the FlatUExpression to get the bits from
    /// * `from` - the original bitwidth of `e`
    /// * `to` - the bitwidth of the output representation
    /// * `statement_buffer` - a buffer to add statements to
    /// * `error` - the error to throw at runtime in case anything fails
    ///
    /// # Notes
    /// * `from` and `to` must be smaller or equal to `T::get_required_bits()`, the bitwidth of the prime field
    /// * the result is not checked to be in range. This is fine for `to < T::get_required_bits()`, but otherwise it is the caller's responsibility to add that check
    fn get_bits_unchecked(
        &mut self,
        e: &FlatUExpression<T>,
        from: usize,
        to: usize,
        statements_flattened: &mut FlatStatements<'ast, T>,
        error: RuntimeError,
    ) -> Vec<FlatExpression<T>> {
        assert!(from <= T::get_required_bits());
        assert!(to <= T::get_required_bits());

        // constants do not require directives
        if let Some(FlatExpression::Value(ref x)) = e.field {
            let bits: Vec<_> = Interpreter::execute_solver(&Solver::bits(to), &[x.value], &[])
                .unwrap()
                .into_iter()
                .map(FlatExpression::value)
                .collect();

            assert_eq!(bits.len(), to);

            self.bits_cache
                .insert(e.field.clone().unwrap(), bits.clone());
            return bits;
        };

        e.bits.clone().unwrap_or_else(|| {
            // we are not reducing a constant, therefore the result should always have a smaller bitwidth:
            // `to` is the target bitwidth, and `from` cannot be smaller than that unless we're looking at a
            // constant

            let from = std::cmp::max(from, to);
            let res = match self.bits_cache.entry(e.field.clone().unwrap()) {
                Entry::Occupied(entry) => {
                    let res: Vec<_> = entry.get().clone();
                    // if we already know a decomposition, its number of elements has to be smaller or equal to `to`
                    assert!(res.len() <= to);

                    // we then pad it with zeroes on the left (big endian) to return `to` bits
                    if res.len() == to {
                        res
                    } else {
                        (0..to - res.len())
                            .map(|_| FlatExpression::value(T::zero()))
                            .chain(res)
                            .collect()
                    }
                }
                Entry::Vacant(_) => {
                    let bits = (0..from).map(|_| self.use_sym()).collect::<Vec<_>>();
                    statements_flattened.push_back(FlatStatement::directive(
                        bits.clone(),
                        Solver::Bits(from),
                        vec![e.field.clone().unwrap()],
                    ));

                    let bits: Vec<_> = bits.into_iter().map(FlatExpression::identifier).collect();

                    // decompose to the actual bitwidth

                    // bit checks
                    statements_flattened.extend(bits.iter().take(from).map(|bit| {
                        FlatStatement::condition(
                            bit.clone(),
                            FlatExpression::mul(bit.clone(), bit.clone()),
                            RuntimeError::Bitness,
                        )
                    }));

                    let sum = flat_expression_from_bits(bits.clone());

                    // sum check
                    statements_flattened.push_back(FlatStatement::condition(
                        e.field.clone().unwrap(),
                        sum.clone(),
                        error,
                    ));

                    // truncate to the `to` lowest bits
                    let bits = bits[from - to..].to_vec();

                    assert_eq!(bits.len(), to);

                    self.bits_cache
                        .insert(e.field.clone().unwrap(), bits.clone());
                    self.bits_cache.insert(sum, bits.clone());

                    bits
                }
            };

            assert_eq!(res.len(), to);

            res
        })
    }

    fn flatten_select_expression<U: Flatten<'ast, T>>(
        &mut self,
        statements_flattened: &mut FlatStatements<'ast, T>,
        e: SelectExpression<'ast, T, U>,
    ) -> FlatUExpression<T> {
        let span = e.get_span();

        let array = e.array;
        let index = *e.index;

        let (range_check, result) = array
            .into_iter()
            .enumerate()
            .map(|(i, e)| {
                let condition = self.flatten_boolean_expression(
                    statements_flattened,
                    BooleanExpression::uint_eq(
                        UExpression::value(i as u128)
                            .annotate(UBitwidth::B32)
                            .metadata(UMetadata {
                                should_reduce: ShouldReduce::True,
                                max: T::from(i),
                            })
                            .span(span),
                        index.clone(),
                    )
                    .span(span),
                );

                let element = e.flatten(self, statements_flattened);

                (condition, element)
            })
            .collect::<Vec<_>>()
            .into_iter()
            .fold(
                (
                    FlatExpression::value(T::zero()),
                    FlatExpression::value(T::zero()),
                ),
                |(mut range_check, mut result), (condition, element)| {
                    range_check = FlatExpression::add(range_check, condition.clone()).span(span);

                    let conditional_element_id = self.use_sym();
                    statements_flattened.push_back(
                        FlatStatement::definition(
                            conditional_element_id,
                            FlatExpression::mul(condition, element.flat()).span(span),
                        )
                        .span(span),
                    );

                    result = FlatExpression::add(result, conditional_element_id.into()).span(span);
                    (range_check, result)
                },
            );

        statements_flattened.push_back(FlatStatement::condition(
            range_check,
            FlatExpression::value(T::one()),
            RuntimeError::SelectRangeCheck,
        ));
        FlatUExpression::with_field(result)
    }

    /// Flattens a field expression
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `expr` - `FieldElementExpression` that will be flattened.
    fn flatten_field_expression(
        &mut self,
        statements_flattened: &mut FlatStatements<'ast, T>,
        expr: FieldElementExpression<'ast, T>,
    ) -> FlatExpression<T> {
        let span = expr.get_span();

        let span_backup = statements_flattened.span;

        statements_flattened.set_span(span);

        let res = match expr {
            FieldElementExpression::Value(x) => FlatExpression::Value(x), // force to be a field element
            FieldElementExpression::Identifier(x) => FlatExpression::identifier(
                *self.layout.get(&x.id).unwrap_or_else(|| panic!("{}", x)),
            ),
            FieldElementExpression::Select(e) => self
                .flatten_select_expression(statements_flattened, e)
                .get_field_unchecked(),
            FieldElementExpression::Add(e) => {
                let left_flattened = self.flatten_field_expression(statements_flattened, *e.left);
                let right_flattened = self.flatten_field_expression(statements_flattened, *e.right);
                let new_left = if left_flattened.is_linear() {
                    left_flattened
                } else {
                    let id = self.use_sym();
                    statements_flattened.push_back(FlatStatement::definition(id, left_flattened));
                    FlatExpression::identifier(id)
                };
                let new_right = if right_flattened.is_linear() {
                    right_flattened
                } else {
                    let id = self.use_sym();
                    statements_flattened.push_back(FlatStatement::definition(id, right_flattened));
                    FlatExpression::identifier(id)
                };
                FlatExpression::add(new_left, new_right)
            }
            FieldElementExpression::Sub(e) => {
                let left_flattened = self.flatten_field_expression(statements_flattened, *e.left);
                let right_flattened = self.flatten_field_expression(statements_flattened, *e.right);

                let new_left = if left_flattened.is_linear() {
                    left_flattened
                } else {
                    let id = self.use_sym();
                    statements_flattened.push_back(FlatStatement::definition(id, left_flattened));
                    FlatExpression::identifier(id)
                };
                let new_right = if right_flattened.is_linear() {
                    right_flattened
                } else {
                    let id = self.use_sym();
                    statements_flattened.push_back(FlatStatement::definition(id, right_flattened));
                    FlatExpression::identifier(id)
                };

                FlatExpression::sub(new_left, new_right)
            }
            FieldElementExpression::Mult(e) => {
                let left_flattened = self.flatten_field_expression(statements_flattened, *e.left);
                let right_flattened = self.flatten_field_expression(statements_flattened, *e.right);
                let new_left = if left_flattened.is_linear() {
                    left_flattened
                } else {
                    let id = self.use_sym();
                    statements_flattened.push_back(FlatStatement::definition(id, left_flattened));
                    FlatExpression::identifier(id)
                };
                let new_right = if right_flattened.is_linear() {
                    right_flattened
                } else {
                    let id = self.use_sym();
                    statements_flattened.push_back(FlatStatement::definition(id, right_flattened));
                    FlatExpression::identifier(id)
                };
                FlatExpression::mul(new_left, new_right)
            }
            FieldElementExpression::Div(e) => {
                let left_flattened = self.flatten_field_expression(statements_flattened, *e.left);
                let right_flattened = self.flatten_field_expression(statements_flattened, *e.right);
                let new_left: FlatExpression<T> = {
                    let id = self.use_sym();
                    statements_flattened.push_back(FlatStatement::definition(id, left_flattened));
                    id.into()
                };
                let new_right: FlatExpression<T> = {
                    let id = self.use_sym();
                    statements_flattened.push_back(FlatStatement::definition(id, right_flattened));
                    id.into()
                };

                // `right` is assumed to already be non-zero so this is an unchecked division
                // TODO: we could save one constraint here by reusing the inverse of `right` computed earlier

                let inverse = self.use_sym();

                // # c = a/b
                statements_flattened.push_back(FlatStatement::directive(
                    vec![inverse],
                    Solver::Div,
                    vec![new_left.clone(), new_right.clone()],
                ));

                // assert(c * b == a)
                statements_flattened.push_back(FlatStatement::condition(
                    new_left,
                    FlatExpression::mul(new_right, inverse.into()),
                    RuntimeError::Division,
                ));

                inverse.into()
            }
            FieldElementExpression::Pow(e) => {
                match e.right.into_inner() {
                    UExpressionInner::Value(ref exp) => {
                        // flatten the base expression
                        let base_flattened =
                            self.flatten_field_expression(statements_flattened, *e.left.clone());

                        // we require from the base to be linear
                        // TODO change that
                        assert!(base_flattened.is_linear());

                        // convert the exponent to bytes, big endian
                        let ebytes_be = exp.value.to_be_bytes();

                        // convert the bytes to bits, remove leading zeroes (we only need powers up to the highest non-zero bit)
                        #[allow(clippy::needless_collect)]
                        // collecting is required as we then reverse
                        let ebits_be: Vec<_> = ebytes_be
                            .iter()
                            .flat_map(|byte| (0..8).rev().map(move |i| byte & (1 << i) != 0)) // byte to bit, big endian
                            .skip_while(|b| !b) // skip trailing false bits
                            .collect();

                        // reverse to start with the lowest bit first
                        let ebits_le: Vec<_> = ebits_be.into_iter().rev().collect();

                        // calculate all powers e**(2**i) by squaring
                        let powers: Vec<FlatExpression<T>> = ebits_le
                            .iter()
                            .scan(None, |state, _| {
                                match state {
                                    // the first element is the base
                                    None => {
                                        *state = Some(base_flattened.clone());
                                        Some(base_flattened.clone())
                                    }
                                    // any subsequent element is the square of the previous one
                                    Some(previous) => {
                                        // introduce a new variable
                                        let id = self.use_sym();
                                        // set it to the square of the previous one, stored in state
                                        statements_flattened.push_back(FlatStatement::definition(
                                            id,
                                            FlatExpression::mul(previous.clone(), previous.clone()),
                                        ));
                                        // store it in the state for later squaring
                                        *state = Some(FlatExpression::identifier(id));
                                        // return it for later use constructing the result
                                        Some(FlatExpression::identifier(id))
                                    }
                                }
                            })
                            .collect();

                        // construct the result iterating through the bits, multiplying by the associated power iff the bit is true
                        ebits_le.into_iter().zip(powers).fold(
                            FlatExpression::value(T::from(1)), // initialise the result at 1. If we have no bits to iterate through, we're computing x**0 == 1
                            |acc, (bit, power)| match bit {
                                true => {
                                    // update the result by introducing a new variable
                                    let id = self.use_sym();
                                    statements_flattened.push_back(FlatStatement::definition(
                                        id,
                                        FlatExpression::mul(acc, power), // set the new result to the current result times the current power
                                    ));
                                    FlatExpression::identifier(id)
                                }
                                false => acc, // this bit is false, keep the previous result
                            },
                        )
                    }
                    _ => panic!("Expected number as pow exponent"),
                }
            }
            FieldElementExpression::Conditional(e) => self
                .flatten_conditional_expression(statements_flattened, e)
                .get_field_unchecked(),
            _ => unreachable!(),
        };

        statements_flattened.set_span(span_backup);

        res
    }

    fn flatten_assembly_statement(
        &mut self,
        statements_flattened: &mut FlatStatements<'ast, T>,
        stat: ZirAssemblyStatement<'ast, T>,
    ) {
        let span = stat.get_span();

        let span_backup = statements_flattened.span;

        statements_flattened.set_span(span);

        match stat {
            ZirAssemblyStatement::Assignment(s) => {
                let inputs: Vec<FlatExpression<T>> = s
                    .expression
                    .arguments
                    .iter()
                    .cloned()
                    .map(|p| self.layout.get(&p.id.id).cloned().unwrap().into())
                    .collect();

                let outputs: Vec<Variable> = s
                    .assignee
                    .into_iter()
                    .map(|assignee| self.use_variable(&assignee))
                    .collect();

                let mut canonicalizer = ZirCanonicalizer::default();
                let function = canonicalizer.fold_function(s.expression);

                let directive = FlatDirective::new(outputs, Solver::Zir(function), inputs);
                statements_flattened.push_back(FlatStatement::Directive(directive));
            }
            ZirAssemblyStatement::Constraint(s) => {
                let lhs = self.flatten_field_expression(statements_flattened, s.left);
                let rhs = self.flatten_field_expression(statements_flattened, s.right);
                statements_flattened.push_back(FlatStatement::condition(
                    lhs,
                    rhs,
                    RuntimeError::SourceAssemblyConstraint(s.metadata),
                ));
            }
        };

        statements_flattened.set_span(span_backup);
    }

    /// Flattens a statement
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - Vector where new flattened statements can be added.
    /// * `stat` - `ZirStatement` that will be flattened.
    fn flatten_statement(
        &mut self,
        statements_flattened: &mut FlatStatements<'ast, T>,
        s: ZirStatement<'ast, T>,
    ) {
        let span = s.get_span();

        let span_backup = statements_flattened.span;

        statements_flattened.set_span(span);

        match s {
            ZirStatement::Return(s) => {
                #[allow(clippy::needless_collect)]
                // clippy suggests to not collect here, but `statements_flattened` is borrowed in the iterator,
                // so we cannot borrow again when extending
                let flat_expressions: Vec<_> = s
                    .inner
                    .into_iter()
                    .map(|expr| self.flatten_expression(statements_flattened, expr))
                    .map(|x| x.get_field_unchecked())
                    .collect();

                statements_flattened.extend(
                    flat_expressions
                        .into_iter()
                        .enumerate()
                        .map(|(index, e)| FlatStatement::definition(Variable::public(index), e)),
                );
            }
            ZirStatement::Assembly(s) => {
                let mut block_statements = FlatStatements::default();
                block_statements.set_span(s.get_span());

                for s in s.inner {
                    self.flatten_assembly_statement(&mut block_statements, s);
                }
                statements_flattened
                    .push_back(FlatStatement::block(block_statements.buffer.into()));
            }
            ZirStatement::IfElse(s) => {
                let condition_flat =
                    self.flatten_boolean_expression(statements_flattened, s.condition.clone());

                let condition_id = self.use_sym();
                statements_flattened
                    .push_back(FlatStatement::definition(condition_id, condition_flat));

                if self.config.isolate_branches {
                    let mut consequence_statements = FlatStatements::default();
                    let mut alternative_statements = FlatStatements::default();

                    s.consequence
                        .into_iter()
                        .for_each(|s| self.flatten_statement(&mut consequence_statements, s));
                    s.alternative
                        .into_iter()
                        .for_each(|s| self.flatten_statement(&mut alternative_statements, s));

                    let consequence_statements =
                        self.make_conditional(consequence_statements, condition_id.into());
                    let alternative_statements = self.make_conditional(
                        alternative_statements,
                        FlatExpression::sub(FlatExpression::value(T::one()), condition_id.into()),
                    );

                    statements_flattened.extend(consequence_statements);
                    statements_flattened.extend(alternative_statements);
                } else {
                    s.consequence
                        .into_iter()
                        .for_each(|s| self.flatten_statement(statements_flattened, s));
                    s.alternative
                        .into_iter()
                        .for_each(|s| self.flatten_statement(statements_flattened, s));
                }
            }
            ZirStatement::Definition(s) => {
                // define n variables with n the number of primitive types for v_type
                // assign them to the n primitive types for expr

                let assignee = s.assignee;
                let expr = s.rhs;

                let rhs = self.flatten_expression(statements_flattened, expr);

                let bits = rhs.bits.clone();

                let var = match rhs.get_field_unchecked() {
                    FlatExpression::Identifier(id) => {
                        self.use_variable_with_existing(&assignee, id.id);
                        id.id
                    }
                    e => {
                        let var = self.use_variable(&assignee);

                        // handle return of function call
                        statements_flattened.push_back(FlatStatement::definition(var, e));

                        var
                    }
                };

                // register bits
                if let Some(bits) = bits {
                    self.bits_cache
                        .insert(FlatExpression::identifier(var), bits);
                }
            }
            ZirStatement::Assertion(s) => {
                let e = s.expression;
                let error = s.error;

                match e {
                    BooleanExpression::And(..) => {
                        for boolean in e.into_conjunction_iterator() {
                            self.flatten_statement(
                                statements_flattened,
                                ZirStatement::assertion(boolean, error.clone()).span(span),
                            )
                        }
                    }
                    BooleanExpression::FieldEq(e) => {
                        let lhs = self.flatten_field_expression(statements_flattened, *e.left);
                        let rhs = self.flatten_field_expression(statements_flattened, *e.right);

                        self.flatten_equality_assertion(
                            statements_flattened,
                            lhs,
                            rhs,
                            error.into(),
                        )
                    }
                    BooleanExpression::FieldLt(e) => {
                        let lhs = self.flatten_field_expression(statements_flattened, *e.left);
                        let rhs = self.flatten_field_expression(statements_flattened, *e.right);

                        match (lhs, rhs) {
                            (e, FlatExpression::Value(c)) => self.enforce_constant_lt_check(
                                statements_flattened,
                                e,
                                c.value,
                                error.into(),
                            ),
                            // c < e <=> p - 1 - e < p - 1 - c
                            (FlatExpression::Value(c), e) => self.enforce_constant_lt_check(
                                statements_flattened,
                                FlatExpression::sub(T::max_value().into(), e),
                                T::max_value() - c.value,
                                error.into(),
                            ),
                            (lhs, rhs) => {
                                let bit_width = T::get_required_bits();
                                let safe_width = bit_width - 2; // dynamic comparison is not complete
                                let e = self.lt_check(statements_flattened, lhs, rhs, safe_width);
                                statements_flattened.push_back(FlatStatement::condition(
                                    e,
                                    FlatExpression::value(T::one()),
                                    error.into(),
                                ));
                            }
                        }
                    }
                    BooleanExpression::FieldLe(e) => {
                        let lhs = self.flatten_field_expression(statements_flattened, *e.left);
                        let rhs = self.flatten_field_expression(statements_flattened, *e.right);

                        match (lhs, rhs) {
                            (e, FlatExpression::Value(c)) => self.enforce_constant_le_check(
                                statements_flattened,
                                e,
                                c.value,
                                error.into(),
                            ),
                            // c <= e <=> p - 1 - e <= p - 1 - c
                            (FlatExpression::Value(c), e) => self.enforce_constant_le_check(
                                statements_flattened,
                                FlatExpression::sub(T::max_value().into(), e),
                                T::max_value() - c.value,
                                error.into(),
                            ),
                            (lhs, rhs) => {
                                let bit_width = T::get_required_bits();
                                let safe_width = bit_width - 2; // dynamic comparison is not complete
                                let e = self.le_check(statements_flattened, lhs, rhs, safe_width);
                                statements_flattened.push_back(FlatStatement::condition(
                                    e,
                                    FlatExpression::value(T::one()),
                                    error.into(),
                                ));
                            }
                        }
                    }
                    BooleanExpression::UintLe(e) => {
                        let lhs = self
                            .flatten_uint_expression(statements_flattened, *e.left)
                            .get_field_unchecked();
                        let rhs = self
                            .flatten_uint_expression(statements_flattened, *e.right)
                            .get_field_unchecked();

                        match (lhs, rhs) {
                            (e, FlatExpression::Value(c)) => self.enforce_constant_le_check(
                                statements_flattened,
                                e,
                                c.value,
                                error.into(),
                            ),
                            // c <= e <=> p - 1 - e <= p - 1 - c
                            (FlatExpression::Value(c), e) => self.enforce_constant_le_check(
                                statements_flattened,
                                FlatExpression::sub(T::max_value().into(), e),
                                T::max_value() - c.value,
                                error.into(),
                            ),
                            (lhs, rhs) => {
                                let bit_width = T::get_required_bits();
                                let safe_width = bit_width - 2; // dynamic comparison is not complete
                                let e = self.le_check(statements_flattened, lhs, rhs, safe_width);
                                statements_flattened.push_back(FlatStatement::condition(
                                    e,
                                    FlatExpression::value(T::one()),
                                    error.into(),
                                ));
                            }
                        }
                    }
                    BooleanExpression::UintEq(e) => {
                        let lhs = self
                            .flatten_uint_expression(statements_flattened, *e.left)
                            .get_field_unchecked();
                        let rhs = self
                            .flatten_uint_expression(statements_flattened, *e.right)
                            .get_field_unchecked();

                        self.flatten_equality_assertion(
                            statements_flattened,
                            lhs,
                            rhs,
                            error.into(),
                        )
                    }
                    BooleanExpression::BoolEq(e) => {
                        let lhs = self.flatten_boolean_expression(statements_flattened, *e.left);
                        let rhs = self.flatten_boolean_expression(statements_flattened, *e.right);

                        self.flatten_equality_assertion(
                            statements_flattened,
                            lhs,
                            rhs,
                            error.into(),
                        )
                    }
                    BooleanExpression::Not(u) => {
                        let inner_span = u.get_span();

                        match *u.inner {
                            BooleanExpression::UintEq(b) => {
                                if let UExpressionInner::Value(ValueExpression {
                                    value: 0, ..
                                }) = b.left.inner
                                {
                                    let x = self
                                        .flatten_uint_expression(statements_flattened, *b.right)
                                        .get_field_unchecked();
                                    self.enforce_not_zero_assertion(statements_flattened, x)
                                } else if let UExpressionInner::Value(ValueExpression {
                                    value: 0,
                                    ..
                                }) = b.right.inner
                                {
                                    let x = self
                                        .flatten_uint_expression(statements_flattened, *b.left)
                                        .get_field_unchecked();
                                    self.enforce_not_zero_assertion(statements_flattened, x)
                                } else {
                                    self.enforce_naive_assertion(
                                        statements_flattened,
                                        BooleanExpression::not(BooleanExpression::UintEq(b)),
                                        error,
                                    );
                                }
                            }
                            BooleanExpression::FieldEq(b) => match (*b.left, *b.right) {
                                (
                                    FieldElementExpression::Value(ValueExpression {
                                        value: zero,
                                        ..
                                    }),
                                    x,
                                )
                                | (
                                    x,
                                    FieldElementExpression::Value(ValueExpression {
                                        value: zero,
                                        ..
                                    }),
                                ) if zero == T::from(0) => {
                                    let x = self.flatten_field_expression(statements_flattened, x);
                                    self.enforce_not_zero_assertion(statements_flattened, x)
                                }
                                (left, right) => self.enforce_naive_assertion(
                                    statements_flattened,
                                    BooleanExpression::not(
                                        BooleanExpression::field_eq(left, right).span(inner_span),
                                    )
                                    .span(span),
                                    error,
                                ),
                            },
                            e => self.enforce_naive_assertion(
                                statements_flattened,
                                BooleanExpression::not(e.span(inner_span)).span(span),
                                error,
                            ),
                        }
                    }
                    e => self.enforce_naive_assertion(statements_flattened, e, error),
                }
            }
            ZirStatement::MultipleDefinition(s) => {
                // flatten the right side to p = sum(var_i.type.primitive_count) expressions
                // define p new variables to the right side expressions

                match s.rhs {
                    ZirExpressionList::EmbedCall(embed, generics, exprs) => {
                        let rhs_flattened = self.flatten_embed_call(
                            statements_flattened,
                            embed,
                            generics,
                            exprs.clone(),
                        );

                        let rhs = rhs_flattened.into_iter();

                        assert_eq!(s.assignees.len(), rhs.len());

                        let assignees: Vec<_> = s
                            .assignees
                            .into_iter()
                            .zip(rhs)
                            .map(|(v, r)| match r.get_field_unchecked() {
                                FlatExpression::Identifier(id) => {
                                    self.use_variable_with_existing(&v, id.id);
                                    id.id
                                }
                                e => {
                                    let id = self.use_variable(&v);
                                    statements_flattened
                                        .push_back(FlatStatement::definition(id, e));
                                    id
                                }
                            })
                            .collect();

                        match embed {
                            FlatEmbed::U64FromBits
                            | FlatEmbed::U32FromBits
                            | FlatEmbed::U16FromBits
                            | FlatEmbed::U8FromBits => {
                                let bits = exprs
                                    .into_iter()
                                    .map(|e| {
                                        self.flatten_expression(statements_flattened, e)
                                            .get_field_unchecked()
                                    })
                                    .collect();
                                self.bits_cache.insert(assignees[0].into(), bits);
                            }
                            _ => {}
                        }
                    }
                }
            }
            ZirStatement::Log(s) => {
                let expressions = s
                    .expressions
                    .into_iter()
                    .map(|(t, e)| {
                        (
                            t,
                            e.into_iter()
                                .map(|e| {
                                    self.flatten_expression(statements_flattened, e)
                                        .get_field_unchecked()
                                })
                                .collect(),
                        )
                    })
                    .collect();

                statements_flattened.push_back(FlatStatement::Log(LogStatement::new(
                    s.format_string,
                    expressions,
                )));
            }
        };

        statements_flattened.set_span(span_backup);
    }

    fn enforce_naive_assertion(
        &mut self,
        statements_flattened: &mut FlatStatements<'ast, T>,
        e: BooleanExpression<'ast, T>,
        error: zokrates_ast::zir::RuntimeError,
    ) {
        // naive approach: flatten the boolean to a single field element and constrain it to 1
        let e = self.flatten_boolean_expression(statements_flattened, e);

        if e.is_linear() {
            statements_flattened.push_back(FlatStatement::condition(
                e,
                FlatExpression::value(T::from(1)),
                error.into(),
            ));
        } else {
            // swap so that left side is linear
            statements_flattened.push_back(FlatStatement::condition(
                FlatExpression::value(T::from(1)),
                e,
                error.into(),
            ));
        }
    }

    /// Enforce that x is not zero
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - `FlatStatements<'ast, T>` Vector where new flattened statements can be added.
    /// * `x` - `FlatExpression<T>` The expression to be constrained to not be zero.
    fn enforce_not_zero_assertion(
        &mut self,
        statements_flattened: &mut FlatStatements<'ast, T>,
        x: FlatExpression<T>,
    ) {
        // introduce intermediate variable
        let x_id = self.define(x, statements_flattened);

        // check that `x` is not 0 by giving its inverse
        let invx = self.use_sym();

        // # invx = 1/x
        statements_flattened.push_back(FlatStatement::Directive(FlatDirective::new(
            vec![invx],
            Solver::Div,
            vec![FlatExpression::value(T::one()), x_id.into()],
        )));

        // assert(invx * x == 1)
        statements_flattened.push_back(FlatStatement::condition(
            FlatExpression::value(T::one()),
            FlatExpression::mul(invx.into(), x_id.into()),
            RuntimeError::Inverse,
        ));
    }

    /// Flattens an equality assertion, enforcing it in the circuit.
    ///
    /// # Arguments
    ///
    /// * `statements_flattened` - `FlatStatements<'ast, T>` Vector where new flattened statements can be added.
    /// * `lhs` - `FlatExpression<T>` Left-hand side of the equality expression.
    /// * `rhs` - `FlatExpression<T>` Right-hand side of the equality expression.
    fn flatten_equality_assertion(
        &mut self,
        statements_flattened: &mut FlatStatements<'ast, T>,
        lhs: FlatExpression<T>,
        rhs: FlatExpression<T>,
        error: RuntimeError,
    ) {
        let (lhs, rhs) = match (lhs, rhs) {
            (FlatExpression::Mult(e), z) | (z, FlatExpression::Mult(e)) => (
                self.identify_expression(z, statements_flattened),
                FlatExpression::mul(
                    self.identify_expression(*e.left, statements_flattened),
                    self.identify_expression(*e.right, statements_flattened),
                ),
            ),
            (x, z) => (
                self.identify_expression(z, statements_flattened),
                FlatExpression::mul(
                    self.identify_expression(x, statements_flattened),
                    FlatExpression::value(T::from(1)),
                ),
            ),
        };
        statements_flattened.push_back(FlatStatement::condition(lhs, rhs, error));
    }

    /// Identifies a non-linear expression by assigning it to a new identifier.
    ///
    /// # Arguments
    ///
    /// * `e` - `FlatExpression<T>` Expression to be assigned to an identifier.
    /// * `statements_flattened` - `FlatStatements<'ast, T>` Vector where new flattened statements can be added.
    fn identify_expression(
        &mut self,
        e: FlatExpression<T>,
        statements_flattened: &mut FlatStatements<'ast, T>,
    ) -> FlatExpression<T> {
        match e.is_linear() {
            true => e,
            false => {
                let sym = self.use_sym();
                statements_flattened.push_back(FlatStatement::definition(sym, e));
                FlatExpression::identifier(sym)
            }
        }
    }

    /// Returns a fresh Variable for a given Variable
    /// # Arguments
    ///
    /// * `variable` - a variable in the program being flattened
    fn use_variable(&mut self, variable: &ZirVariable<'ast>) -> Variable {
        let var = self.issue_new_variable();

        self.layout.insert(variable.id.clone(), var);
        var
    }

    /// Reuse an existing variable for a new name
    /// # Arguments
    ///
    /// * `variable` - a variable in the program being flattened
    /// * `flat_variable` - an existing flat variable
    fn use_variable_with_existing(
        &mut self,
        variable: &ZirVariable<'ast>,
        flat_variable: Variable,
    ) {
        self.layout.insert(variable.id.clone(), flat_variable);
    }

    fn use_parameter(
        &mut self,
        parameter: &ZirParameter<'ast>,
        statements_flattened: &mut FlatStatements<'ast, T>,
    ) -> Parameter {
        let span = parameter.get_span();

        let backup_span = statements_flattened.span;

        statements_flattened.set_span(span);

        let variable = self.use_variable(&parameter.id);

        match parameter.id.get_type() {
            Type::Uint(bitwidth) => {
                // to constrain unsigned integer inputs to be in range, we get their bit decomposition.
                // it will be cached
                self.get_bits_unchecked(
                    &FlatUExpression::with_field(FlatExpression::identifier(variable)),
                    bitwidth.to_usize(),
                    bitwidth.to_usize(),
                    statements_flattened,
                    RuntimeError::Sum,
                );
            }
            Type::Boolean => {
                statements_flattened.push_back(FlatStatement::condition(
                    variable.into(),
                    FlatExpression::mul(variable.into(), variable.into()),
                    RuntimeError::ArgumentBitness,
                ));
            }
            Type::FieldElement => {}
        }

        statements_flattened.set_span(backup_span);

        Parameter::new(variable, parameter.private).span(span)
    }

    fn issue_new_variable(&mut self) -> Variable {
        let var = Variable::new(self.next_var_idx);
        self.next_var_idx += 1;
        var
    }

    // create an internal variable. We do not register it in the layout
    fn use_sym(&mut self) -> Variable {
        self.issue_new_variable()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_ast::zir;
    use zokrates_ast::zir::types::Signature;
    use zokrates_ast::zir::types::Type;
    use zokrates_ast::zir::Id;
    use zokrates_ast::zir::ZirFunction;
    use zokrates_field::Bn128Field;

    fn flatten_function<T: Field>(f: ZirFunction<T>) -> FlatProg<T> {
        from_program_and_config(
            ZirProgram {
                main: f,
                module_map: Default::default(),
            },
            CompileConfig::default(),
        )
        .collect()
    }

    #[test]
    fn assertion_bool_eq() {
        // def main() {
        //     bool x = true;
        //     bool y = true;
        //     assert(x == y);
        //     return;
        // }

        // def main() {
        //     _0 = 1;
        //     _1 = 1;
        //     _1 == (_0 * 1);
        // }
        let function = ZirFunction::<Bn128Field> {
            arguments: vec![],
            statements: vec![
                ZirStatement::definition(
                    zir::Variable::boolean("x".into()),
                    BooleanExpression::value(true).into(),
                ),
                ZirStatement::definition(
                    zir::Variable::boolean("y".into()),
                    BooleanExpression::value(true).into(),
                ),
                ZirStatement::assertion(
                    BooleanExpression::bool_eq(
                        BooleanExpression::identifier("x".into()),
                        BooleanExpression::identifier("y".into()),
                    ),
                    zir::RuntimeError::mock(),
                ),
                ZirStatement::ret(vec![]),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![],
            },
        };

        let flat = flatten_function(function);
        let expected = FlatFunction {
            module_map: Default::default(),
            arguments: vec![],
            return_count: 0,
            statements: vec![
                FlatStatement::definition(
                    Variable::new(0),
                    FlatExpression::value(Bn128Field::from(1)),
                ),
                FlatStatement::definition(
                    Variable::new(1),
                    FlatExpression::value(Bn128Field::from(1)),
                ),
                FlatStatement::condition(
                    FlatExpression::identifier(Variable::new(1)),
                    FlatExpression::mul(
                        FlatExpression::identifier(Variable::new(0)),
                        FlatExpression::value(Bn128Field::from(1)),
                    ),
                    zir::RuntimeError::mock().into(),
                ),
            ],
        };

        assert_eq!(flat.collect(), expected);
    }

    #[test]
    fn assertion_field_eq() {
        // def main() {
        //     field x = 1;
        //     field y = 2;
        //     assert(x + 1 == y);
        //     return;
        // }

        // def main() {
        //     _0 = 42;
        //     _1 = 42;
        //     _1 == ((_0 + 1) * 1);
        // }
        let function = ZirFunction {
            arguments: vec![],
            statements: vec![
                ZirStatement::definition(
                    zir::Variable::field_element("x"),
                    FieldElementExpression::value(Bn128Field::from(1)).into(),
                ),
                ZirStatement::definition(
                    zir::Variable::field_element("y"),
                    FieldElementExpression::value(Bn128Field::from(2)).into(),
                ),
                ZirStatement::assertion(
                    BooleanExpression::field_eq(
                        FieldElementExpression::add(
                            FieldElementExpression::identifier("x".into()),
                            FieldElementExpression::value(Bn128Field::from(1)),
                        ),
                        FieldElementExpression::identifier("y".into()),
                    ),
                    zir::RuntimeError::mock(),
                ),
                ZirStatement::ret(vec![]),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![],
            },
        };

        let flat = flatten_function(function);

        let expected = FlatFunction {
            module_map: Default::default(),
            arguments: vec![],
            return_count: 0,
            statements: vec![
                FlatStatement::definition(
                    Variable::new(0),
                    FlatExpression::value(Bn128Field::from(1)),
                ),
                FlatStatement::definition(
                    Variable::new(1),
                    FlatExpression::value(Bn128Field::from(2)),
                ),
                FlatStatement::condition(
                    FlatExpression::identifier(Variable::new(1)),
                    FlatExpression::mul(
                        FlatExpression::add(
                            FlatExpression::identifier(Variable::new(0)),
                            FlatExpression::value(Bn128Field::from(1)),
                        ),
                        FlatExpression::value(Bn128Field::from(1)),
                    ),
                    zir::RuntimeError::mock().into(),
                ),
            ],
        };

        assert_eq!(flat.collect(), expected);
    }

    #[test]
    fn assertion_uint_eq() {
        // def main() {
        //     u32 x = 42;
        //     assert(x == 42);
        //     return;
        // }

        // def main() {
        //     _0 = 42;
        //     42 == (_0 * 1);
        // }
        let metadata = UMetadata {
            max: 0xffffffff_u32.into(),
            should_reduce: ShouldReduce::True,
        };
        let function = ZirFunction::<Bn128Field> {
            arguments: vec![],
            statements: vec![
                ZirStatement::definition(
                    zir::Variable::uint("x".into(), 32),
                    ZirExpression::Uint(
                        UExpression::value(42)
                            .annotate(32)
                            .metadata(metadata.clone()),
                    ),
                ),
                ZirStatement::assertion(
                    BooleanExpression::uint_eq(
                        UExpression::identifier("x".into())
                            .annotate(32)
                            .metadata(metadata.clone()),
                        UExpression::value(42).annotate(32).metadata(metadata),
                    ),
                    zir::RuntimeError::mock(),
                ),
                ZirStatement::ret(vec![]),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![],
            },
        };

        let flat = flatten_function(function);

        let expected = FlatFunction {
            module_map: Default::default(),
            arguments: vec![],
            return_count: 0,
            statements: vec![
                FlatStatement::definition(
                    Variable::new(0),
                    FlatExpression::value(Bn128Field::from(42)),
                ),
                FlatStatement::condition(
                    FlatExpression::value(Bn128Field::from(42)),
                    FlatExpression::mul(
                        FlatExpression::identifier(Variable::new(0)),
                        FlatExpression::value(Bn128Field::from(1)),
                    ),
                    zir::RuntimeError::mock().into(),
                ),
            ],
        };

        assert_eq!(flat.collect(), expected);
    }

    #[test]
    fn assertion_ident_eq_ident() {
        // def main() {
        //     field x = 2;
        //     field y = 2;
        //     assert(x == y);
        //     return;
        // }

        // def main() {
        //     _0 = 2;
        //     _1 = 2;
        //     _1 == (_0 * 1);
        // }
        let function = ZirFunction {
            arguments: vec![],
            statements: vec![
                ZirStatement::definition(
                    zir::Variable::field_element("x"),
                    FieldElementExpression::value(Bn128Field::from(2)).into(),
                ),
                ZirStatement::definition(
                    zir::Variable::field_element("y"),
                    FieldElementExpression::value(Bn128Field::from(2)).into(),
                ),
                ZirStatement::assertion(
                    BooleanExpression::field_eq(
                        FieldElementExpression::identifier("x".into()),
                        FieldElementExpression::identifier("y".into()),
                    ),
                    zir::RuntimeError::mock(),
                ),
                ZirStatement::ret(vec![]),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![],
            },
        };

        let flat = flatten_function(function);

        let expected = FlatFunction {
            module_map: Default::default(),
            arguments: vec![],
            return_count: 0,
            statements: vec![
                FlatStatement::definition(
                    Variable::new(0),
                    FlatExpression::value(Bn128Field::from(2)),
                ),
                FlatStatement::definition(
                    Variable::new(1),
                    FlatExpression::value(Bn128Field::from(2)),
                ),
                FlatStatement::condition(
                    FlatExpression::identifier(Variable::new(1)),
                    FlatExpression::mul(
                        FlatExpression::identifier(Variable::new(0)),
                        FlatExpression::value(Bn128Field::from(1)),
                    ),
                    zir::RuntimeError::mock().into(),
                ),
            ],
        };

        assert_eq!(flat.collect(), expected);
    }

    #[test]
    fn assertion_mult_eq_ident() {
        // def main() {
        //     field x = 2;
        //     field y = 2;
        //     field z = 4;
        //     assert(x * y == z);
        //     return;
        // }

        // def main() {
        //     _0 = 2;
        //     _1 = 2;
        //     _2 = 4;
        //     _2 == (_0 * _1);
        // }
        let function = ZirFunction {
            arguments: vec![],
            statements: vec![
                ZirStatement::definition(
                    zir::Variable::field_element("x"),
                    FieldElementExpression::value(Bn128Field::from(2)).into(),
                ),
                ZirStatement::definition(
                    zir::Variable::field_element("y"),
                    FieldElementExpression::value(Bn128Field::from(2)).into(),
                ),
                ZirStatement::definition(
                    zir::Variable::field_element("z"),
                    FieldElementExpression::value(Bn128Field::from(4)).into(),
                ),
                ZirStatement::assertion(
                    BooleanExpression::field_eq(
                        FieldElementExpression::mul(
                            FieldElementExpression::identifier("x".into()),
                            FieldElementExpression::identifier("y".into()),
                        ),
                        FieldElementExpression::identifier("z".into()),
                    ),
                    zir::RuntimeError::mock(),
                ),
                ZirStatement::ret(vec![]),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![],
            },
        };

        let flat = flatten_function(function);

        let expected = FlatFunction {
            module_map: Default::default(),
            arguments: vec![],
            return_count: 0,
            statements: vec![
                FlatStatement::definition(
                    Variable::new(0),
                    FlatExpression::value(Bn128Field::from(2)),
                ),
                FlatStatement::definition(
                    Variable::new(1),
                    FlatExpression::value(Bn128Field::from(2)),
                ),
                FlatStatement::definition(
                    Variable::new(2),
                    FlatExpression::value(Bn128Field::from(4)),
                ),
                FlatStatement::condition(
                    FlatExpression::identifier(Variable::new(2)),
                    FlatExpression::mul(
                        FlatExpression::identifier(Variable::new(0)),
                        FlatExpression::identifier(Variable::new(1)),
                    ),
                    zir::RuntimeError::mock().into(),
                ),
            ],
        };

        assert_eq!(flat.collect(), expected);
    }

    #[test]
    fn assertion_ident_eq_mult() {
        // def main() {
        //     field x = 2;
        //     field y = 2;
        //     field z = 4;
        //     assert(z == x * y);
        //     return;
        // }

        // def main() {
        //     _0 = 2;
        //     _1 = 2;
        //     _2 = 4;
        //     _2 == (_0 * _1);
        // }
        let function = ZirFunction {
            arguments: vec![],
            statements: vec![
                ZirStatement::definition(
                    zir::Variable::field_element("x"),
                    FieldElementExpression::value(Bn128Field::from(2)).into(),
                ),
                ZirStatement::definition(
                    zir::Variable::field_element("y"),
                    FieldElementExpression::value(Bn128Field::from(2)).into(),
                ),
                ZirStatement::definition(
                    zir::Variable::field_element("z"),
                    FieldElementExpression::value(Bn128Field::from(4)).into(),
                ),
                ZirStatement::assertion(
                    BooleanExpression::field_eq(
                        FieldElementExpression::identifier("z".into()),
                        FieldElementExpression::mul(
                            FieldElementExpression::identifier("x".into()),
                            FieldElementExpression::identifier("y".into()),
                        ),
                    ),
                    zir::RuntimeError::mock(),
                ),
                ZirStatement::ret(vec![]),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![],
            },
        };

        let flat = flatten_function(function);

        let expected = FlatFunction {
            module_map: Default::default(),
            arguments: vec![],
            return_count: 0,
            statements: vec![
                FlatStatement::definition(
                    Variable::new(0),
                    FlatExpression::value(Bn128Field::from(2)),
                ),
                FlatStatement::definition(
                    Variable::new(1),
                    FlatExpression::value(Bn128Field::from(2)),
                ),
                FlatStatement::definition(
                    Variable::new(2),
                    FlatExpression::value(Bn128Field::from(4)),
                ),
                FlatStatement::condition(
                    FlatExpression::identifier(Variable::new(2)),
                    FlatExpression::mul(
                        FlatExpression::identifier(Variable::new(0)),
                        FlatExpression::identifier(Variable::new(1)),
                    ),
                    zir::RuntimeError::mock().into(),
                ),
            ],
        };

        assert_eq!(flat.collect(), expected);
    }

    #[test]
    fn assertion_mult_eq_mult() {
        // def main() {
        //     field x = 4;
        //     field y = 4;
        //     field z = 8;
        //     field t = 2;
        //     assert(x * y == z * t);
        //     return;
        // }

        // def main() {
        //     _0 = 4;
        //     _1 = 4;
        //     _2 = 8;
        //     _3 = 2;
        //     _4 = (_2 * _3);
        //     _4 == (_0 * _1);
        // }
        let function = ZirFunction {
            arguments: vec![],
            statements: vec![
                ZirStatement::definition(
                    zir::Variable::field_element("x"),
                    FieldElementExpression::value(Bn128Field::from(4)).into(),
                ),
                ZirStatement::definition(
                    zir::Variable::field_element("y"),
                    FieldElementExpression::value(Bn128Field::from(4)).into(),
                ),
                ZirStatement::definition(
                    zir::Variable::field_element("z"),
                    FieldElementExpression::value(Bn128Field::from(8)).into(),
                ),
                ZirStatement::definition(
                    zir::Variable::field_element("t"),
                    FieldElementExpression::value(Bn128Field::from(2)).into(),
                ),
                ZirStatement::assertion(
                    BooleanExpression::field_eq(
                        FieldElementExpression::mul(
                            FieldElementExpression::identifier("x".into()),
                            FieldElementExpression::identifier("y".into()),
                        ),
                        FieldElementExpression::mul(
                            FieldElementExpression::identifier("z".into()),
                            FieldElementExpression::identifier("t".into()),
                        ),
                    ),
                    zir::RuntimeError::mock(),
                ),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![],
            },
        };

        let flat = flatten_function(function);

        let expected = FlatFunction {
            module_map: Default::default(),
            arguments: vec![],
            return_count: 0,
            statements: vec![
                FlatStatement::definition(
                    Variable::new(0),
                    FlatExpression::value(Bn128Field::from(4)),
                ),
                FlatStatement::definition(
                    Variable::new(1),
                    FlatExpression::value(Bn128Field::from(4)),
                ),
                FlatStatement::definition(
                    Variable::new(2),
                    FlatExpression::value(Bn128Field::from(8)),
                ),
                FlatStatement::definition(
                    Variable::new(3),
                    FlatExpression::value(Bn128Field::from(2)),
                ),
                FlatStatement::definition(
                    Variable::new(4),
                    FlatExpression::mul(
                        FlatExpression::identifier(Variable::new(2)),
                        FlatExpression::identifier(Variable::new(3)),
                    ),
                ),
                FlatStatement::condition(
                    FlatExpression::identifier(Variable::new(4)),
                    FlatExpression::mul(
                        FlatExpression::identifier(Variable::new(0)),
                        FlatExpression::identifier(Variable::new(1)),
                    ),
                    zir::RuntimeError::mock().into(),
                ),
            ],
        };

        assert_eq!(flat.collect(), expected);
    }

    #[test]
    fn powers_zero() {
        // def main() {
        //     field a = 7;
        //     field b = a**0;
        //     return b;
        // }

        // def main() {
        //     _0 = 7;
        //     _1 = 1;        // power flattening returns 1, definition introduces _7
        //     return _1;
        // }
        let function = ZirFunction {
            arguments: vec![],
            statements: vec![
                ZirStatement::definition(
                    zir::Variable::field_element("a"),
                    FieldElementExpression::value(Bn128Field::from(7)).into(),
                ),
                ZirStatement::definition(
                    zir::Variable::field_element("b"),
                    FieldElementExpression::pow(
                        FieldElementExpression::identifier("a".into()),
                        0u32.into(),
                    )
                    .into(),
                ),
                ZirStatement::ret(vec![FieldElementExpression::identifier("b".into()).into()]),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![Type::FieldElement],
            },
        };

        let expected = FlatFunction {
            module_map: Default::default(),
            arguments: vec![],
            return_count: 1,
            statements: vec![
                FlatStatement::definition(
                    Variable::new(0),
                    FlatExpression::value(Bn128Field::from(7)),
                ),
                FlatStatement::definition(
                    Variable::new(1),
                    FlatExpression::value(Bn128Field::from(1)),
                ),
                FlatStatement::definition(
                    Variable::public(0),
                    FlatExpression::identifier(Variable::new(1)),
                ),
            ],
        };

        let flattened = flatten_function(function);

        assert_eq!(flattened, expected);
    }

    #[test]
    fn power_one() {
        // def main() {
        //     field a = 7;
        //     field b = a**1;
        //     return b;
        // }

        // def main() {
        //     _0 = 7;
        //     _1 = 1 * _0;     // x**1
        //     _2 = _1;         // power flattening returns _1, definition introduces _2
        //     return _2;
        // }
        let function = ZirFunction {
            arguments: vec![],
            statements: vec![
                ZirStatement::definition(
                    zir::Variable::field_element("a"),
                    FieldElementExpression::value(Bn128Field::from(7)).into(),
                ),
                ZirStatement::definition(
                    zir::Variable::field_element("b"),
                    FieldElementExpression::pow(
                        FieldElementExpression::identifier("a".into()),
                        1u32.into(),
                    )
                    .into(),
                ),
                ZirStatement::ret(vec![FieldElementExpression::identifier("b".into()).into()]),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![Type::FieldElement],
            },
        };

        let expected = FlatFunction {
            module_map: Default::default(),
            arguments: vec![],
            return_count: 1,
            statements: vec![
                FlatStatement::definition(
                    Variable::new(0),
                    FlatExpression::value(Bn128Field::from(7)),
                ),
                FlatStatement::definition(
                    Variable::new(1),
                    FlatExpression::mul(
                        FlatExpression::value(Bn128Field::from(1)),
                        FlatExpression::identifier(Variable::new(0)),
                    ),
                ),
                FlatStatement::definition(
                    Variable::public(0),
                    FlatExpression::identifier(Variable::new(1)),
                ),
            ],
        };

        let flattened = flatten_function(function);

        assert_eq!(flattened, expected);
    }

    #[test]
    fn power_13() {
        // def main() {
        //     field a = 7;
        //     field b = a**13;
        //     return b;
        // }

        // we apply double and add
        // 13 == 0b1101
        // a ** 13 == a**(2**0 + 2**2 + 2**3) == a**1 * a**4 * a**8

        // a_0 = a * a      // a**2
        // a_1 = a_0 * a_0  // a**4
        // a_2 = a_1 * a_1  // a**8

        // a_3 = a * a_1    // a * a**4 == a**5
        // a_4 = a_3 * a_2  // a**5 * a**8 == a**13

        // def main() {
        //     _0 = 7;
        //     _1 = (_0 * _0);  // a**2
        //     _2 = (_1 * _1);  // a**4
        //     _3 = (_2 * _2);  // a**8
        //
        //     _4 = 1 * _0;     // a
        //     _5 = _4 * _2;    // a**5
        //     _6 = _5 * _3;    // a**13
        //     return _6;
        // }

        let function = ZirFunction {
            arguments: vec![],
            statements: vec![
                ZirStatement::definition(
                    zir::Variable::field_element("a"),
                    FieldElementExpression::value(Bn128Field::from(7)).into(),
                ),
                ZirStatement::definition(
                    zir::Variable::field_element("b"),
                    FieldElementExpression::pow(
                        FieldElementExpression::identifier("a".into()),
                        13u32.into(),
                    )
                    .into(),
                ),
                ZirStatement::ret(vec![FieldElementExpression::identifier("b".into()).into()]),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![Type::FieldElement],
            },
        };

        let expected = FlatFunction {
            module_map: Default::default(),
            arguments: vec![],
            return_count: 1,
            statements: vec![
                FlatStatement::definition(
                    Variable::new(0),
                    FlatExpression::value(Bn128Field::from(7)),
                ),
                FlatStatement::definition(
                    Variable::new(1),
                    FlatExpression::mul(
                        FlatExpression::identifier(Variable::new(0)),
                        FlatExpression::identifier(Variable::new(0)),
                    ),
                ),
                FlatStatement::definition(
                    Variable::new(2),
                    FlatExpression::mul(
                        FlatExpression::identifier(Variable::new(1)),
                        FlatExpression::identifier(Variable::new(1)),
                    ),
                ),
                FlatStatement::definition(
                    Variable::new(3),
                    FlatExpression::mul(
                        FlatExpression::identifier(Variable::new(2)),
                        FlatExpression::identifier(Variable::new(2)),
                    ),
                ),
                FlatStatement::definition(
                    Variable::new(4),
                    FlatExpression::mul(
                        FlatExpression::value(Bn128Field::from(1)),
                        FlatExpression::identifier(Variable::new(0)),
                    ),
                ),
                FlatStatement::definition(
                    Variable::new(5),
                    FlatExpression::mul(
                        FlatExpression::identifier(Variable::new(4)),
                        FlatExpression::identifier(Variable::new(2)),
                    ),
                ),
                FlatStatement::definition(
                    Variable::new(6),
                    FlatExpression::mul(
                        FlatExpression::identifier(Variable::new(5)),
                        FlatExpression::identifier(Variable::new(3)),
                    ),
                ),
                FlatStatement::definition(
                    Variable::public(0),
                    FlatExpression::identifier(Variable::new(6)),
                ),
            ],
        };

        let flattened = flatten_function(function);

        assert_eq!(flattened, expected);
    }

    #[test]
    fn if_else() {
        let config = CompileConfig::default();
        let expression = FieldElementExpression::conditional(
            BooleanExpression::field_eq(
                FieldElementExpression::value(Bn128Field::from(32)),
                FieldElementExpression::value(Bn128Field::from(4)),
            ),
            FieldElementExpression::value(Bn128Field::from(12)),
            FieldElementExpression::value(Bn128Field::from(51)),
        );

        let mut flattener = Flattener::new(config);

        flattener.flatten_field_expression(&mut FlatStatements::default(), expression);
    }

    #[test]
    fn geq_leq() {
        let config = CompileConfig::default();
        let mut flattener = Flattener::new(config);
        let expression_le = BooleanExpression::field_le(
            FieldElementExpression::value(Bn128Field::from(32)),
            FieldElementExpression::value(Bn128Field::from(4)),
        );
        flattener.flatten_boolean_expression(&mut FlatStatements::default(), expression_le);
    }

    #[test]
    fn bool_and() {
        let config = CompileConfig::default();
        let mut flattener = Flattener::new(config);

        let expression = FieldElementExpression::conditional(
            BooleanExpression::bitand(
                BooleanExpression::field_eq(
                    FieldElementExpression::value(Bn128Field::from(4)),
                    FieldElementExpression::value(Bn128Field::from(4)),
                ),
                BooleanExpression::field_lt(
                    FieldElementExpression::value(Bn128Field::from(4)),
                    FieldElementExpression::value(Bn128Field::from(20)),
                ),
            ),
            FieldElementExpression::value(Bn128Field::from(12)),
            FieldElementExpression::value(Bn128Field::from(51)),
        );

        flattener.flatten_field_expression(&mut FlatStatements::default(), expression);
    }

    #[test]
    fn div() {
        // a = 5 / b / b
        let config = CompileConfig::default();
        let mut flattener = Flattener::new(config);
        let mut statements_flattened = FlatStatements::default();

        let definition = ZirStatement::definition(
            zir::Variable::field_element("b"),
            FieldElementExpression::value(Bn128Field::from(42)).into(),
        );

        let statement = ZirStatement::definition(
            zir::Variable::field_element("a"),
            FieldElementExpression::div(
                FieldElementExpression::div(
                    FieldElementExpression::value(Bn128Field::from(5)),
                    FieldElementExpression::identifier("b".into()),
                ),
                FieldElementExpression::identifier("b".into()),
            )
            .into(),
        );

        flattener.flatten_statement(&mut statements_flattened, definition);

        flattener.flatten_statement(&mut statements_flattened, statement);

        // define b
        let b = Variable::new(0);
        // define new wires for members of Div
        let five = Variable::new(1);
        let b0 = Variable::new(2);
        // Define inverse
        let sym_0 = Variable::new(3);
        // Define result, which is first member to next Div
        let sym_1 = Variable::new(4);
        // Define second member
        let b1 = Variable::new(5);
        // Define inverse
        let sym_2 = Variable::new(6);

        assert_eq!(
            statements_flattened.buffer,
            vec![
                FlatStatement::definition(b, FlatExpression::value(Bn128Field::from(42))),
                // inputs to first div (5/b)
                FlatStatement::definition(five, FlatExpression::value(Bn128Field::from(5))),
                FlatStatement::definition(b0, b.into()),
                // execute div
                FlatStatement::Directive(FlatDirective::new(
                    vec![sym_0],
                    Solver::Div,
                    vec![five.into(), b0.into()]
                )),
                FlatStatement::condition(
                    five.into(),
                    FlatExpression::mul(b0.into(), sym_0.into()),
                    RuntimeError::Division
                ),
                // inputs to second div (res/b)
                FlatStatement::definition(sym_1, sym_0.into()),
                FlatStatement::definition(b1, b.into()),
                // execute div
                FlatStatement::Directive(FlatDirective::new(
                    vec![sym_2],
                    Solver::Div,
                    vec![sym_1.into(), b1.into()]
                )),
                FlatStatement::condition(
                    sym_1.into(),
                    FlatExpression::mul(b1.into(), sym_2.into()),
                    RuntimeError::Division
                ),
            ]
        );
    }
}
