use serde::{Deserialize, Serialize};
use std::borrow::Borrow;
use std::collections::HashMap;
use std::fmt;
use zokrates_abi::{Decode, Value};
use zokrates_ast::ir::{
    LinComb, Parameter, QuadComb, RuntimeError, Solver, Statement, Variable, Witness,
};
use zokrates_ast::zir::{self, Expr};
use zokrates_field::Field;

pub type ExecutionResult<T> = Result<Witness<T>, Error>;

#[derive(Default)]
pub struct Interpreter {
    /// Whether we should try to give out-of-range bit decompositions when the input is not a single summand.
    /// Used to do targeted testing of `<` flattening, making sure the bit decomposition we base the result on is unique.
    should_try_out_of_range: bool,
}

impl Interpreter {
    pub fn try_out_of_range() -> Interpreter {
        Interpreter {
            should_try_out_of_range: true,
        }
    }
}

impl Interpreter {
    pub fn execute<'ast, T: Field, S: Borrow<Statement<'ast, T>>>(
        &self,
        inputs: &[T],
        statements: impl Iterator<Item = S>,
        arguments: &[Parameter],
        solvers: &[Solver<'ast, T>],
    ) -> ExecutionResult<T> {
        self.execute_with_log_stream(inputs, statements, arguments, solvers, &mut std::io::sink())
    }

    pub fn execute_with_log_stream<
        'ast,
        'a,
        W: std::io::Write,
        T: Field,
        S: Borrow<Statement<'ast, T>>,
    >(
        &self,
        inputs: &[T],
        statements: impl Iterator<Item = S>,
        arguments: &[Parameter],
        solvers: &[Solver<'ast, T>],
        log_stream: &mut W,
    ) -> ExecutionResult<T> {
        if arguments.len() != inputs.len() {
            return Err(Error::WrongInputCount {
                expected: arguments.len(),
                received: inputs.len(),
            });
        };

        let mut witness = Witness::default();
        witness.insert(Variable::one(), T::one());

        for (arg, value) in arguments.iter().zip(inputs.iter()) {
            witness.insert(arg.id, *value);
        }

        for statement in statements {
            match statement.borrow() {
                Statement::Block(..) => unreachable!(),
                Statement::Constraint(s) => match s.lin.is_assignee(&witness) {
                    true => {
                        let val = evaluate_quad(&witness, &s.quad).unwrap();
                        witness.insert(s.lin.value.get(0).unwrap().0, val);
                    }
                    false => {
                        let lhs_value = evaluate_quad(&witness, &s.quad).unwrap();
                        let rhs_value = evaluate_lin(&witness, &s.lin).unwrap();
                        if lhs_value != rhs_value {
                            return Err(Error::UnsatisfiedConstraint {
                                error: s.error.clone(),
                            });
                        }
                    }
                },
                Statement::Directive(ref d) => {
                    let mut inputs: Vec<_> = d
                        .inputs
                        .iter()
                        .map(|i| evaluate_quad(&witness, i).unwrap())
                        .collect();

                    let res = match (&d.solver, self.should_try_out_of_range) {
                        (Solver::Bits(bitwidth), true) if *bitwidth >= T::get_required_bits() => {
                            Ok(Self::try_solve_with_out_of_range_bits(
                                *bitwidth,
                                inputs.pop().unwrap(),
                            ))
                        }
                        _ => Self::execute_solver(&d.solver, &inputs, solvers),
                    }
                    .map_err(Error::Solver)?;

                    for (i, o) in d.outputs.iter().enumerate() {
                        witness.insert(*o, res[i]);
                    }
                }
                Statement::Log(s) => {
                    let mut parts = s.format_string.parts.iter();

                    write!(log_stream, "{}", parts.next().unwrap())
                        .map_err(|_| Error::LogStream)?;

                    for ((t, e), part) in s.expressions.iter().zip(parts) {
                        let values: Vec<_> = e
                            .iter()
                            .map(|e| evaluate_lin(&witness, e).unwrap())
                            .collect();

                        write!(
                            log_stream,
                            "{}",
                            Value::decode(values, t.clone()).into_serde_json()
                        )
                        .map_err(|_| Error::LogStream)?;

                        write!(log_stream, "{}", part).map_err(|_| Error::LogStream)?;
                    }

                    writeln!(log_stream).map_err(|_| Error::LogStream)?;

                    log_stream.flush().map_err(|_| Error::LogStream)?;
                }
            }
        }

        Ok(witness)
    }

    fn try_solve_with_out_of_range_bits<T: Field>(bit_width: usize, input: T) -> Vec<T> {
        use num::traits::Pow;
        use num_bigint::BigUint;

        let candidate = input.to_biguint() + T::max_value().to_biguint() + T::from(1).to_biguint();

        let input = if candidate < T::from(2).to_biguint().pow(T::get_required_bits()) {
            candidate
        } else {
            input.to_biguint()
        };

        let padding = bit_width - T::get_required_bits();

        (0..padding)
            .map(|_| T::zero())
            .chain((0..T::get_required_bits()).rev().scan(input, |state, i| {
                if BigUint::from(2usize).pow(i) <= *state {
                    *state = (*state).clone() - BigUint::from(2usize).pow(i);
                    Some(T::one())
                } else {
                    Some(T::zero())
                }
            }))
            .collect()
    }

    pub fn execute_solver<'ast, T: Field>(
        solver: &Solver<'ast, T>,
        inputs: &[T],
        solvers: &[Solver<'ast, T>],
    ) -> Result<Vec<T>, String> {
        let solver = match solver {
            Solver::Ref(call) => solvers
                .get(call.index)
                .ok_or_else(|| format!("Could not get solver at index {}", call.index))?,
            s => s,
        };

        let (expected_input_count, expected_output_count) = solver.get_signature();
        assert_eq!(inputs.len(), expected_input_count);

        let res = match solver {
            Solver::Zir(func) => {
                use zokrates_ast::zir::result_folder::ResultFolder;
                assert_eq!(func.arguments.len(), inputs.len());

                let constants = func
                    .arguments
                    .iter()
                    .zip(inputs)
                    .map(|(a, v)| match &a.id.ty {
                        zir::Type::FieldElement => Ok((
                            a.id.id.clone(),
                            zokrates_ast::zir::FieldElementExpression::value(*v).into(),
                        )),
                        zir::Type::Boolean => match v {
                            v if *v == T::from(0) => Ok((
                                a.id.id.clone(),
                                zokrates_ast::zir::BooleanExpression::value(false).into(),
                            )),
                            v if *v == T::from(1) => Ok((
                                a.id.id.clone(),
                                zokrates_ast::zir::BooleanExpression::value(true).into(),
                            )),
                            v => Err(format!("`{}` has unexpected value `{}`", a.id, v)),
                        },
                        zir::Type::Uint(bitwidth) => match v.bits() <= bitwidth.to_usize() as u32 {
                            true => Ok((
                                a.id.id.clone(),
                                zokrates_ast::zir::UExpression::value(
                                    v.to_dec_string().parse::<u128>().unwrap(),
                                )
                                .annotate(*bitwidth)
                                .into(),
                            )),
                            false => Err(format!(
                                "`{}` has unexpected bitwidth (got {} but expected {})",
                                a.id,
                                v.bits(),
                                bitwidth
                            )),
                        },
                    })
                    .collect::<Result<HashMap<_, _>, _>>()?;

                let mut propagator = zokrates_analysis::ZirPropagator::with_constants(constants);

                let folded_function = propagator
                    .fold_function(func.clone())
                    .map_err(|e| e.to_string())?;

                assert_eq!(folded_function.statements.len(), 1);
                if let zokrates_ast::zir::ZirStatement::Return(v) =
                    folded_function.statements[0].clone()
                {
                    v.inner
                        .into_iter()
                        .map(|v| match v {
                            zokrates_ast::zir::ZirExpression::FieldElement(
                                zokrates_ast::zir::FieldElementExpression::Value(n),
                            ) => n.value,
                            _ => unreachable!(),
                        })
                        .collect()
                } else {
                    unreachable!()
                }
            }
            Solver::ConditionEq => match inputs[0].is_zero() {
                true => vec![T::zero(), T::one()],
                false => vec![
                    T::one(),
                    T::one().checked_div(&inputs[0]).unwrap_or_else(T::one),
                ],
            },
            Solver::Bits(bit_width) => {
                // get all the bits
                let bits = inputs[0].to_bits_be();

                // only keep at most `bit_width` of them, starting from the least significant
                let bits = bits[bits.len().saturating_sub(*bit_width)..].to_vec();

                // pad with zeroes so that the result is exactly `bit_width` long
                (0..bit_width - bits.len())
                    .map(|_| false)
                    .chain(bits)
                    .map(T::from)
                    .collect()
            }
            Solver::Xor => {
                let x = inputs[0];
                let y = inputs[1];

                vec![x + y - T::from(2) * x * y]
            }
            Solver::Or => {
                let x = inputs[0];
                let y = inputs[1];

                vec![x + y - x * y]
            }
            // res = b * c - (2b * c - b - c) * (a)
            Solver::ShaAndXorAndXorAnd => {
                let a = inputs[0];
                let b = inputs[1];
                let c = inputs[2];
                vec![b * c - (T::from(2) * b * c - b - c) * a]
            }
            // res = a(b - c) + c
            Solver::ShaCh => {
                let a = inputs[0];
                let b = inputs[1];
                let c = inputs[2];
                vec![a * (b - c) + c]
            }

            Solver::Div => vec![inputs[0].checked_div(&inputs[1]).unwrap_or_else(T::one)],
            Solver::EuclideanDiv => {
                use num::CheckedDiv;

                let n = inputs[0].to_biguint();
                let d = inputs[1].to_biguint();

                let q = n.checked_div(&d).unwrap_or_else(|| 0u32.into());
                let r = n - d * &q;
                vec![T::try_from(q).unwrap(), T::try_from(r).unwrap()]
            }
            #[cfg(feature = "bellman")]
            Solver::Sha256Round => {
                use pairing_ce::bn256::Bn256;
                use zokrates_embed::bellman::generate_sha256_round_witness;
                use zokrates_field::Bn128Field;
                assert_eq!(T::id(), Bn128Field::id());
                let i = &inputs[0..512];
                let h = &inputs[512..];
                let to_fr = |x: &T| {
                    use pairing_ce::ff::{PrimeField, ScalarEngine};
                    let s = x.to_dec_string();
                    <Bn256 as ScalarEngine>::Fr::from_str(&s).unwrap()
                };
                let i: Vec<_> = i.iter().map(to_fr).collect();
                let h: Vec<_> = h.iter().map(to_fr).collect();
                assert_eq!(h.len(), 256);
                generate_sha256_round_witness::<Bn256>(&i, &h)
                    .into_iter()
                    .map(|x| {
                        use pairing_ce::ff::{PrimeField, PrimeFieldRepr};
                        let mut res: Vec<u8> = vec![];
                        x.into_repr().write_le(&mut res).unwrap();
                        T::from_byte_vector(res)
                    })
                    .collect()
            }
            #[cfg(feature = "ark")]
            Solver::SnarkVerifyBls12377(n) => {
                use zokrates_embed::ark::generate_verify_witness;
                use zokrates_field::Bw6_761Field;
                assert_eq!(T::id(), Bw6_761Field::id());

                generate_verify_witness(
                    &inputs[..*n],
                    &inputs[*n..*n + 8usize],
                    &inputs[*n + 8usize..],
                )
            }
            _ => unreachable!("unexpected solver"),
        };

        assert_eq!(res.len(), expected_output_count);

        Ok(res)
    }
}

#[derive(Debug)]
pub struct EvaluationError;

#[derive(PartialEq, Eq, Clone, Serialize, Deserialize)]
pub enum Error {
    UnsatisfiedConstraint { error: Option<RuntimeError> },
    Solver(String),
    WrongInputCount { expected: usize, received: usize },
    LogStream,
}

fn evaluate_lin<T: Field>(w: &Witness<T>, l: &LinComb<T>) -> Result<T, EvaluationError> {
    l.value.iter().try_fold(T::from(0), |acc, (var, mult)| {
        w.0.get(var)
            .map(|v| acc + (*v * mult))
            .ok_or(EvaluationError) // fail if any term isn't found
    })
}

pub fn evaluate_quad<T: Field>(w: &Witness<T>, q: &QuadComb<T>) -> Result<T, EvaluationError> {
    let left = evaluate_lin(w, &q.left)?;
    let right = evaluate_lin(w, &q.right)?;
    Ok(left * right)
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::UnsatisfiedConstraint { ref error } => {
                write!(
                    f,
                    "{}",
                    error
                        .as_ref()
                        .map(|m| m.to_string())
                        .expect("Found an unsatisfied constraint without an attached error.")
                )?;

                match error {
                    Some(e) if e.is_malicious() => {
                        writeln!(f)?;
                        write!(f, "The default ZoKrates interpreter should not yield this error. Please open an issue.")
                    }
                    _ => write!(f, ""),
                }
            }
            Error::Solver(ref e) => write!(f, "Solver error: {}", e),
            Error::WrongInputCount { expected, received } => write!(
                f,
                "Program takes {} input{} but was passed {} value{}",
                expected,
                if expected == 1 { "" } else { "s" },
                received,
                if received == 1 { "" } else { "s" }
            ),
            Error::LogStream => write!(f, "Error writing a log to the log stream"),
        }
    }
}

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::Bn128Field;

    mod eq_condition {

        // Wanted: (Y = (X != 0) ? 1 : 0)
        // # Y = if X == 0 then 0 else 1 fi
        // # M = if X == 0 then 1 else 1/X fi

        use super::*;

        #[test]
        fn execute() {
            let cond_eq = Solver::ConditionEq;
            let inputs = [0];
            let r = Interpreter::execute_solver(
                &cond_eq,
                &inputs
                    .iter()
                    .map(|&i| Bn128Field::from(i))
                    .collect::<Vec<_>>(),
                &[],
            )
            .unwrap();
            let res: Vec<Bn128Field> = [0, 1].iter().map(|&i| Bn128Field::from(i)).collect();
            assert_eq!(r, &res[..]);
        }

        #[test]
        fn execute_non_eq() {
            let cond_eq = Solver::ConditionEq;
            let inputs = [1];
            let r = Interpreter::execute_solver(
                &cond_eq,
                &inputs
                    .iter()
                    .map(|&i| Bn128Field::from(i))
                    .collect::<Vec<_>>(),
                &[],
            )
            .unwrap();
            let res: Vec<Bn128Field> = [1, 1].iter().map(|&i| Bn128Field::from(i)).collect();
            assert_eq!(r, &res[..]);
        }
    }

    #[test]
    fn bits_of_one() {
        let inputs = vec![Bn128Field::from(1)];
        let res = Interpreter::execute_solver(
            &Solver::Bits(Bn128Field::get_required_bits()),
            &inputs,
            &[],
        )
        .unwrap();
        assert_eq!(res[253], Bn128Field::from(1));
        for r in &res[0..253] {
            assert_eq!(*r, Bn128Field::from(0));
        }
    }

    #[test]
    fn bits_of_42() {
        let inputs = vec![Bn128Field::from(42)];
        let res = Interpreter::execute_solver(
            &Solver::Bits(Bn128Field::get_required_bits()),
            &inputs,
            &[],
        )
        .unwrap();
        assert_eq!(res[253], Bn128Field::from(0));
        assert_eq!(res[252], Bn128Field::from(1));
        assert_eq!(res[251], Bn128Field::from(0));
        assert_eq!(res[250], Bn128Field::from(1));
        assert_eq!(res[249], Bn128Field::from(0));
        assert_eq!(res[248], Bn128Field::from(1));
        assert_eq!(res[247], Bn128Field::from(0));
    }

    #[test]
    fn five_hundred_bits_of_1() {
        let inputs = vec![Bn128Field::from(1)];
        let res = Interpreter::execute_solver(&Solver::Bits(500), &inputs, &[]).unwrap();

        let mut expected = vec![Bn128Field::from(0); 500];
        expected[499] = Bn128Field::from(1);

        assert_eq!(res, expected);
    }

    #[test]
    fn solver_ref() {
        use std::ops::Mul;
        use zir::{
            types::{Signature, Type},
            FieldElementExpression, Identifier, IdentifierExpression, Parameter, Variable,
            ZirFunction, ZirStatement,
        };
        use zokrates_ast::common::RefCall;

        let id = IdentifierExpression::new(Identifier::internal(0usize));

        // (field i0) -> i0 * i0
        let solver = Solver::Zir(ZirFunction {
            arguments: vec![Parameter::new(Variable::field_element(id.id.clone()), true)],
            statements: vec![ZirStatement::ret(vec![FieldElementExpression::mul(
                FieldElementExpression::Identifier(id.clone()),
                FieldElementExpression::Identifier(id.clone()),
            )
            .into()])],
            signature: Signature::new()
                .inputs(vec![Type::FieldElement])
                .outputs(vec![Type::FieldElement]),
        });

        let signature = solver.get_signature();
        let solvers = vec![solver];

        let inputs = vec![Bn128Field::from(2)];
        let res = Interpreter::execute_solver(
            &Solver::Ref(RefCall {
                index: 0,
                signature,
            }),
            &inputs,
            &solvers,
        )
        .unwrap();

        let expected = vec![Bn128Field::from(4)];
        assert_eq!(res, expected);
    }
}
