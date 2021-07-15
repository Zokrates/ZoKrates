//! Module containing static analysis
//!
//! @file mod.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

mod branch_isolator;
mod constant_inliner;
mod flat_propagation;
mod flatten_complex_types;
mod propagation;
mod reducer;
mod shift_checker;
mod uint_optimizer;
mod unconstrained_vars;
mod variable_write_remover;

use self::branch_isolator::Isolator;
use self::flatten_complex_types::Flattener;
use self::propagation::Propagator;
use self::reducer::reduce_program;
use self::shift_checker::ShiftChecker;
use self::uint_optimizer::UintOptimizer;
use self::unconstrained_vars::UnconstrainedVariableDetector;
use self::variable_write_remover::VariableWriteRemover;
use crate::compile::CompileConfig;
use crate::flat_absy::FlatProg;
use crate::ir::Prog;
use crate::static_analysis::constant_inliner::ConstantInliner;
use crate::typed_absy::{abi::Abi, TypedProgram};
use crate::zir::ZirProgram;
use std::fmt;
use zokrates_field::Field;

pub trait Analyse {
    fn analyse(self) -> Self;
}
#[derive(Debug)]
pub enum Error {
    Reducer(self::reducer::Error),
    Propagation(self::propagation::Error),
    NonConstantShift(self::shift_checker::Error),
}

impl From<reducer::Error> for Error {
    fn from(e: self::reducer::Error) -> Self {
        Error::Reducer(e)
    }
}

impl From<propagation::Error> for Error {
    fn from(e: propagation::Error) -> Self {
        Error::Propagation(e)
    }
}

impl From<shift_checker::Error> for Error {
    fn from(e: shift_checker::Error) -> Self {
        Error::NonConstantShift(e)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Reducer(e) => write!(f, "{}", e),
            Error::Propagation(e) => write!(f, "{}", e),
            Error::NonConstantShift(e) => write!(f, "{}", e),
        }
    }
}

impl<'ast, T: Field> TypedProgram<'ast, T> {
    pub fn analyse(self, config: &CompileConfig) -> Result<(ZirProgram<'ast, T>, Abi), Error> {
        // inline user-defined constants
        let r = ConstantInliner::inline(self);
        // isolate branches
        let r = if config.isolate_branches {
            Isolator::isolate(r)
        } else {
            r
        };

        // reduce the program to a single function
        let r = reduce_program(r).map_err(Error::from)?;

        // generate abi
        let abi = r.abi();

        // propagate
        let r = Propagator::propagate(r).map_err(Error::from)?;

        // remove assignment to variable index
        let r = VariableWriteRemover::apply(r);
        // detect non constant shifts
        let r = ShiftChecker::check(r).map_err(Error::from)?;
        // convert to zir, removing complex types
        let zir = Flattener::flatten(r);
        // optimize uint expressions
        let zir = UintOptimizer::optimize(zir);

        Ok((zir, abi))
    }
}

impl<T: Field> Analyse for FlatProg<T> {
    fn analyse(self) -> Self {
        self.propagate()
    }
}

impl<T: Field> Analyse for Prog<T> {
    fn analyse(self) -> Self {
        UnconstrainedVariableDetector::detect(self)
    }
}
