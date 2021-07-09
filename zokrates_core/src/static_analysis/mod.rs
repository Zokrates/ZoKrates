//! Module containing static analysis
//!
//! @file mod.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

mod bounds_checker;
mod branch_isolator;
mod constant_inliner;
mod flat_propagation;
mod flatten_complex_types;
mod propagation;
mod reducer;
mod shift_checker;
mod uint_optimizer;
mod unconstrained_vars;
mod variable_read_remover;
mod variable_write_remover;

use self::bounds_checker::BoundsChecker;
use self::branch_isolator::Isolator;
use self::flatten_complex_types::Flattener;
use self::propagation::Propagator;
use self::reducer::reduce_program;
use self::shift_checker::ShiftChecker;
use self::uint_optimizer::UintOptimizer;
use self::unconstrained_vars::UnconstrainedVariableDetector;
use self::variable_read_remover::VariableReadRemover;
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
    OutOfBounds(self::bounds_checker::Error),
    Propagation(self::propagation::Error),
}

impl From<self::reducer::Error> for Error {
    fn from(e: self::reducer::Error) -> Self {
        Error::Reducer(e)
    }
}

impl From<self::bounds_checker::Error> for Error {
    fn from(e: bounds_checker::Error) -> Self {
        Error::OutOfBounds(e)
    }
}

impl From<self::propagation::Error> for Error {
    fn from(e: propagation::Error) -> Self {
        Error::Propagation(e)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Reducer(e) => write!(f, "{}", e),
            Error::OutOfBounds(e) => write!(f, "{}", e),
            Error::Propagation(e) => write!(f, "{}", e),
        }
    }
}

impl<'ast, T: Field> TypedProgram<'ast, T> {
    pub fn analyse(self, config: &CompileConfig) -> Result<(ZirProgram<'ast, T>, Abi), Error> {
        println!("{}", self);

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

        println!("{}", r);

        // generate abi
        let abi = r.abi();

        // propagate
        let r = Propagator::propagate(r).map_err(Error::from)?;
        // remove assignment to variable index
        let r = VariableWriteRemover::apply(r);
        // remove variable access to complex types
        let r = VariableReadRemover::apply(r);
        // check array accesses are in bounds
        let r = BoundsChecker::check(r).map_err(Error::from)?;
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
