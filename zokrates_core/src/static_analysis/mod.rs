//! Module containing static analysis
//!
//! @file mod.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

mod branch_isolator;
mod condition_redefiner;
mod constant_argument_checker;
mod constant_resolver;
mod dead_code;
mod flat_propagation;
mod flatten_complex_types;
mod log_ignorer;
mod out_of_bounds;
mod panic_extractor;
mod propagation;
mod reducer;
mod struct_concretizer;
mod uint_optimizer;
mod variable_write_remover;
mod zir_propagation;

use self::branch_isolator::Isolator;
use self::condition_redefiner::ConditionRedefiner;
use self::constant_argument_checker::ConstantArgumentChecker;
use self::flatten_complex_types::Flattener;
use self::log_ignorer::LogIgnorer;
use self::out_of_bounds::OutOfBoundsChecker;
use self::propagation::Propagator;
use self::reducer::reduce_program;
use self::struct_concretizer::StructConcretizer;
use self::uint_optimizer::UintOptimizer;
use self::variable_write_remover::VariableWriteRemover;
use crate::compile::CompileConfig;
use crate::static_analysis::constant_resolver::ConstantResolver;
use crate::static_analysis::dead_code::DeadCodeEliminator;
use crate::static_analysis::panic_extractor::PanicExtractor;
use crate::static_analysis::zir_propagation::ZirPropagator;
use std::fmt;
use zokrates_ast::typed::{abi::Abi, TypedProgram};
use zokrates_ast::zir::ZirProgram;
use zokrates_field::Field;

#[derive(Debug)]
pub enum Error {
    Reducer(self::reducer::Error),
    Propagation(self::propagation::Error),
    ZirPropagation(self::zir_propagation::Error),
    NonConstantArgument(self::constant_argument_checker::Error),
    OutOfBounds(self::out_of_bounds::Error),
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

impl From<zir_propagation::Error> for Error {
    fn from(e: zir_propagation::Error) -> Self {
        Error::ZirPropagation(e)
    }
}

impl From<out_of_bounds::Error> for Error {
    fn from(e: out_of_bounds::Error) -> Self {
        Error::OutOfBounds(e)
    }
}

impl From<constant_argument_checker::Error> for Error {
    fn from(e: constant_argument_checker::Error) -> Self {
        Error::NonConstantArgument(e)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Reducer(e) => write!(f, "{}", e),
            Error::Propagation(e) => write!(f, "{}", e),
            Error::ZirPropagation(e) => write!(f, "{}", e),
            Error::NonConstantArgument(e) => write!(f, "{}", e),
            Error::OutOfBounds(e) => write!(f, "{}", e),
        }
    }
}

pub fn analyse<'ast, T: Field>(
    p: TypedProgram<'ast, T>,
    config: &CompileConfig,
) -> Result<(ZirProgram<'ast, T>, Abi), Error> {
    // inline user-defined constants
    log::debug!("Static analyser: Inline constants");
    let r = ConstantResolver::inline(p);
    log::trace!("\n{}", r);

    // isolate branches
    let r = if config.isolate_branches {
        log::debug!("Static analyser: Isolate branches");
        let r = Isolator::isolate(r);
        log::trace!("\n{}", r);
        r
    } else {
        log::debug!("Static analyser: Branch isolation skipped");
        r
    };

    // include logs
    let r = if config.debug {
        log::debug!("Static analyser: Include logs");
        r
    } else {
        log::debug!("Static analyser: Ignore logs");
        let r = LogIgnorer::ignore(r);
        log::trace!("\n{}", r);
        r
    };

    // reduce the program to a single function
    log::debug!("Static analyser: Reduce program");
    let r = reduce_program(r).map_err(Error::from)?;
    log::trace!("\n{}", r);

    log::debug!("Static analyser: Propagate");
    let r = Propagator::propagate(r)?;
    log::trace!("\n{}", r);

    log::debug!("Static analyser: Concretize structs");
    let r = StructConcretizer::concretize(r);
    log::trace!("\n{}", r);

    // generate abi
    log::debug!("Static analyser: Generate abi");
    let abi = r.abi();

    // propagate
    log::debug!("Static analyser: Propagate");
    let r = Propagator::propagate(r).map_err(Error::from)?;
    log::trace!("\n{}", r);

    // remove assignment to variable index
    log::debug!("Static analyser: Remove variable index");
    let r = VariableWriteRemover::apply(r);
    log::trace!("\n{}", r);

    // detect non constant shifts and constant lt bounds
    log::debug!("Static analyser: Detect non constant arguments");
    let r = ConstantArgumentChecker::check(r).map_err(Error::from)?;
    log::trace!("\n{}", r);

    // detect out of bounds reads and writes
    log::debug!("Static analyser: Detect out of bound accesses");
    let r = OutOfBoundsChecker::check(r).map_err(Error::from)?;
    log::trace!("\n{}", r);

    // redefine conditions
    log::debug!("Static analyser: Redefine conditions");
    let r = ConditionRedefiner::redefine(r);
    log::trace!("\n{}", r);

    // convert to zir, removing complex types
    log::debug!("Static analyser: Convert to zir");
    let zir = Flattener::flatten(r);
    log::trace!("\n{}", zir);

    // apply propagation in zir
    log::debug!("Static analyser: Apply propagation in zir");
    let zir = ZirPropagator::propagate(zir).map_err(Error::from)?;
    log::trace!("\n{}", zir);

    log::debug!("Static analyser: Extract panics");
    let zir = PanicExtractor::extract(zir);
    log::trace!("\n{}", zir);

    log::debug!("Static analyser: Remove dead code");
    let zir = DeadCodeEliminator::eliminate(zir);
    log::trace!("\n{}", zir);

    // optimize uint expressions
    log::debug!("Static analyser: Optimize uints");
    let zir = UintOptimizer::optimize(zir);
    log::trace!("\n{}", zir);

    Ok((zir, abi))
}
