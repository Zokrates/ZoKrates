//! Module containing static analysis
//!
//! @file mod.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

mod branch_isolator;
mod constant_argument_checker;
mod constant_resolver;
mod flat_propagation;
mod flatten_complex_types;
mod out_of_bounds;
mod propagation;
mod reducer;
mod uint_optimizer;
mod variable_write_remover;
mod zir_propagation;

use self::branch_isolator::Isolator;
use self::constant_argument_checker::ConstantArgumentChecker;
use self::flatten_complex_types::{Flattener, FlattenerInner};
use self::out_of_bounds::OutOfBoundsChecker;
use self::propagation::Propagator;
use self::reducer::reduce_program;
use self::uint_optimizer::UintOptimizer;
use self::variable_write_remover::VariableWriteRemover;
use crate::compile::CompileConfig;
use crate::static_analysis::constant_resolver::ConstantResolver;
use crate::static_analysis::zir_propagation::ZirPropagator;
use crate::typed_absy;
use crate::typed_absy::{abi::Abi, Folder, ResultFolder, TypedProgram};
use crate::zir;
use crate::zir::folder::Folder as ZirFolder;
use crate::zir::result_folder::ResultFolder as ZirResultFolder;
use crate::zir::ZirFunctionIterator;
use crate::zir::{IntoZirStatements, ZirProgramIterator};
use std::fmt;
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

impl<'ast, T: Field> TypedProgram<'ast, T> {
    pub fn analyse(
        self,
        config: &CompileConfig,
    ) -> Result<
        (
            ZirProgramIterator<'ast, impl IntoZirStatements<'ast, Field = T>>,
            Abi,
        ),
        Error,
    > {
        // inline user-defined constants
        log::debug!("Static analyser: Inline constants");
        let r = ConstantResolver::inline(self);
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

        use fallible_iterator::IntoFallibleIterator;

        log::debug!("Start streaming");

        // reduce the program to a single function
        log::debug!("Static analyser: Reduce program");
        let r = reduce_program(r).map_err(Error::from)?;
        //log::trace!("\n{}", r);

        let r = r.collect().unwrap();

        log::trace!("\n{}", r);

        panic!();

        // generate abi
        log::debug!("Static analyser: Generate abi");
        let abi: Abi = r.abi();

        // // propagate
        // log::debug!("Static analyser: Propagate");
        // let r = Propagator::propagate(r).map_err(Error::from)?;
        // log::trace!("\n{}", r);

        // // remove assignment to variable index
        // log::debug!("Static analyser: Remove variable index");
        // let r = VariableWriteRemover::apply(r);
        // log::trace!("\n{}", r);

        // // detect non constant shifts and constant lt bounds
        // log::debug!("Static analyser: Detect non constant arguments");
        // let r = ConstantArgumentChecker::check(r).map_err(Error::from)?;
        // log::trace!("\n{}", r);

        // // detect out of bounds reads and writes
        // log::debug!("Static analyser: Detect out of bound accesses");
        // let r = OutOfBoundsChecker::check(r).map_err(Error::from)?;
        // log::trace!("\n{}", r);

        // convert to zir, removing complex types
        log::debug!("Static analyser: Convert to zir");
        log::debug!("Static analyser: Optimize uints");

        //let mut constants = crate::static_analysis::propagation::Constants::new();
        //let mut propagator = Propagator::with_constants(&mut constants);
        let mut variable_write_remover = VariableWriteRemover::default();
        let mut constant_argument_checker = ConstantArgumentChecker::default();
        let mut out_of_bounds_checker = OutOfBoundsChecker::default();
        let mut type_flattener_inner = FlattenerInner::default();
        let mut zir_propagator = ZirPropagator::default();
        let mut uint_optimizer = UintOptimizer::default();

        let arguments = r.arguments;
        let statements = r.statements.into_fallible_iter();
        let signature = type_flattener_inner.fold_signature(r.signature);
        // todo: initialise with parameters
        let arguments: Vec<_> = arguments
            .into_iter()
            //.map(|a| propagator.fold_parameter(a).unwrap())
            .map(|a| variable_write_remover.fold_parameter(a))
            .map(|a| constant_argument_checker.fold_parameter(a).unwrap())
            .map(|a| out_of_bounds_checker.fold_parameter(a).unwrap())
            .flat_map(|a| type_flattener_inner.fold_declaration_parameter(a))
            .map(|a| zir_propagator.fold_parameter(a).unwrap())
            .map(|a| uint_optimizer.fold_parameter(a))
            .collect();

        //let statements = typed_absy::result_folder::fold_statements(propagator, statements);
        let statements = typed_absy::folder::fold_statements(variable_write_remover, statements);
        let statements =
            typed_absy::result_folder::fold_statements(constant_argument_checker, statements);
        let statements =
            typed_absy::result_folder::fold_statements(out_of_bounds_checker, statements);

        let type_flattener = Flattener {
            input: statements.into_fallible_iter(),
            output: std::collections::VecDeque::default(),
            flattener: type_flattener_inner,
        };

        let statements = type_flattener;

        let statements = zir::result_folder::fold_statements(zir_propagator, statements);
        let statements = zir::folder::fold_statements(uint_optimizer, statements);

        let zir = ZirFunctionIterator {
            statements,
            arguments,
            signature,
        };

        Ok((zir, abi))
    }
}
