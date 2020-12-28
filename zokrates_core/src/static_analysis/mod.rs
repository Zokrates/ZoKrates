//! Module containing static analysis
//!
//! @file mod.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

mod flat_propagation;
mod flatten_complex_types;
mod propagation;
mod redefinition;
mod reducer;
mod uint_optimizer;
mod unconstrained_vars;
mod variable_read_remover;
mod variable_write_remover;

use self::flatten_complex_types::Flattener;
use self::propagation::Propagator;
use self::redefinition::RedefinitionOptimizer;
use self::reducer::reduce_program;
use self::uint_optimizer::UintOptimizer;
use self::unconstrained_vars::UnconstrainedVariableDetector;
use self::variable_read_remover::VariableReadRemover;
use self::variable_write_remover::VariableWriteRemover;
use crate::flat_absy::FlatProg;
use crate::ir::Prog;
use crate::typed_absy::{abi::Abi, TypedProgram};
use crate::zir::ZirProgram;
use zokrates_field::Field;

pub trait Analyse {
    fn analyse(self) -> Self;
}

pub use self::reducer::Error;

impl<'ast, T: Field> TypedProgram<'ast, T> {
    pub fn analyse(self) -> Result<(ZirProgram<'ast, T>, Abi), Error> {
        let r = reduce_program(self)?;

        let abi = r.abi();

        // propagate
        let r = Propagator::propagate(r);

        // optimize redefinitions
        let r = RedefinitionOptimizer::optimize(r);

        // remove assignment to variable index
        let r = VariableWriteRemover::apply(r);

        // remove variable access to complex types
        let r = VariableReadRemover::apply(r);

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
