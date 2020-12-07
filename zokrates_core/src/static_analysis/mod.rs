//! Module containing static analysis
//!
//! @file mod.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

mod flat_propagation;
mod flatten_complex_types;
mod inline;
mod propagate_unroll;
mod propagation;
mod redefinition;
mod return_binder;
mod uint_optimizer;
mod unconstrained_vars;
mod unroll;
mod variable_read_remover;
mod variable_write_remover;

use self::flatten_complex_types::Flattener;
use self::inline::Inliner;
use self::propagate_unroll::PropagatedUnroller;
use self::propagation::Propagator;
use self::redefinition::RedefinitionOptimizer;
use self::return_binder::ReturnBinder;
use self::uint_optimizer::UintOptimizer;
use self::unconstrained_vars::UnconstrainedVariableDetector;
use self::variable_read_remover::VariableReadRemover;
use self::variable_write_remover::VariableWriteRemover;
use crate::flat_absy::FlatProg;
use crate::ir::Prog;
use crate::typed_absy::TypedProgram;
use zir::ZirProgram;
use zokrates_field::Field;

pub trait Analyse {
    fn analyse(self) -> Self;
}

impl<'ast, T: Field> TypedProgram<'ast, T> {
    pub fn analyse(self) -> ZirProgram<'ast, T> {
        // propagated unrolling
        println!("propagate unroll");
        let r = PropagatedUnroller::unroll(self).unwrap_or_else(|e| panic!(e));
        println!("bind");
        // return binding
        let r = ReturnBinder::bind(r);
        println!("inline");
        // inline
        let r = Inliner::inline(r);
        println!("propagate");
        // propagate
        let r = Propagator::propagate(r);
        println!("redef");
        // optimize redefinitions
        let r = RedefinitionOptimizer::optimize(r);
        println!("variable access");
        // remove variable access to complex types
        let r = VariableReadRemover::apply(r);
        println!("{}", r);
        println!("variable index");
        // remove assignment to variable index
        let r = VariableWriteRemover::apply(r);
        println!("{}", r);
        println!("flatten complex types");
        // convert to zir, removing complex types
        let zir = Flattener::flatten(r);
        println!("uint opt");
        // optimize uint expressions
        let zir = UintOptimizer::optimize(zir);

        zir
    }
}

impl<T: Field> Analyse for FlatProg<T> {
    fn analyse(self) -> Self {
        self.propagate()
    }
}

impl<T: Field> Analyse for Prog<T> {
    fn analyse(self) -> Self {
        let r = UnconstrainedVariableDetector::detect(self);
        r
    }
}
