//! Module containing static analysis
//!
//! @file mod.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

mod constrain_inputs;
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
mod variable_access_remover;

use self::constrain_inputs::InputConstrainer;
use self::flatten_complex_types::Flattener;
use self::inline::Inliner;
use self::propagate_unroll::PropagatedUnroller;
use self::propagation::Propagator;
use self::redefinition::RedefinitionOptimizer;
use self::return_binder::ReturnBinder;
use self::uint_optimizer::UintOptimizer;
use self::unconstrained_vars::UnconstrainedVariableDetector;
use self::variable_access_remover::VariableAccessRemover;
use crate::flat_absy::FlatProg;
use crate::ir::Prog;
use crate::typed_absy::TypedProgram;
use zir::ZirProgram;
use zokrates_field::field::Field;

pub trait Analyse {
    fn analyse(self) -> Self;
}

impl<'ast, T: Field> TypedProgram<'ast, T> {
    pub fn analyse(self) -> ZirProgram<'ast, T> {
        // propagated unrolling
        let r = PropagatedUnroller::unroll(self).unwrap_or_else(|e| panic!(e));
        // return binding
        let r = ReturnBinder::bind(r);

        // inline
        let r = Inliner::inline(r);

        // propagate
        let r = Propagator::propagate(r);

        let r = RedefinitionOptimizer::optimize(r);

        let r = VariableAccessRemover::apply(r);

        let zir = Flattener::flatten(r.clone());
        // constrain inputs
        let zir = InputConstrainer::constrain(zir);

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
