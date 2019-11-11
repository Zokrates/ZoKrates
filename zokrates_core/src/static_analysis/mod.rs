//! Module containing static analysis
//!
//! @file mod.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

mod constrain_inputs;
mod flat_propagation;
mod inline;
mod propagation;
mod unroll;
mod uint_optimizer;

use self::constrain_inputs::InputConstrainer;
use self::inline::Inliner;
use self::propagation::Propagator;
use self::unroll::Unroller;
use self::uint_optimizer::UintOptimizer;
use crate::flat_absy::FlatProg;
use crate::typed_absy::TypedProgram;
use zokrates_field::field::Field;

pub trait Analyse {
    fn analyse(self) -> Self;
}

impl<'ast, T: Field> Analyse for TypedProgram<'ast, T> {
    fn analyse(self) -> Self {
        // unroll
        let r = Unroller::unroll(self);
        // inline
        let r = Inliner::inline(r);
        // propagate
        let r = Propagator::propagate(r);
        // constrain inputs
        let r = InputConstrainer::constrain(r);
        // optimize uint expressions
        let r = UintOptimizer::optimize(r);
        r
    }
}

impl<T: Field> Analyse for FlatProg<T> {
    fn analyse(self) -> Self {
        self.propagate()
    }
}
