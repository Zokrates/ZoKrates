//! Module containing static analysis
//!
//! @file mod.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

mod dead_code;
mod flat_propagation;
mod inline;
mod propagation;
mod unroll;

use self::dead_code::DeadCode;
use self::inline::Inliner;
use self::propagation::Propagator;
use self::unroll::Unroller;
use crate::flat_absy::FlatProg;
use crate::typed_absy::TypedProg;
use zokrates_field::field::Field;

pub trait Analyse {
    fn analyse(self) -> Self;
}

impl<'ast, T: Field> Analyse for TypedProg<'ast, T> {
    fn analyse(self) -> Self {
        // unroll
        let r = Unroller::unroll(self);
        //propagate a first time for constants to reach function calls
        let r = Propagator::propagate(r);
        // apply inlining strategy
        let r = Inliner::inline(r);
        // Propagate again
        let r = Propagator::propagate(r);
        // remove unused functions
        let r = DeadCode::clean(r);
        r
    }
}

impl<T: Field> Analyse for FlatProg<T> {
    fn analyse(self) -> Self {
        self.propagate()
    }
}
