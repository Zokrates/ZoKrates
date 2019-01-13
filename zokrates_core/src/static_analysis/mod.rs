//! Module containing static analysis
//!
//! @file mod.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

mod dead_code;
mod flat_propagation;
mod inline;
mod power_check;
mod propagation;
mod unroll;

use self::dead_code::DeadCode;
use self::inline::Inliner;
use self::power_check::PowerChecker;
use self::propagation::Propagator;
use self::unroll::Unroller;
use flat_absy::FlatProg;
use typed_absy::TypedProg;
use zokrates_field::field::Field;

pub trait Analyse {
    fn analyse(self) -> Self;
}

impl<T: Field> Analyse for TypedProg<T> {
    fn analyse(self) -> Self {
        let r = PowerChecker::check(self);
        // unroll
        let r = Unroller::unroll(r);
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
