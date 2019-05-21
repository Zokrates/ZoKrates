//! Module containing static analysis
//!
//! @file mod.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

mod core_lib_injector;
mod flat_propagation;
mod power_check;
mod propagation;
mod unroll;

use self::core_lib_injector::CoreLibInjector;
use self::power_check::PowerChecker;
use self::propagation::Propagator;
use self::unroll::Unroller;
use crate::flat_absy::FlatProg;
use crate::typed_absy::TypedProgram;
use zokrates_field::field::Field;

pub trait Analyse {
    fn analyse(self) -> Self;
}

impl<T: Field> Analyse for TypedProgram<T> {
    fn analyse(self) -> Self {
        println!("{}", self);
        let r = PowerChecker::check(self);
        // unroll
        let r = Unroller::unroll(r);
        // propagate
        let r = Propagator::propagate(r);
        // inject core lib
        let r = CoreLibInjector::inject(r);
        r
    }
}

impl<T: Field> Analyse for FlatProg<T> {
    fn analyse(self) -> Self {
        self.propagate()
    }
}
