//! Module containing static analysis
//!
//! @file mod.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

mod core_lib_injector;
mod flat_propagation;
mod flat_resolver;
mod inline;
mod power_check;
mod propagation;
mod unroll;

pub use self::core_lib_injector::CoreLibInjector;
use self::flat_resolver::FlatResolver;
use self::inline::Inliner;
use self::power_check::PowerChecker;
use self::propagation::Propagator;
use self::unroll::Unroller;
use crate::flat_absy::FlatProg;
use crate::typed_absy::TypedProgram;
use zokrates_field::field::Field;

pub trait Analyse {
    fn analyse(self) -> Self;
}

impl<'ast, T: Field> Analyse for TypedProgram<'ast, T> {
    fn analyse(self) -> Self {
        let r = PowerChecker::check(self);
        // remove chains of imports ending by a flat function
        let r = FlatResolver::resolve(r);
        // unroll
        let r = Unroller::unroll(r);
        // inline
        let r = Inliner::inline(r);
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
