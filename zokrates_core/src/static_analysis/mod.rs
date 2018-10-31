//! Module containing static analysis
//!
//! @file mod.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

mod propagation;
mod unroll;
mod flat_propagation;
mod inline;
mod dead_code;
mod power_check;

use flat_absy::FlatProg;
use field::Field;
use typed_absy::TypedProg;
use self::unroll::Unroller;
use self::inline::Inliner;
use self::propagation::Propagator;
use self::dead_code::DeadCode;
use self::power_check::PowerChecker;

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