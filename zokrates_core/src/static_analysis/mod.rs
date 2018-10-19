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

use flat_absy::FlatProg;
use field::Field;
use typed_absy::TypedProg;
use self::unroll::Unroll;
use self::inline::Inliner;
use self::dead_code::DeadCode;

pub trait Analyse {
	fn analyse(self) -> Self;
}

impl<T: Field> Analyse for TypedProg<T> {
	fn analyse(self) -> Self {
		// unroll and propagate a first time for constants to reach function calls
		let r = self.unroll().propagate();
		// apply inlining strategy and propagate again
		let r = Inliner::inline(r).propagate();
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