//! Module containing static analysis
//!
//! @file mod.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

mod propagation;
mod unroll;
mod flat_propagation;
mod inline;

use flat_absy::FlatProg;
use field::Field;
use typed_absy::TypedProg;
use self::unroll::Unroll;
use self::inline::Inliner;

pub trait Analyse {
	fn analyse(self) -> Self;
}

impl<T: Field> Analyse for TypedProg<T> {
	fn analyse(self) -> Self {
		// unroll and propagate a first time for constants to reach function calls
		let r = self.unroll().propagate();
		// apply inlining strategy and propagate again
		Inliner::inline(r).propagate()
	}
}

impl<T: Field> Analyse for FlatProg<T> {
	fn analyse(self) -> Self {
		self.propagate()
	}
}