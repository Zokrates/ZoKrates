//! Module containing static analysis
//!
//! @file mod.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

mod propagation;
mod unroll;
mod flat_propagation;

use flat_absy::FlatProg;
use field::Field;
use typed_absy::TypedProg;
use self::unroll::Unroll;

pub trait Analyse {
	fn analyse(self) -> Self;
}

impl<T: Field> Analyse for TypedProg<T> {
	fn analyse(self) -> Self {
		//self.unroll().propagate()
		let r = self.unroll();
		let r = r.propagate();
		print!("propagated! {}", r);
		r
	}
}

impl<T: Field> Analyse for FlatProg<T> {
	fn analyse(self) -> Self {
		self.propagate()
	}
}