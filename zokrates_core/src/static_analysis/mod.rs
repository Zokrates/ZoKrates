//! Module containing static analysis
//!
//! @file mod.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

mod constrain_inputs;
mod flat_propagation;
mod flatten_complex_types;
mod inline;
mod propagation;
mod uint_optimizer;
mod unroll;

use zir::ZirProgram;
use self::constrain_inputs::InputConstrainer;
use self::flatten_complex_types::Flattener;
use self::inline::Inliner;
use self::propagation::Propagator;
use self::uint_optimizer::UintOptimizer;
use self::unroll::Unroller;
use crate::flat_absy::FlatProg;
use crate::typed_absy::TypedProgram;
use zokrates_field::field::Field;

pub trait Analyse {
    fn analyse(self) -> Self;
}

impl<'ast, T: Field> TypedProgram<'ast, T> {
    pub fn analyse(self) -> ZirProgram<'ast, T> {
        // unroll
        let r = Unroller::unroll(self);
        // inline
        let r = Inliner::inline(r);
        // propagate
        let r = Propagator::propagate(r);

        // println!("{}", r);

        let zir = Flattener::flatten(r.clone());

        // println!("{}", zir);

        // constrain inputs
        let zir = InputConstrainer::constrain(zir);

        // println!("{}", zir);

        // optimize uint expressions
        let zir = UintOptimizer::optimize(zir);

        println!("{}", zir);

        zir
    }
}

impl<T: Field> Analyse for FlatProg<T> {
    fn analyse(self) -> Self {
        self.propagate()
    }
}
