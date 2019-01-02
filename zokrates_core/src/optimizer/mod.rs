//! Module containing flat program optimization
//!
//! @file mod.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

mod dead_code;
mod redefinition;

use self::dead_code::DeadCodeOptimizer;
use self::redefinition::RedefinitionOptimizer;

use flat_absy::FlatProg;
use zokrates_field::field::Field;

pub trait Optimize {
    fn optimize(self) -> Self;
}

impl<T: Field> Optimize for FlatProg<T> {
    fn optimize(self) -> Self {
        // only keep the main function
        let r = DeadCodeOptimizer::optimize(self);
        // remove redefinitions
        let r = RedefinitionOptimizer::optimize(r);
        r
    }
}
