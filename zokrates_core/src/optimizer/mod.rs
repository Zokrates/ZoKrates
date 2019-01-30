//! Module containing flat program optimization
//!
//! @file mod.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

mod redefinition;
mod tautology;

use self::redefinition::RedefinitionOptimizer;
use self::tautology::TautologyOptimizer;

use ir::Prog;
use zokrates_field::field::Field;

pub trait Optimize {
    fn optimize(self) -> Self;
}

impl<T: Field> Optimize for Prog<T> {
    fn optimize(self) -> Self {
        // // only keep the main function
        // let r = DeadCodeOptimizer::optimize(self);
        // // remove redefinitions
        let r = RedefinitionOptimizer::optimize(self);
        let r = TautologyOptimizer::optimize(r);
        r
    }
}
