//! Module containing flat program optimization
//!
//! @file mod.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

mod redefinition;
mod tautology;

use self::redefinition::RedefinitionOptimizer;
use self::tautology::TautologyOptimizer;

use zokrates_field::field::Field;
use zokrates_ir::Prog;

pub trait Optimize {
    fn optimize(self) -> Self;
}

impl<T: Field> Optimize for Prog<T> {
    fn optimize(self) -> Self {
        // remove redefinitions
        let r = RedefinitionOptimizer::optimize(self);
        // remove constraints that are always satisfied
        let r = TautologyOptimizer::optimize(r);
        r
    }
}
