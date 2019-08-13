//! Module containing flat program optimization
//!
//! @file mod.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

mod redefinition;
mod tautology;

pub use self::redefinition::RedefinitionOptimizer;
use self::tautology::TautologyOptimizer;

use crate::ir::Prog;
use zokrates_field::field::Field;

pub trait Optimize {
    fn optimize(self) -> Self;
}

impl<T: Field> Optimize for Prog<T> {
    fn optimize(self) -> Self {
        // remove redefinitions
        println!("redef");
        let r = RedefinitionOptimizer::optimize(self);
        println!("tautology");
        // remove constraints that are always satisfied
        let r = TautologyOptimizer::optimize(r);
        r
    }
}
