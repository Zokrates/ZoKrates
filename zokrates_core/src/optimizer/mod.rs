//! Module containing flat program optimization
//!
//! @file mod.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

mod directive;
mod duplicate;
mod redefinition;
mod tautology;

use self::directive::DirectiveOptimizer;
use self::duplicate::DuplicateOptimizer;
use self::redefinition::RedefinitionOptimizer;
use self::tautology::TautologyOptimizer;

use crate::ir::Prog;
use zokrates_field::field::Field;

pub trait Optimize {
    fn optimize(self) -> Self;
}

impl<T: Field> Optimize for Prog<T> {
    fn optimize(self) -> Self {
        // remove redefinitions
        println!("opt 1");
        let r = RedefinitionOptimizer::optimize(self);
        // remove constraints that are always satisfied
        println!("opt 2");
        let r = TautologyOptimizer::optimize(r);
        // // deduplicate directives which take the same input
        println!("opt 3");
        let r = DirectiveOptimizer::optimize(r);
        // remove duplicate constraints
        println!("opt 4");
        let r = DuplicateOptimizer::optimize(r);
        r
    }
}
