//! Module containing flat program optimization
//!
//! @file mod.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

mod canonicalizer;
mod directive;
mod duplicate;
mod redefinition;
mod tautology;

use self::directive::DirectiveOptimizer;
use self::duplicate::DuplicateOptimizer;
use self::redefinition::RedefinitionOptimizer;
use self::tautology::TautologyOptimizer;

use crate::ir::Prog;
use zokrates_field::Field;

impl<T: Field> Prog<T> {
    pub fn optimize(self) -> Self {
        // remove redefinitions
        let r = RedefinitionOptimizer::optimize(self);
        // remove constraints that are always satisfied
        let r = TautologyOptimizer::optimize(r);
        // // deduplicate directives which take the same input
        let r = DirectiveOptimizer::optimize(r);
        // remove duplicate constraints
        DuplicateOptimizer::optimize(r)
    }
}
