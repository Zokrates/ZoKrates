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
    #[zokrates_macro::stopwatch]
    pub fn optimize(self) -> Self {
        // remove redefinitions
        log::debug!("Constraints: {}", self.constraint_count());
        log::debug!("Optimizer: Remove redefinitions");
        let r = RedefinitionOptimizer::optimize(self);
        log::debug!("Done");

        // remove constraints that are always satisfied
        log::debug!("Constraints: {}", r.constraint_count());
        log::debug!("Optimizer: Remove tautologies");
        let r = TautologyOptimizer::optimize(r);
        log::debug!("Done");

        // deduplicate directives which take the same input
        log::debug!("Constraints: {}", r.constraint_count());
        log::debug!("Optimizer: Remove duplicate directive");
        let r = DirectiveOptimizer::optimize(r);
        log::debug!("Done");

        // remove duplicate constraints
        log::debug!("Constraints: {}", r.constraint_count());
        log::debug!("Optimizer: Remove duplicate constraints");
        let r = DuplicateOptimizer::optimize(r);
        log::debug!("Done");

        log::debug!("Constraints: {}", r.constraint_count());
        r
    }
}
