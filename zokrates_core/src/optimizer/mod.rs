//! Module containing flat program optimization
//!
//! @file mod.rs
//! @author Thibaut Schaeffer <thibaut@schaeff.fr>
//! @date 2018

mod duplicate;
mod redefinition;
mod tautology;

use self::duplicate::DuplicateOptimizer;
use self::redefinition::RedefinitionOptimizer;
use self::tautology::TautologyOptimizer;
use compile::CompileConfig;

use crate::ir::Prog;
use zokrates_field::Field;

impl<T: Field> Prog<T> {
    pub fn optimize(self, config: &CompileConfig) -> Self {
        let r = if config.is_release() {
            // remove redefinitions
            RedefinitionOptimizer::optimize(self)
        } else {
            self
        };
        // remove constraints that are always satisfied
        let r = TautologyOptimizer::optimize(r);
        // remove duplicate constraints
        let r = DuplicateOptimizer::optimize(r);
        r
    }
}
