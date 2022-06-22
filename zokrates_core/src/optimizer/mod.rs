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

use self::canonicalizer::Canonicalizer;
use self::directive::DirectiveOptimizer;
use self::duplicate::DuplicateOptimizer;
use self::redefinition::RedefinitionOptimizer;
use self::tautology::TautologyOptimizer;

use zokrates_ast::ir::{ProgIterator, Statement};
use zokrates_field::Field;

pub fn optimize<T: Field, I: IntoIterator<Item = Statement<T>>>(
    p: ProgIterator<T, I>,
) -> ProgIterator<T, impl IntoIterator<Item = Statement<T>>> {
    // remove redefinitions
    log::debug!("Optimizer: Remove redefinitions and tautologies and directives and duplicates");

    // define all optimizer steps
    let mut redefinition_optimizer = RedefinitionOptimizer::init(&p);
    let mut tautologies_optimizer = TautologyOptimizer::default();
    let mut directive_optimizer = DirectiveOptimizer::default();
    let mut canonicalizer = Canonicalizer::default();
    let mut duplicate_optimizer = DuplicateOptimizer::default();

    use zokrates_ast::ir::folder::Folder;

    let r = ProgIterator {
        arguments: p
            .arguments
            .into_iter()
            .map(|a| redefinition_optimizer.fold_argument(a))
            .map(|a| {
                <TautologyOptimizer as Folder<T>>::fold_argument(&mut tautologies_optimizer, a)
            })
            .map(|a| directive_optimizer.fold_argument(a))
            .map(|a| <DuplicateOptimizer as Folder<T>>::fold_argument(&mut duplicate_optimizer, a))
            .collect(),
        statements: p
            .statements
            .into_iter()
            .flat_map(move |s| redefinition_optimizer.fold_statement(s))
            .flat_map(move |s| tautologies_optimizer.fold_statement(s))
            .flat_map(move |s| canonicalizer.fold_statement(s))
            .flat_map(move |s| directive_optimizer.fold_statement(s))
            .flat_map(move |s| duplicate_optimizer.fold_statement(s)),
        return_count: p.return_count,
    };

    log::debug!("Done");
    r
}
