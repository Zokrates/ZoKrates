//! Module containing the `DuplicateOptimizer` to remove duplicate constraints

use crate::ir::folder::Folder;
use crate::ir::*;
use zokrates_field::field::Field;

#[derive(Debug)]
pub struct DuplicateOptimizer {}

impl DuplicateOptimizer {
    pub fn optimize<T: Field>(p: Prog<T>) -> Prog<T> {
        p
    }
}

impl<T: Field> Folder<T> for DuplicateOptimizer {}
