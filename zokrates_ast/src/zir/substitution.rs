use super::{Folder, Identifier};
use std::collections::HashMap;
use zokrates_field::Field;

#[derive(Default)]
pub struct ZirSubstitutor<'ast> {
    substitution: HashMap<Identifier<'ast>, Identifier<'ast>>,
}

impl<'ast> ZirSubstitutor<'ast> {
    pub fn new(substitution: HashMap<Identifier<'ast>, Identifier<'ast>>) -> Self {
        Self { substitution }
    }
}

impl<'ast, T: Field> Folder<'ast, T> for ZirSubstitutor<'ast> {
    fn fold_name(&mut self, n: Identifier<'ast>) -> Identifier<'ast> {
        match self.substitution.get(&n) {
            Some(v) => v.clone(),
            None => n,
        }
    }
}
