use super::{Folder, Identifier};
use std::{collections::HashMap, marker::PhantomData};
use zokrates_field::Field;

pub struct ZirSubstitutor<'a, 'ast, T> {
    substitution: &'a HashMap<Identifier<'ast>, Identifier<'ast>>,
    _phantom: PhantomData<T>,
}

impl<'a, 'ast, T: Field> ZirSubstitutor<'a, 'ast, T> {
    pub fn new(substitution: &'a HashMap<Identifier<'ast>, Identifier<'ast>>) -> Self {
        ZirSubstitutor {
            substitution,
            _phantom: PhantomData::default(),
        }
    }
}

impl<'a, 'ast, T: Field> Folder<'ast, T> for ZirSubstitutor<'a, 'ast, T> {
    fn fold_name(&mut self, n: Identifier<'ast>) -> Identifier<'ast> {
        match self.substitution.get(&n) {
            Some(v) => v.clone(),
            None => n,
        }
    }
}
