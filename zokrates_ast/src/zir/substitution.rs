use super::{Folder, Identifier, Parameter, Variable, ZirAssignee};
use std::collections::HashMap;
use zokrates_field::Field;

#[derive(Default)]
pub struct ZirSubstitutor<'ast> {
    substitution: HashMap<Identifier<'ast>, usize>,
}

impl<'ast, T: Field> Folder<'ast, T> for ZirSubstitutor<'ast> {
    fn fold_parameter(&mut self, p: Parameter<'ast>) -> Parameter<'ast> {
        let new_id = self.substitution.len();
        self.substitution.insert(p.id.id.clone(), new_id);

        Parameter {
            id: Variable::with_id_and_type(Identifier::internal(new_id), p.id._type),
            ..p
        }
    }
    fn fold_assignee(&mut self, a: ZirAssignee<'ast>) -> ZirAssignee<'ast> {
        let new_id = self.substitution.len();
        self.substitution.insert(a.id.clone(), new_id);
        ZirAssignee::with_id_and_type(Identifier::internal(new_id), a._type)
    }
    fn fold_name(&mut self, n: Identifier<'ast>) -> Identifier<'ast> {
        match self.substitution.get(&n) {
            Some(v) => Identifier::internal(*v),
            None => unreachable!(),
        }
    }
}
