use super::{Folder, Identifier, Parameter, Variable, ZirAssignee};
use std::collections::HashMap;
use zokrates_field::Field;

#[derive(Default)]
pub struct ZirCanonicalizer<'ast> {
    identifier_map: HashMap<Identifier<'ast>, usize>,
}

impl<'ast, T: Field> Folder<'ast, T> for ZirCanonicalizer<'ast> {
    fn fold_parameter(&mut self, p: Parameter<'ast>) -> Parameter<'ast> {
        let new_id = self.identifier_map.len();
        self.identifier_map.insert(p.id.id.clone(), new_id);

        Parameter {
            id: Variable::with_id_and_type(Identifier::internal(new_id), p.id.ty),
            ..p
        }
    }
    fn fold_assignee(&mut self, a: ZirAssignee<'ast>) -> ZirAssignee<'ast> {
        let new_id = self.identifier_map.len();
        self.identifier_map.insert(a.id.clone(), new_id);
        ZirAssignee::with_id_and_type(Identifier::internal(new_id), a.ty)
    }
    fn fold_name(&mut self, n: Identifier<'ast>) -> Identifier<'ast> {
        match self.identifier_map.get(&n) {
            Some(v) => Identifier::internal(*v),
            None => unreachable!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::zir::{
        FieldElementExpression, IdentifierExpression, Signature, Type, ZirAssignee, ZirFunction,
        ZirStatement,
    };

    use super::*;
    use zokrates_field::Bn128Field;

    #[test]
    fn canonicalize() {
        let func = ZirFunction::<Bn128Field> {
            arguments: vec![Parameter::new(Variable::field_element("a"), true)],
            statements: vec![
                ZirStatement::definition(
                    ZirAssignee::field_element("b"),
                    FieldElementExpression::Identifier(IdentifierExpression::new("a".into()))
                        .into(),
                ),
                ZirStatement::ret(vec![FieldElementExpression::Identifier(
                    IdentifierExpression::new("b".into()),
                )
                .into()]),
            ],
            signature: Signature::new()
                .inputs(vec![Type::FieldElement])
                .outputs(vec![Type::FieldElement]),
        };

        let mut canonicalizer = ZirCanonicalizer::default();
        let result = canonicalizer.fold_function(func);

        let expected = ZirFunction::<Bn128Field> {
            arguments: vec![Parameter::new(
                Variable::field_element(Identifier::internal(0usize)),
                true,
            )],
            statements: vec![
                ZirStatement::definition(
                    ZirAssignee::field_element(Identifier::internal(1usize)),
                    FieldElementExpression::Identifier(IdentifierExpression::new(
                        Identifier::internal(0usize),
                    ))
                    .into(),
                ),
                ZirStatement::ret(vec![FieldElementExpression::Identifier(
                    IdentifierExpression::new(Identifier::internal(1usize)),
                )
                .into()]),
            ],
            signature: Signature::new()
                .inputs(vec![Type::FieldElement])
                .outputs(vec![Type::FieldElement]),
        };

        assert_eq!(result, expected);
    }
}
