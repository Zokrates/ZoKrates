use crate::absy;
use crate::typed_absy::Identifier;
use crate::types::Type;
use std::fmt;

#[derive(Clone, PartialEq, Hash, Eq)]
pub struct Variable<'ast> {
    pub id: Identifier<'ast>,
    pub _type: Type,
}

impl<'ast> Variable<'ast> {
    pub fn field_element(id: Identifier<'ast>) -> Variable<'ast> {
        Self::with_id_and_type(id, Type::FieldElement)
    }

    pub fn boolean(id: Identifier<'ast>) -> Variable<'ast> {
        Self::with_id_and_type(id, Type::Boolean)
    }

    pub fn field_array(id: Identifier<'ast>, size: usize) -> Variable<'ast> {
        Self::with_id_and_type(id, Type::FieldElementArray(size))
    }

    pub fn with_id_and_type(id: Identifier<'ast>, _type: Type) -> Variable<'ast> {
        Variable { id, _type }
    }

    pub fn get_type(&self) -> Type {
        self._type.clone()
    }
}

impl<'ast> fmt::Display for Variable<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self._type, self.id,)
    }
}

impl<'ast> fmt::Debug for Variable<'ast> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Variable(type: {:?}, id: {:?})", self._type, self.id,)
    }
}

impl<'ast> From<absy::Variable<'ast>> for Variable<'ast> {
    fn from(v: absy::Variable) -> Variable {
        Variable::with_id_and_type(
            Identifier {
                id: v.id,
                version: 0,
                stack: vec![],
            },
            v._type,
        )
    }
}
