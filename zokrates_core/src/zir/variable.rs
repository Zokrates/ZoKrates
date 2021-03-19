use crate::zir::types::{Type, UBitwidth};
use crate::zir::Identifier;
use std::fmt;

#[derive(Clone, PartialEq, Hash, Eq)]
pub struct Variable<'ast> {
    pub id: Identifier<'ast>,
    pub _type: Type,
}

impl<'ast> Variable<'ast> {
    pub fn field_element<I: Into<Identifier<'ast>>>(id: I) -> Variable<'ast> {
        Self::with_id_and_type(id, Type::FieldElement)
    }

    pub fn boolean(id: Identifier<'ast>) -> Variable<'ast> {
        Self::with_id_and_type(id, Type::Boolean)
    }

    pub fn uint<W: Into<UBitwidth>>(id: Identifier<'ast>, bitwidth: W) -> Variable<'ast> {
        Self::with_id_and_type(id, Type::uint(bitwidth))
    }

    pub fn with_id_and_type<I: Into<Identifier<'ast>>>(id: I, _type: Type) -> Variable<'ast> {
        Variable {
            id: id.into(),
            _type,
        }
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
