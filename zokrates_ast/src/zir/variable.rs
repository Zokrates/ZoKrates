use crate::zir::types::{Type, UBitwidth};
use crate::zir::Identifier;
use std::fmt;

#[derive(Clone, PartialEq, Hash, Eq)]
pub struct Variable<I> {
    pub id: Identifier<I>,
    pub _type: Type,
}

impl<I> Variable<I> {
    pub fn field_element<J: Into<Identifier<I>>>(id: J) -> Variable<I> {
        Self::with_id_and_type(id, Type::FieldElement)
    }

    pub fn boolean(id: Identifier<I>) -> Variable<I> {
        Self::with_id_and_type(id, Type::Boolean)
    }

    pub fn uint<W: Into<UBitwidth>>(id: Identifier<I>, bitwidth: W) -> Variable<I> {
        Self::with_id_and_type(id, Type::uint(bitwidth))
    }

    pub fn with_id_and_type<J: Into<Identifier<I>>>(id: J, _type: Type) -> Variable<I> {
        Variable {
            id: id.into(),
            _type,
        }
    }

    pub fn get_type(&self) -> Type {
        self._type.clone()
    }
}

impl<I: fmt::Display> fmt::Display for Variable<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self._type, self.id,)
    }
}

impl<I: fmt::Debug> fmt::Debug for Variable<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Variable(type: {:?}, id: {:?})", self._type, self.id,)
    }
}
