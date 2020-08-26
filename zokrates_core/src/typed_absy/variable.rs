use crate::typed_absy::types::GType;
use crate::typed_absy::Identifier;
use std::fmt;
use typed_absy::types::{Constant, GStructType, UBitwidth};
use typed_absy::TryFrom;
use typed_absy::UExpression;

#[derive(Clone, PartialEq, Hash, Eq)]
pub struct GVariable<'ast, S> {
    pub id: Identifier<'ast>,
    pub _type: GType<S>,
}

pub type DeclarationVariable<'ast> = GVariable<'ast, Constant<'ast>>;
pub type ConcreteVariable<'ast> = GVariable<'ast, usize>;
pub type Variable<'ast, T> = GVariable<'ast, UExpression<'ast, T>>;

impl<'ast, T> TryFrom<Variable<'ast, T>> for ConcreteVariable<'ast> {
    type Error = ();

    fn try_from(t: Variable<'ast, T>) -> Result<Self, Self::Error> {
        unimplemented!()
    }
}

impl<'ast> TryFrom<DeclarationVariable<'ast>> for ConcreteVariable<'ast> {
    type Error = ();

    fn try_from(t: DeclarationVariable<'ast>) -> Result<Self, Self::Error> {
        unimplemented!()
    }
}

impl<'ast, T> From<ConcreteVariable<'ast>> for Variable<'ast, T> {
    fn from(t: ConcreteVariable<'ast>) -> Self {
        unimplemented!()
    }
}

impl<'ast, T> From<DeclarationVariable<'ast>> for Variable<'ast, T> {
    fn from(t: DeclarationVariable<'ast>) -> Self {
        unimplemented!()
    }
}

impl<'ast, S> GVariable<'ast, S> {
    pub fn field_element<I: Into<Identifier<'ast>>>(id: I) -> Self {
        Self::with_id_and_type(id, GType::FieldElement)
    }

    pub fn boolean<I: Into<Identifier<'ast>>>(id: I) -> Self {
        Self::with_id_and_type(id, GType::Boolean)
    }

    pub fn uint<I: Into<Identifier<'ast>>, W: Into<UBitwidth>>(id: I, bitwidth: W) -> Self {
        Self::with_id_and_type(id, GType::uint(bitwidth))
    }

    #[cfg(test)]
    pub fn field_array<I: Into<Identifier<'ast>>>(id: I, size: S) -> Self {
        Self::array(id, GType::FieldElement, size)
    }

    pub fn array<I: Into<Identifier<'ast>>>(id: I, ty: GType<S>, size: S) -> Self {
        Self::with_id_and_type(id, GType::array(ty, size))
    }

    pub fn struc<I: Into<Identifier<'ast>>>(id: I, ty: GStructType<S>) -> Self {
        Self::with_id_and_type(id, GType::Struct(ty))
    }

    pub fn with_id_and_type<I: Into<Identifier<'ast>>>(id: I, _type: GType<S>) -> Self {
        GVariable {
            id: id.into(),
            _type,
        }
    }

    pub fn get_type(&self) -> GType<S> {
        self._type.clone()
    }
}

impl<'ast, S> fmt::Display for GVariable<'ast, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self._type, self.id,)
    }
}

impl<'ast, S> fmt::Debug for GVariable<'ast, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Variable(type: {:?}, id: {:?})", self._type, self.id,)
    }
}
