use crate::typed::types::{DeclarationConstant, GStructType, UBitwidth};
use crate::typed::types::{GType, SpecializationError};
use crate::typed::Identifier;
use crate::typed::UExpression;
use crate::typed::{TryFrom, TryInto};
use std::fmt;

#[derive(Clone, PartialEq, Hash, Eq, PartialOrd, Ord, Debug)]
pub struct GVariable<I, S> {
    pub id: Identifier<I>,
    pub _type: GType<S>,
    pub is_mutable: bool,
}

pub type DeclarationVariable<I, T> = GVariable<I, DeclarationConstant<I, T>>;
pub type ConcreteVariable<I> = GVariable<I, u32>;
pub type Variable<I, T> = GVariable<I, UExpression<I, T>>;

impl<I, T> TryFrom<Variable<I, T>> for ConcreteVariable<I> {
    type Error = SpecializationError;

    fn try_from(v: Variable<I, T>) -> Result<Self, Self::Error> {
        let _type = v._type.try_into()?;

        Ok(Self {
            _type,
            id: v.id,
            is_mutable: v.is_mutable,
        })
    }
}

impl<I, T> From<ConcreteVariable<I>> for Variable<I, T> {
    fn from(v: ConcreteVariable<I>) -> Self {
        let _type = v._type.into();

        Self {
            _type,
            id: v.id,
            is_mutable: v.is_mutable,
        }
    }
}

pub fn try_from_g_variable<I, T: TryInto<U>, U>(
    v: GVariable<I, T>,
) -> Result<GVariable<I, U>, SpecializationError> {
    let _type = crate::typed::types::try_from_g_type(v._type)?;

    Ok(GVariable {
        _type,
        id: v.id,
        is_mutable: v.is_mutable,
    })
}

impl<I, S: Clone> GVariable<I, S> {
    pub fn field_element<J: Into<Identifier<I>>>(id: J) -> Self {
        Self::immutable(id, GType::FieldElement)
    }

    pub fn boolean<J: Into<Identifier<I>>>(id: J) -> Self {
        Self::immutable(id, GType::Boolean)
    }

    pub fn uint<J: Into<Identifier<I>>, W: Into<UBitwidth>>(id: J, bitwidth: W) -> Self {
        Self::immutable(id, GType::uint(bitwidth))
    }

    pub fn array<J: Into<Identifier<I>>, U: Into<S>>(id: J, ty: GType<S>, size: U) -> Self {
        Self::immutable(id, GType::array((ty, size.into())))
    }

    pub fn struc<J: Into<Identifier<I>>>(id: J, ty: GStructType<S>) -> Self {
        Self::immutable(id, GType::Struct(ty))
    }

    pub fn immutable<J: Into<Identifier<I>>>(id: J, _type: GType<S>) -> Self {
        Self::new(id, _type, false)
    }

    pub fn mutable<J: Into<Identifier<I>>>(id: J, _type: GType<S>) -> Self {
        Self::new(id, _type, true)
    }

    pub fn new<J: Into<Identifier<I>>>(id: J, _type: GType<S>, is_mutable: bool) -> Self {
        GVariable {
            id: id.into(),
            _type,
            is_mutable,
        }
    }

    pub fn get_type(&self) -> GType<S> {
        self._type.clone()
    }
}

impl<I: fmt::Display, S: fmt::Display> fmt::Display for GVariable<I, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self._type, self.id,)
    }
}
