use crate::typed::types::{DeclarationConstant, GStructType, UBitwidth};
use crate::typed::types::{GType, SpecializationError};
use crate::typed::Identifier;
use crate::typed::UExpression;
use crate::typed::{TryFrom, TryInto};
use std::fmt;

#[derive(Clone, PartialEq, Hash, Eq, PartialOrd, Ord, Debug)]
pub struct GVariable<'ast, S> {
    pub id: Identifier<'ast>,
    pub _type: GType<S>,
    pub is_mutable: bool,
}

pub type DeclarationVariable<'ast, T> = GVariable<'ast, DeclarationConstant<'ast, T>>;
pub type ConcreteVariable<'ast> = GVariable<'ast, u32>;
pub type Variable<'ast, T> = GVariable<'ast, UExpression<'ast, T>>;

impl<'ast, T> TryFrom<Variable<'ast, T>> for ConcreteVariable<'ast> {
    type Error = SpecializationError;

    fn try_from(v: Variable<'ast, T>) -> Result<Self, Self::Error> {
        let _type = v._type.try_into()?;

        Ok(Self {
            _type,
            id: v.id,
            is_mutable: v.is_mutable,
        })
    }
}

impl<'ast, T> From<ConcreteVariable<'ast>> for Variable<'ast, T> {
    fn from(v: ConcreteVariable<'ast>) -> Self {
        let _type = v._type.into();

        Self {
            _type,
            id: v.id,
            is_mutable: v.is_mutable,
        }
    }
}

pub fn try_from_g_variable<T: TryInto<U>, U>(
    v: GVariable<T>,
) -> Result<GVariable<U>, SpecializationError> {
    let _type = crate::typed::types::try_from_g_type(v._type)?;

    Ok(GVariable {
        _type,
        id: v.id,
        is_mutable: v.is_mutable,
    })
}

impl<'ast, S: Clone> GVariable<'ast, S> {
    pub fn field_element<I: Into<Identifier<'ast>>>(id: I) -> Self {
        Self::immutable(id, GType::FieldElement)
    }

    pub fn boolean<I: Into<Identifier<'ast>>>(id: I) -> Self {
        Self::immutable(id, GType::Boolean)
    }

    pub fn uint<I: Into<Identifier<'ast>>, W: Into<UBitwidth>>(id: I, bitwidth: W) -> Self {
        Self::immutable(id, GType::uint(bitwidth))
    }

    pub fn array<I: Into<Identifier<'ast>>, U: Into<S>>(id: I, ty: GType<S>, size: U) -> Self {
        Self::immutable(id, GType::array((ty, size.into())))
    }

    pub fn struc<I: Into<Identifier<'ast>>>(id: I, ty: GStructType<S>) -> Self {
        Self::immutable(id, GType::Struct(ty))
    }

    pub fn immutable<I: Into<Identifier<'ast>>>(id: I, _type: GType<S>) -> Self {
        Self::new(id, _type, false)
    }

    pub fn mutable<I: Into<Identifier<'ast>>>(id: I, _type: GType<S>) -> Self {
        Self::new(id, _type, true)
    }

    pub fn new<I: Into<Identifier<'ast>>>(id: I, _type: GType<S>, is_mutable: bool) -> Self {
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

impl<'ast, S: fmt::Display> fmt::Display for GVariable<'ast, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {}", self._type, self.id,)
    }
}
