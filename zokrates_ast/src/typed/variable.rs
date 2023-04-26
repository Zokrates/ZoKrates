use crate::common::WithSpan;
use crate::typed::types::{DeclarationConstant, GStructType, UBitwidth};
use crate::typed::types::{GType, SpecializationError};
use crate::typed::Identifier;
use crate::typed::UExpression;
use crate::typed::{TryFrom, TryInto};

pub type GVariable<'ast, S> = crate::common::Variable<Identifier<'ast>, GType<S>>;
pub type DeclarationVariable<'ast, T> = GVariable<'ast, DeclarationConstant<'ast, T>>;
pub type ConcreteVariable<'ast> = GVariable<'ast, u32>;
pub type Variable<'ast, T> = GVariable<'ast, UExpression<'ast, T>>;

impl<'ast, T> TryFrom<Variable<'ast, T>> for ConcreteVariable<'ast> {
    type Error = SpecializationError;

    fn try_from(v: Variable<'ast, T>) -> Result<Self, Self::Error> {
        let span = v.get_span();

        let ty = v.ty.try_into()?;

        Ok(Self::new(v.id, ty).span(span))
    }
}

impl<'ast, T> From<ConcreteVariable<'ast>> for Variable<'ast, T> {
    fn from(v: ConcreteVariable<'ast>) -> Self {
        let span = v.get_span();

        let ty = v.ty.into();

        Self::new(v.id, ty).span(span)
    }
}

pub fn try_from_g_variable<T: TryInto<U>, U>(
    v: GVariable<T>,
) -> Result<GVariable<U>, SpecializationError> {
    let span = v.get_span();

    let ty = crate::typed::types::try_from_g_type(v.ty)?;

    Ok(GVariable::new(v.id, ty).span(span))
}

impl<'ast, S: Clone> GVariable<'ast, S> {
    pub fn field_element<I: Into<Identifier<'ast>>>(id: I) -> Self {
        Self::new(id, GType::FieldElement)
    }

    pub fn boolean<I: Into<Identifier<'ast>>>(id: I) -> Self {
        Self::new(id, GType::Boolean)
    }

    pub fn uint<I: Into<Identifier<'ast>>, W: Into<UBitwidth>>(id: I, bitwidth: W) -> Self {
        Self::new(id, GType::uint(bitwidth))
    }

    pub fn array<I: Into<Identifier<'ast>>, U: Into<S>>(id: I, ty: GType<S>, size: U) -> Self {
        Self::new(id, GType::array((ty, size.into())))
    }

    pub fn struc<I: Into<Identifier<'ast>>>(id: I, ty: GStructType<S>) -> Self {
        Self::new(id, GType::Struct(ty))
    }

    pub fn get_type(&self) -> GType<S> {
        self.ty.clone()
    }
}
