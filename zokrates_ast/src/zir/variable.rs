use crate::zir::types::{Type, UBitwidth};
use crate::zir::Identifier;

pub type Variable<'ast> = crate::common::Variable<Identifier<'ast>, Type>;

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

    pub fn with_id_and_type<I: Into<Identifier<'ast>>>(id: I, ty: Type) -> Variable<'ast> {
        Variable::new(id.into(), ty)
    }

    pub fn get_type(&self) -> Type {
        self.ty.clone()
    }
}
