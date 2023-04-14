use crate::typed::types::DeclarationConstant;
use crate::typed::GVariable;

pub type GParameter<'ast, S> = crate::common::Parameter<GVariable<'ast, S>>;
pub type DeclarationParameter<'ast, T> = GParameter<'ast, DeclarationConstant<'ast, T>>;
