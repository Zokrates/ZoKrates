// Generic walk through a typed AST. Not mutating in place

use crate::common::expressions::{
    BinaryOrExpression, EqExpression, UnaryOrExpression, ValueOrExpression,
};
use crate::common::ResultFold;
use crate::typed::types::*;
use crate::typed::*;
use zokrates_field::Field;

use super::identifier::FrameIdentifier;

impl<'ast, T: Field, F: ResultFolder<'ast, T>> ResultFold<F, F::Error>
    for FieldElementExpression<'ast, T>
{
    fn fold(self, f: &mut F) -> Result<Self, F::Error> {
        f.fold_field_expression(self)
    }
}

impl<'ast, T: Field, F: ResultFolder<'ast, T>> ResultFold<F, F::Error>
    for BooleanExpression<'ast, T>
{
    fn fold(self, f: &mut F) -> Result<Self, F::Error> {
        f.fold_boolean_expression(self)
    }
}

impl<'ast, T: Field, F: ResultFolder<'ast, T>> ResultFold<F, F::Error> for UExpression<'ast, T> {
    fn fold(self, f: &mut F) -> Result<Self, F::Error> {
        f.fold_uint_expression(self)
    }
}

impl<'ast, T: Field, F: ResultFolder<'ast, T>> ResultFold<F, F::Error>
    for StructExpression<'ast, T>
{
    fn fold(self, f: &mut F) -> Result<Self, F::Error> {
        f.fold_struct_expression(self)
    }
}

impl<'ast, T: Field, F: ResultFolder<'ast, T>> ResultFold<F, F::Error>
    for ArrayExpression<'ast, T>
{
    fn fold(self, f: &mut F) -> Result<Self, F::Error> {
        f.fold_array_expression(self)
    }
}

impl<'ast, T: Field, F: ResultFolder<'ast, T>> ResultFold<F, F::Error>
    for TupleExpression<'ast, T>
{
    fn fold(self, f: &mut F) -> Result<Self, F::Error> {
        f.fold_tuple_expression(self)
    }
}

pub trait ResultFolder<'ast, T: Field>: Sized {
    type Error;

    fn fold_program(
        &mut self,
        p: TypedProgram<'ast, T>,
    ) -> Result<TypedProgram<'ast, T>, Self::Error> {
        fold_program(self, p)
    }

    fn fold_module(
        &mut self,
        m: TypedModule<'ast, T>,
    ) -> Result<TypedModule<'ast, T>, Self::Error> {
        fold_module(self, m)
    }

    fn fold_symbol_declaration(
        &mut self,
        s: TypedSymbolDeclaration<'ast, T>,
    ) -> Result<TypedSymbolDeclaration<'ast, T>, Self::Error> {
        fold_symbol_declaration(self, s)
    }

    fn fold_function_symbol_declaration(
        &mut self,
        s: TypedFunctionSymbolDeclaration<'ast, T>,
    ) -> Result<TypedFunctionSymbolDeclaration<'ast, T>, Self::Error> {
        fold_function_symbol_declaration(self, s)
    }

    fn fold_constant_symbol_declaration(
        &mut self,
        s: TypedConstantSymbolDeclaration<'ast, T>,
    ) -> Result<TypedConstantSymbolDeclaration<'ast, T>, Self::Error> {
        fold_constant_symbol_declaration(self, s)
    }

    fn fold_constant(
        &mut self,
        c: TypedConstant<'ast, T>,
    ) -> Result<TypedConstant<'ast, T>, Self::Error> {
        fold_constant(self, c)
    }

    fn fold_constant_symbol(
        &mut self,
        s: TypedConstantSymbol<'ast, T>,
    ) -> Result<TypedConstantSymbol<'ast, T>, Self::Error> {
        fold_constant_symbol(self, s)
    }

    fn fold_function_symbol(
        &mut self,
        s: TypedFunctionSymbol<'ast, T>,
    ) -> Result<TypedFunctionSymbol<'ast, T>, Self::Error> {
        fold_function_symbol(self, s)
    }

    fn fold_declaration_function_key(
        &mut self,
        key: DeclarationFunctionKey<'ast, T>,
    ) -> Result<DeclarationFunctionKey<'ast, T>, Self::Error> {
        fold_declaration_function_key(self, key)
    }

    fn fold_function(
        &mut self,
        f: TypedFunction<'ast, T>,
    ) -> Result<TypedFunction<'ast, T>, Self::Error> {
        fold_function(self, f)
    }

    fn fold_signature(
        &mut self,
        s: DeclarationSignature<'ast, T>,
    ) -> Result<DeclarationSignature<'ast, T>, Self::Error> {
        fold_signature(self, s)
    }

    fn fold_declaration_constant(
        &mut self,
        c: DeclarationConstant<'ast, T>,
    ) -> Result<DeclarationConstant<'ast, T>, Self::Error> {
        fold_declaration_constant(self, c)
    }

    fn fold_parameter(
        &mut self,
        p: DeclarationParameter<'ast, T>,
    ) -> Result<DeclarationParameter<'ast, T>, Self::Error> {
        Ok(DeclarationParameter {
            id: self.fold_declaration_variable(p.id)?,
            ..p
        })
    }

    fn fold_canonical_constant_identifier(
        &mut self,
        i: CanonicalConstantIdentifier<'ast>,
    ) -> Result<CanonicalConstantIdentifier<'ast>, Self::Error> {
        Ok(CanonicalConstantIdentifier {
            module: self.fold_module_id(i.module)?,
            id: i.id,
        })
    }

    fn fold_module_id(&mut self, i: OwnedModuleId) -> Result<OwnedModuleId, Self::Error> {
        Ok(i)
    }

    fn fold_name(&mut self, n: Identifier<'ast>) -> Result<Identifier<'ast>, Self::Error> {
        let id = match n.id.id.clone() {
            CoreIdentifier::Constant(c) => FrameIdentifier {
                id: CoreIdentifier::Constant(self.fold_canonical_constant_identifier(c)?),
                frame: 0,
            },
            _ => n.id,
        };

        Ok(Identifier { id, ..n })
    }

    fn fold_variable(&mut self, v: Variable<'ast, T>) -> Result<Variable<'ast, T>, Self::Error> {
        let span = v.get_span();
        Ok(Variable::new(self.fold_name(v.id)?, self.fold_type(v.ty)?).span(span))
    }

    fn fold_declaration_variable(
        &mut self,
        v: DeclarationVariable<'ast, T>,
    ) -> Result<DeclarationVariable<'ast, T>, Self::Error> {
        let span = v.get_span();
        Ok(
            DeclarationVariable::new(self.fold_name(v.id)?, self.fold_declaration_type(v.ty)?)
                .span(span),
        )
    }

    fn fold_type(&mut self, t: Type<'ast, T>) -> Result<Type<'ast, T>, Self::Error> {
        use self::GType::*;

        match t {
            Array(array_type) => Ok(Array(self.fold_array_type(array_type)?)),
            Struct(struct_type) => Ok(Struct(self.fold_struct_type(struct_type)?)),
            Tuple(tuple_type) => Ok(Tuple(self.fold_tuple_type(tuple_type)?)),
            t => Ok(t),
        }
    }

    fn fold_conditional_expression<
        E: Expr<'ast, T> + PartialEq + Conditional<'ast, T> + ResultFold<Self, Self::Error>,
    >(
        &mut self,
        ty: &E::Ty,
        e: ConditionalExpression<'ast, T, E>,
    ) -> Result<ConditionalOrExpression<'ast, T, E>, Self::Error> {
        fold_conditional_expression(self, ty, e)
    }

    #[allow(clippy::type_complexity)]
    fn fold_binary_expression<
        L: Expr<'ast, T> + PartialEq + ResultFold<Self, Self::Error>,
        R: Expr<'ast, T> + PartialEq + ResultFold<Self, Self::Error>,
        E: Expr<'ast, T> + PartialEq + ResultFold<Self, Self::Error>,
        Op: OperatorStr,
    >(
        &mut self,
        ty: &E::Ty,
        e: BinaryExpression<Op, L, R, E>,
    ) -> Result<BinaryOrExpression<Op, L, R, E, E::Inner>, Self::Error> {
        fold_binary_expression(self, ty, e)
    }

    #[allow(clippy::type_complexity)]
    fn fold_eq_expression<
        E: Expr<'ast, T> + Constant + Typed<'ast, T> + PartialEq + ResultFold<Self, Self::Error>,
    >(
        &mut self,
        e: EqExpression<E, BooleanExpression<'ast, T>>,
    ) -> Result<
        BinaryOrExpression<OpEq, E, E, BooleanExpression<'ast, T>, BooleanExpression<'ast, T>>,
        Self::Error,
    > {
        fold_binary_expression(self, &Type::Boolean, e)
    }

    fn fold_unary_expression<
        In: Expr<'ast, T> + PartialEq + ResultFold<Self, Self::Error>,
        E: Expr<'ast, T> + PartialEq + ResultFold<Self, Self::Error>,
        Op,
    >(
        &mut self,
        ty: &E::Ty,
        e: UnaryExpression<Op, In, E>,
    ) -> Result<UnaryOrExpression<Op, In, E, E::Inner>, Self::Error> {
        fold_unary_expression(self, ty, e)
    }

    fn fold_block_expression<E: ResultFold<Self, Self::Error>>(
        &mut self,
        block: BlockExpression<'ast, T, E>,
    ) -> Result<BlockExpression<'ast, T, E>, Self::Error> {
        fold_block_expression(self, block)
    }

    fn fold_identifier_expression<
        E: Expr<'ast, T> + Id<'ast, T> + ResultFold<Self, Self::Error>,
    >(
        &mut self,
        ty: &E::Ty,
        id: IdentifierExpression<'ast, E>,
    ) -> Result<IdentifierOrExpression<'ast, T, E>, Self::Error> {
        fold_identifier_expression(self, ty, id)
    }

    fn fold_member_expression<
        E: Expr<'ast, T> + Member<'ast, T> + From<TypedExpression<'ast, T>>,
    >(
        &mut self,
        ty: &E::Ty,
        e: MemberExpression<'ast, T, E>,
    ) -> Result<MemberOrExpression<'ast, T, E>, Self::Error> {
        fold_member_expression(self, ty, e)
    }

    fn fold_slice_expression(
        &mut self,
        e: SliceExpression<'ast, T>,
    ) -> Result<SliceOrExpression<'ast, T>, Self::Error> {
        fold_slice_expression(self, e)
    }

    fn fold_repeat_expression(
        &mut self,
        e: RepeatExpression<'ast, T>,
    ) -> Result<RepeatOrExpression<'ast, T>, Self::Error> {
        fold_repeat_expression(self, e)
    }

    fn fold_element_expression<
        E: Expr<'ast, T> + Element<'ast, T> + From<TypedExpression<'ast, T>>,
    >(
        &mut self,
        ty: &E::Ty,
        e: ElementExpression<'ast, T, E>,
    ) -> Result<ElementOrExpression<'ast, T, E>, Self::Error> {
        fold_element_expression(self, ty, e)
    }

    fn fold_select_expression<
        E: Expr<'ast, T>
            + Select<'ast, T>
            + Into<TypedExpression<'ast, T>>
            + From<TypedExpression<'ast, T>>,
    >(
        &mut self,
        ty: &E::Ty,
        e: SelectExpression<'ast, T, E>,
    ) -> Result<SelectOrExpression<'ast, T, E>, Self::Error> {
        fold_select_expression(self, ty, e)
    }

    fn fold_function_call_expression<
        E: Id<'ast, T> + From<TypedExpression<'ast, T>> + Expr<'ast, T> + FunctionCall<'ast, T>,
    >(
        &mut self,
        ty: &E::Ty,
        e: FunctionCallExpression<'ast, T, E>,
    ) -> Result<FunctionCallOrExpression<'ast, T, E>, Self::Error> {
        fold_function_call_expression(self, ty, e)
    }

    fn fold_array_type(
        &mut self,
        t: ArrayType<'ast, T>,
    ) -> Result<ArrayType<'ast, T>, Self::Error> {
        Ok(ArrayType {
            ty: Box::new(self.fold_type(*t.ty)?),
            size: Box::new(self.fold_uint_expression(*t.size)?),
        })
    }

    fn fold_tuple_type(
        &mut self,
        t: TupleType<'ast, T>,
    ) -> Result<TupleType<'ast, T>, Self::Error> {
        Ok(TupleType {
            elements: t
                .elements
                .into_iter()
                .map(|t| self.fold_type(t))
                .collect::<Result<Vec<_>, _>>()?,
        })
    }

    fn fold_struct_type(
        &mut self,
        t: StructType<'ast, T>,
    ) -> Result<StructType<'ast, T>, Self::Error> {
        Ok(StructType {
            generics: t
                .generics
                .into_iter()
                .map(|g| g.map(|g| self.fold_uint_expression(g)).transpose())
                .collect::<Result<Vec<_>, _>>()?,
            members: t
                .members
                .into_iter()
                .map(|m| {
                    let id = m.id;
                    self.fold_type(*m.ty).map(|ty| StructMember {
                        ty: Box::new(ty),
                        id,
                    })
                })
                .collect::<Result<_, _>>()?,
            ..t
        })
    }

    fn fold_declaration_type(
        &mut self,
        t: DeclarationType<'ast, T>,
    ) -> Result<DeclarationType<'ast, T>, Self::Error> {
        use self::GType::*;

        match t {
            Array(array_type) => Ok(Array(self.fold_declaration_array_type(array_type)?)),
            Struct(struct_type) => Ok(Struct(self.fold_declaration_struct_type(struct_type)?)),
            Tuple(tuple_type) => Ok(Tuple(self.fold_declaration_tuple_type(tuple_type)?)),
            t => Ok(t),
        }
    }

    fn fold_declaration_array_type(
        &mut self,
        t: DeclarationArrayType<'ast, T>,
    ) -> Result<DeclarationArrayType<'ast, T>, Self::Error> {
        Ok(DeclarationArrayType {
            ty: Box::new(self.fold_declaration_type(*t.ty)?),
            size: Box::new(self.fold_declaration_constant(*t.size)?),
        })
    }

    fn fold_declaration_tuple_type(
        &mut self,
        t: DeclarationTupleType<'ast, T>,
    ) -> Result<DeclarationTupleType<'ast, T>, Self::Error> {
        Ok(DeclarationTupleType {
            elements: t
                .elements
                .into_iter()
                .map(|t| self.fold_declaration_type(t))
                .collect::<Result<Vec<_>, _>>()?,
        })
    }

    fn fold_declaration_struct_type(
        &mut self,
        t: DeclarationStructType<'ast, T>,
    ) -> Result<DeclarationStructType<'ast, T>, Self::Error> {
        Ok(DeclarationStructType {
            generics: t
                .generics
                .into_iter()
                .map(|g| g.map(|g| self.fold_declaration_constant(g)).transpose())
                .collect::<Result<Vec<_>, _>>()?,
            members: t
                .members
                .into_iter()
                .map(|m| {
                    let id = m.id;
                    self.fold_declaration_type(*m.ty)
                        .map(|ty| DeclarationStructMember {
                            ty: Box::new(ty),
                            id,
                        })
                })
                .collect::<Result<_, _>>()?,
            ..t
        })
    }

    fn fold_assignee(
        &mut self,
        a: TypedAssignee<'ast, T>,
    ) -> Result<TypedAssignee<'ast, T>, Self::Error> {
        fold_assignee(self, a)
    }

    fn fold_assembly_block(
        &mut self,
        s: AssemblyBlockStatement<'ast, T>,
    ) -> Result<Vec<TypedStatement<'ast, T>>, Self::Error> {
        fold_assembly_block(self, s)
    }

    fn fold_assembly_assignment(
        &mut self,
        s: AssemblyAssignment<'ast, T>,
    ) -> Result<Vec<TypedAssemblyStatement<'ast, T>>, Self::Error> {
        fold_assembly_assignment(self, s)
    }

    fn fold_assembly_constraint(
        &mut self,
        s: AssemblyConstraint<'ast, T>,
    ) -> Result<Vec<TypedAssemblyStatement<'ast, T>>, Self::Error> {
        fold_assembly_constraint(self, s)
    }

    fn fold_assembly_statement(
        &mut self,
        s: TypedAssemblyStatement<'ast, T>,
    ) -> Result<Vec<TypedAssemblyStatement<'ast, T>>, Self::Error> {
        fold_assembly_statement(self, s)
    }

    fn fold_assembly_statement_cases(
        &mut self,
        s: TypedAssemblyStatement<'ast, T>,
    ) -> Result<Vec<TypedAssemblyStatement<'ast, T>>, Self::Error> {
        fold_assembly_statement_cases(self, s)
    }

    fn fold_statement(
        &mut self,
        s: TypedStatement<'ast, T>,
    ) -> Result<Vec<TypedStatement<'ast, T>>, Self::Error> {
        fold_statement(self, s)
    }

    fn fold_statement_cases(
        &mut self,
        s: TypedStatement<'ast, T>,
    ) -> Result<Vec<TypedStatement<'ast, T>>, Self::Error> {
        fold_statement_cases(self, s)
    }

    fn fold_definition_statement(
        &mut self,
        s: DefinitionStatement<'ast, T>,
    ) -> Result<Vec<TypedStatement<'ast, T>>, Self::Error> {
        fold_definition_statement(self, s)
    }

    fn fold_return_statement(
        &mut self,
        s: ReturnStatement<'ast, T>,
    ) -> Result<Vec<TypedStatement<'ast, T>>, Self::Error> {
        fold_return_statement(self, s)
    }

    fn fold_assertion_statement(
        &mut self,
        s: AssertionStatement<'ast, T>,
    ) -> Result<Vec<TypedStatement<'ast, T>>, Self::Error> {
        fold_assertion_statement(self, s)
    }

    fn fold_log_statement(
        &mut self,
        s: LogStatement<'ast, T>,
    ) -> Result<Vec<TypedStatement<'ast, T>>, Self::Error> {
        fold_log_statement(self, s)
    }

    fn fold_for_statement(
        &mut self,
        s: ForStatement<'ast, T>,
    ) -> Result<Vec<TypedStatement<'ast, T>>, Self::Error> {
        fold_for_statement(self, s)
    }

    fn fold_definition_rhs(
        &mut self,
        rhs: DefinitionRhs<'ast, T>,
    ) -> Result<DefinitionRhs<'ast, T>, Self::Error> {
        fold_definition_rhs(self, rhs)
    }

    fn fold_embed_call(
        &mut self,
        e: EmbedCall<'ast, T>,
    ) -> Result<EmbedCall<'ast, T>, Self::Error> {
        fold_embed_call(self, e)
    }

    fn fold_expression_or_spread(
        &mut self,
        e: TypedExpressionOrSpread<'ast, T>,
    ) -> Result<TypedExpressionOrSpread<'ast, T>, Self::Error> {
        Ok(match e {
            TypedExpressionOrSpread::Expression(e) => {
                TypedExpressionOrSpread::Expression(self.fold_expression(e)?)
            }
            TypedExpressionOrSpread::Spread(s) => {
                TypedExpressionOrSpread::Spread(self.fold_spread(s)?)
            }
        })
    }

    fn fold_spread(
        &mut self,
        s: TypedSpread<'ast, T>,
    ) -> Result<TypedSpread<'ast, T>, Self::Error> {
        Ok(TypedSpread {
            array: self.fold_array_expression(s.array)?,
        })
    }

    fn fold_expression(
        &mut self,
        e: TypedExpression<'ast, T>,
    ) -> Result<TypedExpression<'ast, T>, Self::Error> {
        fold_expression(self, e)
    }

    fn fold_array_expression(
        &mut self,
        e: ArrayExpression<'ast, T>,
    ) -> Result<ArrayExpression<'ast, T>, Self::Error> {
        fold_array_expression(self, e)
    }

    fn fold_struct_expression(
        &mut self,
        e: StructExpression<'ast, T>,
    ) -> Result<StructExpression<'ast, T>, Self::Error> {
        fold_struct_expression(self, e)
    }

    fn fold_tuple_expression(
        &mut self,
        e: TupleExpression<'ast, T>,
    ) -> Result<TupleExpression<'ast, T>, Self::Error> {
        fold_tuple_expression(self, e)
    }

    fn fold_int_expression(
        &mut self,
        e: IntExpression<'ast, T>,
    ) -> Result<IntExpression<'ast, T>, Self::Error> {
        fold_int_expression(self, e)
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> Result<FieldElementExpression<'ast, T>, Self::Error> {
        fold_field_expression(self, e)
    }

    fn fold_field_expression_cases(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> Result<FieldElementExpression<'ast, T>, Self::Error> {
        fold_field_expression_cases(self, e)
    }

    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> Result<BooleanExpression<'ast, T>, Self::Error> {
        fold_boolean_expression(self, e)
    }

    fn fold_boolean_expression_cases(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> Result<BooleanExpression<'ast, T>, Self::Error> {
        fold_boolean_expression_cases(self, e)
    }

    fn fold_uint_expression(
        &mut self,
        e: UExpression<'ast, T>,
    ) -> Result<UExpression<'ast, T>, Self::Error> {
        fold_uint_expression(self, e)
    }

    fn fold_uint_expression_inner(
        &mut self,
        bitwidth: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> Result<UExpressionInner<'ast, T>, Self::Error> {
        fold_uint_expression_inner(self, bitwidth, e)
    }

    fn fold_uint_expression_cases(
        &mut self,
        bitwidth: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> Result<UExpressionInner<'ast, T>, Self::Error> {
        fold_uint_expression_cases(self, bitwidth, e)
    }

    fn fold_array_expression_inner(
        &mut self,
        ty: &ArrayType<'ast, T>,
        e: ArrayExpressionInner<'ast, T>,
    ) -> Result<ArrayExpressionInner<'ast, T>, Self::Error> {
        fold_array_expression_inner(self, ty, e)
    }

    fn fold_array_expression_cases(
        &mut self,
        ty: &ArrayType<'ast, T>,
        e: ArrayExpressionInner<'ast, T>,
    ) -> Result<ArrayExpressionInner<'ast, T>, Self::Error> {
        fold_array_expression_cases(self, ty, e)
    }

    fn fold_struct_expression_inner(
        &mut self,
        ty: &StructType<'ast, T>,
        e: StructExpressionInner<'ast, T>,
    ) -> Result<StructExpressionInner<'ast, T>, Self::Error> {
        fold_struct_expression_inner(self, ty, e)
    }

    fn fold_struct_expression_cases(
        &mut self,
        ty: &StructType<'ast, T>,
        e: StructExpressionInner<'ast, T>,
    ) -> Result<StructExpressionInner<'ast, T>, Self::Error> {
        fold_struct_expression_cases(self, ty, e)
    }

    fn fold_tuple_expression_inner(
        &mut self,
        ty: &TupleType<'ast, T>,
        e: TupleExpressionInner<'ast, T>,
    ) -> Result<TupleExpressionInner<'ast, T>, Self::Error> {
        fold_tuple_expression_inner(self, ty, e)
    }

    fn fold_tuple_expression_cases(
        &mut self,
        ty: &TupleType<'ast, T>,
        e: TupleExpressionInner<'ast, T>,
    ) -> Result<TupleExpressionInner<'ast, T>, Self::Error> {
        fold_tuple_expression_cases(self, ty, e)
    }

    fn fold_struct_value_expression(
        &mut self,
        ty: &StructType<'ast, T>,
        v: StructValueExpression<'ast, T>,
    ) -> Result<
        ValueOrExpression<StructValueExpression<'ast, T>, StructExpressionInner<'ast, T>>,
        Self::Error,
    > {
        fold_struct_value_expression(self, ty, v)
    }

    fn fold_array_value_expression(
        &mut self,
        ty: &ArrayType<'ast, T>,
        v: ArrayValueExpression<'ast, T>,
    ) -> Result<
        ValueOrExpression<ArrayValueExpression<'ast, T>, ArrayExpressionInner<'ast, T>>,
        Self::Error,
    > {
        fold_array_value_expression(self, ty, v)
    }

    fn fold_tuple_value_expression(
        &mut self,
        ty: &TupleType<'ast, T>,
        v: TupleValueExpression<'ast, T>,
    ) -> Result<
        ValueOrExpression<TupleValueExpression<'ast, T>, TupleExpressionInner<'ast, T>>,
        Self::Error,
    > {
        fold_tuple_value_expression(self, ty, v)
    }
}

pub fn fold_statement_cases<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    s: TypedStatement<'ast, T>,
) -> Result<Vec<TypedStatement<'ast, T>>, F::Error> {
    match s {
        TypedStatement::Return(s) => f.fold_return_statement(s),
        TypedStatement::Definition(s) => f.fold_definition_statement(s),
        TypedStatement::Assertion(s) => f.fold_assertion_statement(s),
        TypedStatement::For(s) => f.fold_for_statement(s),
        TypedStatement::Log(s) => f.fold_log_statement(s),
        TypedStatement::Assembly(s) => f.fold_assembly_block(s),
    }
}

pub fn fold_assembly_block<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    s: AssemblyBlockStatement<'ast, T>,
) -> Result<Vec<TypedStatement<'ast, T>>, F::Error> {
    Ok(vec![TypedStatement::Assembly(AssemblyBlockStatement::new(
        s.inner
            .into_iter()
            .map(|s| f.fold_assembly_statement(s))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect(),
    ))])
}

pub fn fold_assembly_assignment<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    s: AssemblyAssignment<'ast, T>,
) -> Result<Vec<TypedAssemblyStatement<'ast, T>>, F::Error> {
    let assignee = f.fold_assignee(s.assignee)?;
    let expression = f.fold_expression(s.expression)?;
    Ok(vec![TypedAssemblyStatement::assignment(
        assignee, expression,
    )])
}

pub fn fold_assembly_constraint<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    s: AssemblyConstraint<'ast, T>,
) -> Result<Vec<TypedAssemblyStatement<'ast, T>>, F::Error> {
    let left = f.fold_field_expression(s.left)?;
    let right = f.fold_field_expression(s.right)?;
    Ok(vec![TypedAssemblyStatement::constraint(
        left, right, s.metadata,
    )])
}

fn fold_assembly_statement<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    s: TypedAssemblyStatement<'ast, T>,
) -> Result<Vec<TypedAssemblyStatement<'ast, T>>, F::Error> {
    let span = s.get_span();
    f.fold_assembly_statement_cases(s)
        .map(|s| s.into_iter().map(|s| s.span(span)).collect())
}

pub fn fold_assembly_statement_cases<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    s: TypedAssemblyStatement<'ast, T>,
) -> Result<Vec<TypedAssemblyStatement<'ast, T>>, F::Error> {
    match s {
        TypedAssemblyStatement::Assignment(s) => f.fold_assembly_assignment(s),
        TypedAssemblyStatement::Constraint(s) => f.fold_assembly_constraint(s),
    }
}

pub fn fold_statement<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    s: TypedStatement<'ast, T>,
) -> Result<Vec<TypedStatement<'ast, T>>, F::Error> {
    let span = s.get_span();
    f.fold_statement_cases(s)
        .map(|s| s.into_iter().map(|s| s.span(span)).collect())
}

pub fn fold_return_statement<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    s: ReturnStatement<'ast, T>,
) -> Result<Vec<TypedStatement<'ast, T>>, F::Error> {
    Ok(vec![TypedStatement::Return(ReturnStatement::new(
        f.fold_expression(s.inner)?,
    ))])
}

pub fn fold_definition_statement<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    s: DefinitionStatement<'ast, T>,
) -> Result<Vec<TypedStatement<'ast, T>>, F::Error> {
    let rhs = f.fold_definition_rhs(s.rhs)?;
    Ok(vec![TypedStatement::Definition(DefinitionStatement::new(
        f.fold_assignee(s.assignee)?,
        rhs,
    ))])
}

pub fn fold_assertion_statement<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    s: AssertionStatement<'ast, T>,
) -> Result<Vec<TypedStatement<'ast, T>>, F::Error> {
    Ok(vec![TypedStatement::Assertion(
        AssertionStatement::new(f.fold_boolean_expression(s.expression)?, s.error).span(s.span),
    )])
}

pub fn fold_for_statement<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    s: ForStatement<'ast, T>,
) -> Result<Vec<TypedStatement<'ast, T>>, F::Error> {
    Ok(vec![TypedStatement::For(ForStatement::new(
        f.fold_variable(s.var)?,
        f.fold_uint_expression(s.from)?,
        f.fold_uint_expression(s.to)?,
        s.statements
            .into_iter()
            .map(|s| f.fold_statement(s))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect(),
    ))])
}

pub fn fold_log_statement<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    s: LogStatement<'ast, T>,
) -> Result<Vec<TypedStatement<'ast, T>>, F::Error> {
    Ok(vec![TypedStatement::Log(LogStatement::new(
        s.format_string,
        s.expressions
            .into_iter()
            .map(|e| f.fold_expression(e))
            .collect::<Result<_, _>>()?,
    ))])
}

pub fn fold_definition_rhs<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    rhs: DefinitionRhs<'ast, T>,
) -> Result<DefinitionRhs<'ast, T>, F::Error> {
    Ok(match rhs {
        DefinitionRhs::EmbedCall(c) => DefinitionRhs::EmbedCall(f.fold_embed_call(c)?),
        DefinitionRhs::Expression(e) => DefinitionRhs::Expression(f.fold_expression(e)?),
    })
}

pub fn fold_embed_call<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    e: EmbedCall<'ast, T>,
) -> Result<EmbedCall<'ast, T>, F::Error> {
    Ok(EmbedCall {
        arguments: e
            .arguments
            .into_iter()
            .map(|s| f.fold_expression(s))
            .collect::<Result<Vec<_>, _>>()?,
        ..e
    })
}

fn fold_array_expression_inner<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    ty: &ArrayType<'ast, T>,
    e: ArrayExpressionInner<'ast, T>,
) -> Result<ArrayExpressionInner<'ast, T>, F::Error> {
    let span = e.get_span();
    f.fold_array_expression_cases(ty, e).map(|e| e.span(span))
}

pub fn fold_array_expression_cases<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    ty: &ArrayType<'ast, T>,
    e: ArrayExpressionInner<'ast, T>,
) -> Result<ArrayExpressionInner<'ast, T>, F::Error> {
    use ArrayExpressionInner::*;

    let e = match e {
        Block(block) => Block(f.fold_block_expression(block)?),
        Identifier(id) => match f.fold_identifier_expression(ty, id)? {
            IdentifierOrExpression::Identifier(i) => ArrayExpressionInner::Identifier(i),
            IdentifierOrExpression::Expression(u) => u,
        },
        FunctionCall(function_call) => match f.fold_function_call_expression(ty, function_call)? {
            FunctionCallOrExpression::FunctionCall(c) => FunctionCall(c),
            FunctionCallOrExpression::Expression(u) => u,
        },
        Value(value) => match f.fold_array_value_expression(ty, value)? {
            ValueOrExpression::Value(c) => Value(c),
            ValueOrExpression::Expression(u) => u,
        },
        Conditional(c) => match f.fold_conditional_expression(ty, c)? {
            ConditionalOrExpression::Conditional(c) => Conditional(c),
            ConditionalOrExpression::Expression(u) => u,
        },
        Member(m) => match f.fold_member_expression(ty, m)? {
            MemberOrExpression::Member(m) => Member(m),
            MemberOrExpression::Expression(u) => u,
        },
        Select(select) => match f.fold_select_expression(ty, select)? {
            SelectOrExpression::Select(m) => Select(m),
            SelectOrExpression::Expression(u) => u,
        },
        Slice(s) => match f.fold_slice_expression(s)? {
            SliceOrExpression::Slice(m) => Slice(m),
            SliceOrExpression::Expression(u) => u,
        },
        Repeat(s) => match f.fold_repeat_expression(s)? {
            RepeatOrExpression::Repeat(m) => Repeat(m),
            RepeatOrExpression::Expression(u) => u,
        },
        Element(element) => match f.fold_element_expression(ty, element)? {
            ElementOrExpression::Element(m) => Element(m),
            ElementOrExpression::Expression(u) => u,
        },
    };
    Ok(e)
}

pub fn fold_assignee<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    a: TypedAssignee<'ast, T>,
) -> Result<TypedAssignee<'ast, T>, F::Error> {
    match a {
        TypedAssignee::Identifier(v) => Ok(TypedAssignee::Identifier(f.fold_variable(v)?)),
        TypedAssignee::Select(a, index) => Ok(TypedAssignee::Select(
            Box::new(f.fold_assignee(*a)?),
            Box::new(f.fold_uint_expression(*index)?),
        )),
        TypedAssignee::Member(s, m) => Ok(TypedAssignee::Member(Box::new(f.fold_assignee(*s)?), m)),
        TypedAssignee::Element(s, index) => Ok(TypedAssignee::Element(
            Box::new(f.fold_assignee(*s)?),
            index,
        )),
    }
}

pub fn fold_struct_value_expression<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    _: &StructType<'ast, T>,
    a: StructValueExpression<'ast, T>,
) -> Result<
    ValueOrExpression<StructValueExpression<'ast, T>, StructExpressionInner<'ast, T>>,
    F::Error,
> {
    Ok(ValueOrExpression::Value(StructValueExpression {
        value: a
            .value
            .into_iter()
            .map(|v| f.fold_expression(v))
            .collect::<Result<Vec<_>, _>>()?,
        ..a
    }))
}

pub fn fold_array_value_expression<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    _: &ArrayType<'ast, T>,
    a: ArrayValueExpression<'ast, T>,
) -> Result<ValueOrExpression<ArrayValueExpression<'ast, T>, ArrayExpressionInner<'ast, T>>, F::Error>
{
    Ok(ValueOrExpression::Value(ArrayValueExpression {
        value: a
            .value
            .into_iter()
            .map(|v| f.fold_expression_or_spread(v))
            .collect::<Result<Vec<_>, _>>()?,
        ..a
    }))
}

pub fn fold_tuple_value_expression<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    _: &TupleType<'ast, T>,
    a: TupleValueExpression<'ast, T>,
) -> Result<ValueOrExpression<TupleValueExpression<'ast, T>, TupleExpressionInner<'ast, T>>, F::Error>
{
    Ok(ValueOrExpression::Value(TupleValueExpression {
        value: a
            .value
            .into_iter()
            .map(|v| f.fold_expression(v))
            .collect::<Result<Vec<_>, _>>()?,
        ..a
    }))
}

fn fold_struct_expression_inner<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    ty: &StructType<'ast, T>,
    e: StructExpressionInner<'ast, T>,
) -> Result<StructExpressionInner<'ast, T>, F::Error> {
    let span = e.get_span();
    f.fold_struct_expression_cases(ty, e).map(|e| e.span(span))
}

pub fn fold_struct_expression_cases<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    ty: &StructType<'ast, T>,
    e: StructExpressionInner<'ast, T>,
) -> Result<StructExpressionInner<'ast, T>, F::Error> {
    use StructExpressionInner::*;

    let e = match e {
        Identifier(id) => match f.fold_identifier_expression(ty, id)? {
            IdentifierOrExpression::Identifier(i) => Identifier(i),
            IdentifierOrExpression::Expression(u) => u,
        },
        Block(block) => Block(f.fold_block_expression(block)?),
        Value(value) => match f.fold_struct_value_expression(ty, value)? {
            ValueOrExpression::Value(c) => Value(c),
            ValueOrExpression::Expression(u) => u,
        },
        FunctionCall(function_call) => match f.fold_function_call_expression(ty, function_call)? {
            FunctionCallOrExpression::FunctionCall(c) => FunctionCall(c),
            FunctionCallOrExpression::Expression(u) => u,
        },
        Conditional(c) => match f.fold_conditional_expression(ty, c)? {
            ConditionalOrExpression::Conditional(c) => Conditional(c),
            ConditionalOrExpression::Expression(u) => u,
        },
        Member(m) => match f.fold_member_expression(ty, m)? {
            MemberOrExpression::Member(m) => Member(m),
            MemberOrExpression::Expression(u) => u,
        },
        Select(select) => match f.fold_select_expression(ty, select)? {
            SelectOrExpression::Select(m) => Select(m),
            SelectOrExpression::Expression(u) => u,
        },
        Element(element) => match f.fold_element_expression(ty, element)? {
            ElementOrExpression::Element(m) => Element(m),
            ElementOrExpression::Expression(u) => u,
        },
    };
    Ok(e)
}

fn fold_tuple_expression_inner<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    ty: &TupleType<'ast, T>,
    e: TupleExpressionInner<'ast, T>,
) -> Result<TupleExpressionInner<'ast, T>, F::Error> {
    let span = e.get_span();
    f.fold_tuple_expression_cases(ty, e).map(|e| e.span(span))
}

pub fn fold_tuple_expression_cases<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    ty: &TupleType<'ast, T>,
    e: TupleExpressionInner<'ast, T>,
) -> Result<TupleExpressionInner<'ast, T>, F::Error> {
    use TupleExpressionInner::*;

    let e = match e {
        Block(block) => Block(f.fold_block_expression(block)?),
        Identifier(id) => match f.fold_identifier_expression(ty, id)? {
            IdentifierOrExpression::Identifier(i) => Identifier(i),
            IdentifierOrExpression::Expression(u) => u,
        },
        Value(value) => match f.fold_tuple_value_expression(ty, value)? {
            ValueOrExpression::Value(c) => Value(c),
            ValueOrExpression::Expression(u) => u,
        },
        FunctionCall(function_call) => match f.fold_function_call_expression(ty, function_call)? {
            FunctionCallOrExpression::FunctionCall(c) => FunctionCall(c),
            FunctionCallOrExpression::Expression(u) => u,
        },
        Conditional(c) => match f.fold_conditional_expression(ty, c)? {
            ConditionalOrExpression::Conditional(c) => Conditional(c),
            ConditionalOrExpression::Expression(u) => u,
        },
        Member(m) => match f.fold_member_expression(ty, m)? {
            MemberOrExpression::Member(m) => Member(m),
            MemberOrExpression::Expression(u) => u,
        },
        Select(select) => match f.fold_select_expression(ty, select)? {
            SelectOrExpression::Select(m) => Select(m),
            SelectOrExpression::Expression(u) => u,
        },
        Element(element) => match f.fold_element_expression(ty, element)? {
            ElementOrExpression::Element(m) => Element(m),
            ElementOrExpression::Expression(u) => u,
        },
    };
    Ok(e)
}

fn fold_field_expression<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    e: FieldElementExpression<'ast, T>,
) -> Result<FieldElementExpression<'ast, T>, F::Error> {
    let span = e.get_span();
    f.fold_field_expression_cases(e).map(|e| e.span(span))
}

pub fn fold_field_expression_cases<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    e: FieldElementExpression<'ast, T>,
) -> Result<FieldElementExpression<'ast, T>, F::Error> {
    use FieldElementExpression::*;

    let e = match e {
        Identifier(id) => match f.fold_identifier_expression(&Type::FieldElement, id)? {
            IdentifierOrExpression::Identifier(i) => Identifier(i),
            IdentifierOrExpression::Expression(u) => u,
        },
        Block(block) => Block(f.fold_block_expression(block)?),
        Value(n) => Value(n),
        Add(e) => match f.fold_binary_expression(&Type::FieldElement, e)? {
            BinaryOrExpression::Binary(e) => Add(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Sub(e) => match f.fold_binary_expression(&Type::FieldElement, e)? {
            BinaryOrExpression::Binary(e) => Sub(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Mult(e) => match f.fold_binary_expression(&Type::FieldElement, e)? {
            BinaryOrExpression::Binary(e) => Mult(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Div(e) => match f.fold_binary_expression(&Type::FieldElement, e)? {
            BinaryOrExpression::Binary(e) => Div(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Pow(e) => match f.fold_binary_expression(&Type::FieldElement, e)? {
            BinaryOrExpression::Binary(e) => Pow(e),
            BinaryOrExpression::Expression(u) => u,
        },
        And(e) => match f.fold_binary_expression(&Type::FieldElement, e)? {
            BinaryOrExpression::Binary(e) => And(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Or(e) => match f.fold_binary_expression(&Type::FieldElement, e)? {
            BinaryOrExpression::Binary(e) => Or(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Xor(e) => match f.fold_binary_expression(&Type::FieldElement, e)? {
            BinaryOrExpression::Binary(e) => Xor(e),
            BinaryOrExpression::Expression(u) => u,
        },
        LeftShift(e) => match f.fold_binary_expression(&Type::FieldElement, e)? {
            BinaryOrExpression::Binary(e) => LeftShift(e),
            BinaryOrExpression::Expression(u) => u,
        },
        RightShift(e) => match f.fold_binary_expression(&Type::FieldElement, e)? {
            BinaryOrExpression::Binary(e) => RightShift(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Neg(e) => match f.fold_unary_expression(&Type::FieldElement, e)? {
            UnaryOrExpression::Unary(e) => Neg(e),
            UnaryOrExpression::Expression(u) => u,
        },
        Pos(e) => match f.fold_unary_expression(&Type::FieldElement, e)? {
            UnaryOrExpression::Unary(e) => Pos(e),
            UnaryOrExpression::Expression(u) => u,
        },
        Conditional(c) => match f.fold_conditional_expression(&Type::FieldElement, c)? {
            ConditionalOrExpression::Conditional(c) => Conditional(c),
            ConditionalOrExpression::Expression(u) => u,
        },
        FunctionCall(function_call) => {
            match f.fold_function_call_expression(&Type::FieldElement, function_call)? {
                FunctionCallOrExpression::FunctionCall(c) => FunctionCall(c),
                FunctionCallOrExpression::Expression(u) => u,
            }
        }
        Member(m) => match f.fold_member_expression(&Type::FieldElement, m)? {
            MemberOrExpression::Member(m) => Member(m),
            MemberOrExpression::Expression(u) => u,
        },
        Select(select) => match f.fold_select_expression(&Type::FieldElement, select)? {
            SelectOrExpression::Select(s) => Select(s),
            SelectOrExpression::Expression(u) => u,
        },
        Element(element) => match f.fold_element_expression(&Type::FieldElement, element)? {
            ElementOrExpression::Element(m) => Element(m),
            ElementOrExpression::Expression(u) => u,
        },
    };
    Ok(e)
}

pub fn fold_int_expression<'ast, T: Field, F: ResultFolder<'ast, T>>(
    _: &mut F,
    _: IntExpression<'ast, T>,
) -> Result<IntExpression<'ast, T>, F::Error> {
    unreachable!()
}

pub fn fold_block_expression<
    'ast,
    T: Field,
    E: ResultFold<F, F::Error>,
    F: ResultFolder<'ast, T>,
>(
    f: &mut F,
    block: BlockExpression<'ast, T, E>,
) -> Result<BlockExpression<'ast, T, E>, F::Error> {
    Ok(BlockExpression::new(
        block
            .statements
            .into_iter()
            .map(|s| f.fold_statement(s))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect(),
        block.value.fold(f)?,
    )
    .span(block.span))
}

pub fn fold_conditional_expression<
    'ast,
    T: Field,
    E: Expr<'ast, T>
        + Conditional<'ast, T>
        + PartialEq
        + ResultFold<F, F::Error>
        + From<TypedExpression<'ast, T>>,
    F: ResultFolder<'ast, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: ConditionalExpression<'ast, T, E>,
) -> Result<ConditionalOrExpression<'ast, T, E>, F::Error> {
    Ok(ConditionalOrExpression::Conditional(
        ConditionalExpression::new(
            f.fold_boolean_expression(*e.condition)?,
            e.consequence.fold(f)?,
            e.alternative.fold(f)?,
            e.kind,
        )
        .span(e.span),
    ))
}

#[allow(clippy::type_complexity)]
pub fn fold_binary_expression<
    'ast,
    T: Field,
    L: Expr<'ast, T> + PartialEq + ResultFold<F, F::Error> + From<TypedExpression<'ast, T>>,
    R: Expr<'ast, T> + PartialEq + ResultFold<F, F::Error> + From<TypedExpression<'ast, T>>,
    E: Expr<'ast, T> + PartialEq + ResultFold<F, F::Error> + From<TypedExpression<'ast, T>>,
    F: ResultFolder<'ast, T>,
    Op: OperatorStr,
>(
    f: &mut F,
    _: &E::Ty,
    e: BinaryExpression<Op, L, R, E>,
) -> Result<BinaryOrExpression<Op, L, R, E, E::Inner>, F::Error> {
    Ok(BinaryOrExpression::Binary(
        BinaryExpression::new(e.left.fold(f)?, e.right.fold(f)?).span(e.span),
    ))
}

pub fn fold_unary_expression<
    'ast,
    T: Field,
    In: Expr<'ast, T> + PartialEq + ResultFold<F, F::Error> + From<TypedExpression<'ast, T>>,
    E: Expr<'ast, T> + PartialEq + ResultFold<F, F::Error> + From<TypedExpression<'ast, T>>,
    F: ResultFolder<'ast, T>,
    Op,
>(
    f: &mut F,
    _: &E::Ty,
    e: UnaryExpression<Op, In, E>,
) -> Result<UnaryOrExpression<Op, In, E, E::Inner>, F::Error> {
    Ok(UnaryOrExpression::Unary(
        UnaryExpression::new(e.inner.fold(f)?).span(e.span),
    ))
}

pub fn fold_member_expression<
    'ast,
    T: Field,
    E: Expr<'ast, T> + Member<'ast, T> + From<TypedExpression<'ast, T>>,
    F: ResultFolder<'ast, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: MemberExpression<'ast, T, E>,
) -> Result<MemberOrExpression<'ast, T, E>, F::Error> {
    Ok(MemberOrExpression::Member(
        MemberExpression::new(f.fold_struct_expression(*e.struc)?, e.id).span(e.span),
    ))
}

pub fn fold_slice_expression<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    e: SliceExpression<'ast, T>,
) -> Result<SliceOrExpression<'ast, T>, F::Error> {
    Ok(SliceOrExpression::Slice(SliceExpression::new(
        f.fold_array_expression(*e.array)?,
        f.fold_uint_expression(*e.from)?,
        f.fold_uint_expression(*e.to)?,
    )))
}

pub fn fold_repeat_expression<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    e: RepeatExpression<'ast, T>,
) -> Result<RepeatOrExpression<'ast, T>, F::Error> {
    Ok(RepeatOrExpression::Repeat(RepeatExpression::new(
        f.fold_expression(*e.e)?,
        f.fold_uint_expression(*e.count)?,
    )))
}

pub fn fold_identifier_expression<
    'ast,
    T: Field,
    E: Expr<'ast, T> + Id<'ast, T> + From<TypedExpression<'ast, T>>,
    F: ResultFolder<'ast, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: IdentifierExpression<'ast, E>,
) -> Result<IdentifierOrExpression<'ast, T, E>, F::Error> {
    Ok(IdentifierOrExpression::Identifier(
        IdentifierExpression::new(f.fold_name(e.id)?).span(e.span),
    ))
}

pub fn fold_select_expression<
    'ast,
    T: Field,
    E: Expr<'ast, T>
        + Select<'ast, T>
        + From<TypedExpression<'ast, T>>
        + Into<TypedExpression<'ast, T>>,
    F: ResultFolder<'ast, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: SelectExpression<'ast, T, E>,
) -> Result<SelectOrExpression<'ast, T, E>, F::Error> {
    Ok(SelectOrExpression::Select(
        SelectExpression::new(
            f.fold_array_expression(*e.array)?,
            f.fold_uint_expression(*e.index)?,
        )
        .span(e.span),
    ))
}

pub fn fold_element_expression<
    'ast,
    T: Field,
    E: Expr<'ast, T> + Element<'ast, T> + From<TypedExpression<'ast, T>>,
    F: ResultFolder<'ast, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: ElementExpression<'ast, T, E>,
) -> Result<ElementOrExpression<'ast, T, E>, F::Error> {
    Ok(ElementOrExpression::Element(
        ElementExpression::new(f.fold_tuple_expression(*e.tuple)?, e.index).span(e.span),
    ))
}

pub fn fold_function_call_expression<
    'ast,
    T: Field,
    E: Id<'ast, T> + From<TypedExpression<'ast, T>> + Expr<'ast, T> + FunctionCall<'ast, T>,
    F: ResultFolder<'ast, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: FunctionCallExpression<'ast, T, E>,
) -> Result<FunctionCallOrExpression<'ast, T, E>, F::Error> {
    Ok(FunctionCallOrExpression::Expression(
        E::function_call(
            f.fold_declaration_function_key(e.function_key)?,
            e.generics
                .into_iter()
                .map(|g| g.map(|g| f.fold_uint_expression(g)).transpose())
                .collect::<Result<_, _>>()?,
            e.arguments
                .into_iter()
                .map(|e| f.fold_expression(e))
                .collect::<Result<_, _>>()?,
        )
        .span(e.span),
    ))
}

fn fold_boolean_expression<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    e: BooleanExpression<'ast, T>,
) -> Result<BooleanExpression<'ast, T>, F::Error> {
    let span = e.get_span();
    f.fold_boolean_expression_cases(e).map(|e| e.span(span))
}

pub fn fold_boolean_expression_cases<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    e: BooleanExpression<'ast, T>,
) -> Result<BooleanExpression<'ast, T>, F::Error> {
    use BooleanExpression::*;

    let e = match e {
        Identifier(id) => match f.fold_identifier_expression(&Type::Boolean, id)? {
            IdentifierOrExpression::Identifier(i) => Identifier(i),
            IdentifierOrExpression::Expression(u) => u,
        },
        Block(block) => Block(f.fold_block_expression(block)?),
        Value(v) => Value(v),
        FieldEq(e) => match f.fold_eq_expression(e)? {
            BinaryOrExpression::Binary(e) => FieldEq(e),
            BinaryOrExpression::Expression(u) => u,
        },
        BoolEq(e) => match f.fold_eq_expression(e)? {
            BinaryOrExpression::Binary(e) => BoolEq(e),
            BinaryOrExpression::Expression(u) => u,
        },
        ArrayEq(e) => match f.fold_eq_expression(e)? {
            BinaryOrExpression::Binary(e) => ArrayEq(e),
            BinaryOrExpression::Expression(u) => u,
        },
        StructEq(e) => match f.fold_eq_expression(e)? {
            BinaryOrExpression::Binary(e) => StructEq(e),
            BinaryOrExpression::Expression(u) => u,
        },
        TupleEq(e) => match f.fold_eq_expression(e)? {
            BinaryOrExpression::Binary(e) => TupleEq(e),
            BinaryOrExpression::Expression(u) => u,
        },
        UintEq(e) => match f.fold_eq_expression(e)? {
            BinaryOrExpression::Binary(e) => UintEq(e),
            BinaryOrExpression::Expression(u) => u,
        },
        FieldLt(e) => match f.fold_binary_expression(&Type::Boolean, e)? {
            BinaryOrExpression::Binary(e) => FieldLt(e),
            BinaryOrExpression::Expression(u) => u,
        },
        FieldLe(e) => match f.fold_binary_expression(&Type::Boolean, e)? {
            BinaryOrExpression::Binary(e) => FieldLe(e),
            BinaryOrExpression::Expression(u) => u,
        },
        UintLt(e) => match f.fold_binary_expression(&Type::Boolean, e)? {
            BinaryOrExpression::Binary(e) => UintLt(e),
            BinaryOrExpression::Expression(u) => u,
        },
        UintLe(e) => match f.fold_binary_expression(&Type::Boolean, e)? {
            BinaryOrExpression::Binary(e) => UintLe(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Or(e) => match f.fold_binary_expression(&Type::Boolean, e)? {
            BinaryOrExpression::Binary(e) => Or(e),
            BinaryOrExpression::Expression(u) => u,
        },
        And(e) => match f.fold_binary_expression(&Type::Boolean, e)? {
            BinaryOrExpression::Binary(e) => And(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Not(e) => match f.fold_unary_expression(&Type::Boolean, e)? {
            UnaryOrExpression::Unary(e) => Not(e),
            UnaryOrExpression::Expression(u) => u,
        },
        FunctionCall(function_call) => {
            match f.fold_function_call_expression(&Type::Boolean, function_call)? {
                FunctionCallOrExpression::FunctionCall(c) => FunctionCall(c),
                FunctionCallOrExpression::Expression(u) => u,
            }
        }
        Conditional(c) => match f.fold_conditional_expression(&Type::Boolean, c)? {
            ConditionalOrExpression::Conditional(c) => Conditional(c),
            ConditionalOrExpression::Expression(u) => u,
        },
        Select(select) => match f.fold_select_expression(&Type::Boolean, select)? {
            SelectOrExpression::Select(s) => Select(s),
            SelectOrExpression::Expression(u) => u,
        },
        Member(m) => match f.fold_member_expression(&Type::Boolean, m)? {
            MemberOrExpression::Member(m) => Member(m),
            MemberOrExpression::Expression(u) => u,
        },
        Element(element) => match f.fold_element_expression(&Type::Boolean, element)? {
            ElementOrExpression::Element(m) => Element(m),
            ElementOrExpression::Expression(u) => u,
        },
    };

    Ok(e)
}

pub fn fold_uint_expression<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    e: UExpression<'ast, T>,
) -> Result<UExpression<'ast, T>, F::Error> {
    Ok(UExpression {
        inner: f.fold_uint_expression_inner(e.bitwidth, e.inner)?,
        ..e
    })
}

fn fold_uint_expression_inner<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    ty: UBitwidth,
    e: UExpressionInner<'ast, T>,
) -> Result<UExpressionInner<'ast, T>, F::Error> {
    let span = e.get_span();
    f.fold_uint_expression_cases(ty, e).map(|e| e.span(span))
}

pub fn fold_uint_expression_cases<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    ty: UBitwidth,
    e: UExpressionInner<'ast, T>,
) -> Result<UExpressionInner<'ast, T>, F::Error> {
    use UExpressionInner::*;

    let e = match e {
        Identifier(id) => match f.fold_identifier_expression(&ty, id)? {
            IdentifierOrExpression::Identifier(i) => Identifier(i),
            IdentifierOrExpression::Expression(u) => u,
        },
        Block(block) => Block(f.fold_block_expression(block)?),
        Value(v) => Value(v),
        Add(e) => match f.fold_binary_expression(&ty, e)? {
            BinaryOrExpression::Binary(e) => Add(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Sub(e) => match f.fold_binary_expression(&ty, e)? {
            BinaryOrExpression::Binary(e) => Sub(e),
            BinaryOrExpression::Expression(u) => u,
        },
        FloorSub(e) => match f.fold_binary_expression(&ty, e)? {
            BinaryOrExpression::Binary(e) => FloorSub(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Mult(e) => match f.fold_binary_expression(&ty, e)? {
            BinaryOrExpression::Binary(e) => Mult(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Div(e) => match f.fold_binary_expression(&ty, e)? {
            BinaryOrExpression::Binary(e) => Div(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Rem(e) => match f.fold_binary_expression(&ty, e)? {
            BinaryOrExpression::Binary(e) => Rem(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Xor(e) => match f.fold_binary_expression(&ty, e)? {
            BinaryOrExpression::Binary(e) => Xor(e),
            BinaryOrExpression::Expression(u) => u,
        },
        And(e) => match f.fold_binary_expression(&ty, e)? {
            BinaryOrExpression::Binary(e) => And(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Or(e) => match f.fold_binary_expression(&ty, e)? {
            BinaryOrExpression::Binary(e) => Or(e),
            BinaryOrExpression::Expression(u) => u,
        },
        LeftShift(e) => match f.fold_binary_expression(&ty, e)? {
            BinaryOrExpression::Binary(e) => LeftShift(e),
            BinaryOrExpression::Expression(u) => u,
        },
        RightShift(e) => match f.fold_binary_expression(&ty, e)? {
            BinaryOrExpression::Binary(e) => RightShift(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Pos(e) => match f.fold_unary_expression(&ty, e)? {
            UnaryOrExpression::Unary(e) => Pos(e),
            UnaryOrExpression::Expression(u) => u,
        },
        Neg(e) => match f.fold_unary_expression(&ty, e)? {
            UnaryOrExpression::Unary(e) => Neg(e),
            UnaryOrExpression::Expression(u) => u,
        },
        Not(e) => match f.fold_unary_expression(&ty, e)? {
            UnaryOrExpression::Unary(e) => Not(e),
            UnaryOrExpression::Expression(u) => u,
        },
        FunctionCall(function_call) => {
            match f.fold_function_call_expression(&ty, function_call)? {
                FunctionCallOrExpression::FunctionCall(c) => FunctionCall(c),
                FunctionCallOrExpression::Expression(u) => u,
            }
        }
        Select(select) => match f.fold_select_expression(&ty, select)? {
            SelectOrExpression::Select(s) => Select(s),
            SelectOrExpression::Expression(u) => u,
        },
        Conditional(c) => match f.fold_conditional_expression(&ty, c)? {
            ConditionalOrExpression::Conditional(c) => Conditional(c),
            ConditionalOrExpression::Expression(u) => u,
        },
        Member(m) => match f.fold_member_expression(&ty, m)? {
            MemberOrExpression::Member(m) => Member(m),
            MemberOrExpression::Expression(u) => u,
        },
        Element(element) => match f.fold_element_expression(&ty, element)? {
            ElementOrExpression::Element(m) => Element(m),
            ElementOrExpression::Expression(u) => u,
        },
    };

    Ok(e)
}

pub fn fold_declaration_function_key<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    key: DeclarationFunctionKey<'ast, T>,
) -> Result<DeclarationFunctionKey<'ast, T>, F::Error> {
    Ok(DeclarationFunctionKey {
        module: f.fold_module_id(key.module)?,
        signature: f.fold_signature(key.signature)?,
        ..key
    })
}

pub fn fold_function<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    fun: TypedFunction<'ast, T>,
) -> Result<TypedFunction<'ast, T>, F::Error> {
    Ok(TypedFunction {
        arguments: fun
            .arguments
            .into_iter()
            .map(|a| f.fold_parameter(a))
            .collect::<Result<_, _>>()?,
        statements: fun
            .statements
            .into_iter()
            .map(|s| f.fold_statement(s))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect(),
        signature: f.fold_signature(fun.signature)?,
    })
}

pub fn fold_signature<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    s: DeclarationSignature<'ast, T>,
) -> Result<DeclarationSignature<'ast, T>, F::Error> {
    Ok(DeclarationSignature {
        generics: s
            .generics
            .into_iter()
            .map(|g| g.map(|g| f.fold_declaration_constant(g)).transpose())
            .collect::<Result<_, _>>()?,
        inputs: s
            .inputs
            .into_iter()
            .map(|o| f.fold_declaration_type(o))
            .collect::<Result<_, _>>()?,
        output: Box::new(f.fold_declaration_type(*s.output)?),
    })
}

pub fn fold_declaration_constant<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    c: DeclarationConstant<'ast, T>,
) -> Result<DeclarationConstant<'ast, T>, F::Error> {
    match c {
        DeclarationConstant::Expression(e) => {
            Ok(DeclarationConstant::Expression(f.fold_expression(e)?))
        }
        DeclarationConstant::Constant(c) => Ok(DeclarationConstant::Constant(
            f.fold_canonical_constant_identifier(c)?,
        )),
        c => Ok(c),
    }
}

pub fn fold_expression<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    e: TypedExpression<'ast, T>,
) -> Result<TypedExpression<'ast, T>, F::Error> {
    match e {
        TypedExpression::FieldElement(e) => Ok(f.fold_field_expression(e)?.into()),
        TypedExpression::Boolean(e) => Ok(f.fold_boolean_expression(e)?.into()),
        TypedExpression::Uint(e) => Ok(f.fold_uint_expression(e)?.into()),
        TypedExpression::Array(e) => Ok(f.fold_array_expression(e)?.into()),
        TypedExpression::Struct(e) => Ok(f.fold_struct_expression(e)?.into()),
        TypedExpression::Tuple(e) => Ok(f.fold_tuple_expression(e)?.into()),
        TypedExpression::Int(e) => Ok(f.fold_int_expression(e)?.into()),
    }
}

pub fn fold_array_expression<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    e: ArrayExpression<'ast, T>,
) -> Result<ArrayExpression<'ast, T>, F::Error> {
    let ty = f.fold_array_type(*e.ty)?;

    Ok(ArrayExpression {
        inner: f.fold_array_expression_inner(&ty, e.inner)?,
        ty: Box::new(ty),
    })
}

pub fn fold_struct_expression<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    e: StructExpression<'ast, T>,
) -> Result<StructExpression<'ast, T>, F::Error> {
    let ty = f.fold_struct_type(e.ty)?;
    Ok(StructExpression {
        inner: f.fold_struct_expression_inner(&ty, e.inner)?,
        ty,
    })
}

pub fn fold_tuple_expression<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    e: TupleExpression<'ast, T>,
) -> Result<TupleExpression<'ast, T>, F::Error> {
    let ty = f.fold_tuple_type(e.ty)?;
    Ok(TupleExpression {
        inner: f.fold_tuple_expression_inner(&ty, e.inner)?,
        ty,
    })
}

pub fn fold_constant<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    c: TypedConstant<'ast, T>,
) -> Result<TypedConstant<'ast, T>, F::Error> {
    Ok(TypedConstant {
        expression: f.fold_expression(c.expression)?,
        ty: f.fold_declaration_type(c.ty)?,
    })
}

pub fn fold_constant_symbol<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    s: TypedConstantSymbol<'ast, T>,
) -> Result<TypedConstantSymbol<'ast, T>, F::Error> {
    match s {
        TypedConstantSymbol::Here(tc) => Ok(TypedConstantSymbol::Here(f.fold_constant(tc)?)),
        TypedConstantSymbol::There(id) => Ok(TypedConstantSymbol::There(
            f.fold_canonical_constant_identifier(id)?,
        )),
    }
}

pub fn fold_function_symbol<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    s: TypedFunctionSymbol<'ast, T>,
) -> Result<TypedFunctionSymbol<'ast, T>, F::Error> {
    match s {
        TypedFunctionSymbol::Here(fun) => Ok(TypedFunctionSymbol::Here(f.fold_function(fun)?)),
        TypedFunctionSymbol::There(key) => Ok(TypedFunctionSymbol::There(
            f.fold_declaration_function_key(key)?,
        )),
        s => Ok(s),
    }
}

pub fn fold_symbol_declaration<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    d: TypedSymbolDeclaration<'ast, T>,
) -> Result<TypedSymbolDeclaration<'ast, T>, F::Error> {
    Ok(match d {
        TypedSymbolDeclaration::Function(d) => {
            TypedSymbolDeclaration::Function(f.fold_function_symbol_declaration(d)?)
        }
        TypedSymbolDeclaration::Constant(d) => {
            TypedSymbolDeclaration::Constant(f.fold_constant_symbol_declaration(d)?)
        }
    })
}

pub fn fold_function_symbol_declaration<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    d: TypedFunctionSymbolDeclaration<'ast, T>,
) -> Result<TypedFunctionSymbolDeclaration<'ast, T>, F::Error> {
    Ok(TypedFunctionSymbolDeclaration {
        key: f.fold_declaration_function_key(d.key)?,
        symbol: f.fold_function_symbol(d.symbol)?,
    })
}

pub fn fold_constant_symbol_declaration<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    d: TypedConstantSymbolDeclaration<'ast, T>,
) -> Result<TypedConstantSymbolDeclaration<'ast, T>, F::Error> {
    Ok(TypedConstantSymbolDeclaration {
        id: f.fold_canonical_constant_identifier(d.id)?,
        symbol: f.fold_constant_symbol(d.symbol)?,
    })
}

pub fn fold_module<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    m: TypedModule<'ast, T>,
) -> Result<TypedModule<'ast, T>, F::Error> {
    Ok(TypedModule {
        symbols: m
            .symbols
            .into_iter()
            .map(|s| f.fold_symbol_declaration(s))
            .collect::<Result<_, _>>()?,
    })
}

pub fn fold_program<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    p: TypedProgram<'ast, T>,
) -> Result<TypedProgram<'ast, T>, F::Error> {
    Ok(TypedProgram {
        main: f.fold_module_id(p.main)?,
        modules: p
            .modules
            .into_iter()
            .map(|(module_id, module)| {
                let module_id = f.fold_module_id(module_id)?;
                f.fold_module(module).map(|m| (module_id, m))
            })
            .collect::<Result<_, _>>()?,
        ..p
    })
}
