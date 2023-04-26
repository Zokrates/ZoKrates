use crate::common::expressions::{
    BooleanValueExpression, EqExpression, FieldValueExpression, IntValueExpression,
    UnaryOrExpression, ValueOrExpression,
};
// Generic walk through a typed AST. Not mutating in place
use crate::common::{expressions::BinaryOrExpression, Fold};
use crate::typed::*;
use zokrates_field::Field;

use super::identifier::FrameIdentifier;
use super::types::{DeclarationStructMember, DeclarationTupleType, StructMember};

impl<'ast, T: Field, F: Folder<'ast, T>> Fold<F> for FieldElementExpression<'ast, T> {
    fn fold(self, f: &mut F) -> Self {
        f.fold_field_expression(self)
    }
}

impl<'ast, T: Field, F: Folder<'ast, T>> Fold<F> for BooleanExpression<'ast, T> {
    fn fold(self, f: &mut F) -> Self {
        f.fold_boolean_expression(self)
    }
}

impl<'ast, T: Field, F: Folder<'ast, T>> Fold<F> for UExpression<'ast, T> {
    fn fold(self, f: &mut F) -> Self {
        f.fold_uint_expression(self)
    }
}

impl<'ast, T: Field, F: Folder<'ast, T>> Fold<F> for StructExpression<'ast, T> {
    fn fold(self, f: &mut F) -> Self {
        f.fold_struct_expression(self)
    }
}

impl<'ast, T: Field, F: Folder<'ast, T>> Fold<F> for ArrayExpression<'ast, T> {
    fn fold(self, f: &mut F) -> Self {
        f.fold_array_expression(self)
    }
}

impl<'ast, T: Field, F: Folder<'ast, T>> Fold<F> for TupleExpression<'ast, T> {
    fn fold(self, f: &mut F) -> Self {
        f.fold_tuple_expression(self)
    }
}

pub trait Folder<'ast, T: Field>: Sized {
    fn fold_program(&mut self, p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        fold_program(self, p)
    }

    fn fold_module(&mut self, m: TypedModule<'ast, T>) -> TypedModule<'ast, T> {
        fold_module(self, m)
    }

    fn fold_symbol_declaration(
        &mut self,
        s: TypedSymbolDeclaration<'ast, T>,
    ) -> TypedSymbolDeclaration<'ast, T> {
        fold_symbol_declaration(self, s)
    }

    fn fold_function_symbol_declaration(
        &mut self,
        s: TypedFunctionSymbolDeclaration<'ast, T>,
    ) -> TypedFunctionSymbolDeclaration<'ast, T> {
        fold_function_symbol_declaration(self, s)
    }

    fn fold_constant_symbol_declaration(
        &mut self,
        s: TypedConstantSymbolDeclaration<'ast, T>,
    ) -> TypedConstantSymbolDeclaration<'ast, T> {
        fold_constant_symbol_declaration(self, s)
    }

    fn fold_constant(&mut self, c: TypedConstant<'ast, T>) -> TypedConstant<'ast, T> {
        fold_constant(self, c)
    }

    fn fold_constant_symbol(
        &mut self,
        s: TypedConstantSymbol<'ast, T>,
    ) -> TypedConstantSymbol<'ast, T> {
        fold_constant_symbol(self, s)
    }

    fn fold_function_symbol(
        &mut self,
        s: TypedFunctionSymbol<'ast, T>,
    ) -> TypedFunctionSymbol<'ast, T> {
        fold_function_symbol(self, s)
    }

    fn fold_declaration_function_key(
        &mut self,
        key: DeclarationFunctionKey<'ast, T>,
    ) -> DeclarationFunctionKey<'ast, T> {
        fold_declaration_function_key(self, key)
    }

    fn fold_function(&mut self, f: TypedFunction<'ast, T>) -> TypedFunction<'ast, T> {
        fold_function(self, f)
    }

    fn fold_signature(
        &mut self,
        s: DeclarationSignature<'ast, T>,
    ) -> DeclarationSignature<'ast, T> {
        fold_signature(self, s)
    }

    fn fold_declaration_constant(
        &mut self,
        c: DeclarationConstant<'ast, T>,
    ) -> DeclarationConstant<'ast, T> {
        fold_declaration_constant(self, c)
    }

    fn fold_parameter(
        &mut self,
        p: DeclarationParameter<'ast, T>,
    ) -> DeclarationParameter<'ast, T> {
        DeclarationParameter {
            id: self.fold_declaration_variable(p.id),
            ..p
        }
    }

    fn fold_name(&mut self, n: Identifier<'ast>) -> Identifier<'ast> {
        let id = match n.id.id.clone() {
            CoreIdentifier::Constant(c) => FrameIdentifier {
                id: CoreIdentifier::Constant(self.fold_canonical_constant_identifier(c)),
                frame: 0,
            },
            _ => n.id,
        };

        Identifier { id, ..n }
    }

    fn fold_variable(&mut self, v: Variable<'ast, T>) -> Variable<'ast, T> {
        let span = v.get_span();
        Variable::new(self.fold_name(v.id), self.fold_type(v.ty)).span(span)
    }

    fn fold_declaration_variable(
        &mut self,
        v: DeclarationVariable<'ast, T>,
    ) -> DeclarationVariable<'ast, T> {
        let span = v.get_span();
        DeclarationVariable::new(self.fold_name(v.id), self.fold_declaration_type(v.ty)).span(span)
    }

    fn fold_type(&mut self, t: Type<'ast, T>) -> Type<'ast, T> {
        use self::GType::*;

        match t {
            Array(array_type) => Array(self.fold_array_type(array_type)),
            Struct(struct_type) => Struct(self.fold_struct_type(struct_type)),
            Tuple(tuple_type) => Tuple(self.fold_tuple_type(tuple_type)),
            t => t,
        }
    }

    fn fold_array_type(&mut self, t: ArrayType<'ast, T>) -> ArrayType<'ast, T> {
        ArrayType {
            ty: Box::new(self.fold_type(*t.ty)),
            size: Box::new(self.fold_uint_expression(*t.size)),
        }
    }

    fn fold_tuple_type(&mut self, t: TupleType<'ast, T>) -> TupleType<'ast, T> {
        TupleType {
            elements: t.elements.into_iter().map(|t| self.fold_type(t)).collect(),
        }
    }

    fn fold_struct_type(&mut self, t: StructType<'ast, T>) -> StructType<'ast, T> {
        StructType {
            generics: t
                .generics
                .into_iter()
                .map(|g| g.map(|g| self.fold_uint_expression(g)))
                .collect(),
            members: t
                .members
                .into_iter()
                .map(|m| StructMember {
                    ty: Box::new(self.fold_type(*m.ty)),
                    ..m
                })
                .collect(),
            ..t
        }
    }

    fn fold_declaration_type(&mut self, t: DeclarationType<'ast, T>) -> DeclarationType<'ast, T> {
        use self::GType::*;

        match t {
            Array(array_type) => Array(self.fold_declaration_array_type(array_type)),
            Struct(struct_type) => Struct(self.fold_declaration_struct_type(struct_type)),
            Tuple(tuple_type) => Tuple(self.fold_declaration_tuple_type(tuple_type)),
            t => t,
        }
    }

    fn fold_declaration_array_type(
        &mut self,
        t: DeclarationArrayType<'ast, T>,
    ) -> DeclarationArrayType<'ast, T> {
        DeclarationArrayType {
            ty: Box::new(self.fold_declaration_type(*t.ty)),
            size: Box::new(self.fold_declaration_constant(*t.size)),
        }
    }

    fn fold_declaration_tuple_type(
        &mut self,
        t: DeclarationTupleType<'ast, T>,
    ) -> DeclarationTupleType<'ast, T> {
        DeclarationTupleType {
            elements: t
                .elements
                .into_iter()
                .map(|t| self.fold_declaration_type(t))
                .collect(),
        }
    }

    fn fold_declaration_struct_type(
        &mut self,
        t: DeclarationStructType<'ast, T>,
    ) -> DeclarationStructType<'ast, T> {
        DeclarationStructType {
            generics: t
                .generics
                .into_iter()
                .map(|g| g.map(|g| self.fold_declaration_constant(g)))
                .collect(),
            members: t
                .members
                .into_iter()
                .map(|m| DeclarationStructMember {
                    ty: Box::new(self.fold_declaration_type(*m.ty)),
                    ..m
                })
                .collect(),
            ..t
        }
    }

    fn fold_assignee(&mut self, a: TypedAssignee<'ast, T>) -> TypedAssignee<'ast, T> {
        fold_assignee(self, a)
    }

    fn fold_assembly_block(
        &mut self,
        s: AssemblyBlockStatement<'ast, T>,
    ) -> Vec<TypedStatement<'ast, T>> {
        fold_assembly_block(self, s)
    }

    fn fold_assembly_assignment(
        &mut self,
        s: AssemblyAssignment<'ast, T>,
    ) -> Vec<TypedAssemblyStatement<'ast, T>> {
        fold_assembly_assignment(self, s)
    }

    fn fold_assembly_constraint(
        &mut self,
        s: AssemblyConstraint<'ast, T>,
    ) -> Vec<TypedAssemblyStatement<'ast, T>> {
        fold_assembly_constraint(self, s)
    }

    fn fold_assembly_statement(
        &mut self,
        s: TypedAssemblyStatement<'ast, T>,
    ) -> Vec<TypedAssemblyStatement<'ast, T>> {
        fold_assembly_statement(self, s)
    }

    fn fold_assembly_statement_cases(
        &mut self,
        s: TypedAssemblyStatement<'ast, T>,
    ) -> Vec<TypedAssemblyStatement<'ast, T>> {
        fold_assembly_statement_cases(self, s)
    }

    fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        fold_statement(self, s)
    }

    fn fold_statement_cases(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        fold_statement_cases(self, s)
    }

    fn fold_definition_statement(
        &mut self,
        s: DefinitionStatement<'ast, T>,
    ) -> Vec<TypedStatement<'ast, T>> {
        fold_definition_statement(self, s)
    }

    fn fold_return_statement(
        &mut self,
        s: ReturnStatement<'ast, T>,
    ) -> Vec<TypedStatement<'ast, T>> {
        fold_return_statement(self, s)
    }

    fn fold_assertion_statement(
        &mut self,
        s: AssertionStatement<'ast, T>,
    ) -> Vec<TypedStatement<'ast, T>> {
        fold_assertion_statement(self, s)
    }

    fn fold_log_statement(&mut self, s: LogStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        fold_log_statement(self, s)
    }

    fn fold_for_statement(&mut self, s: ForStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        fold_for_statement(self, s)
    }

    fn fold_definition_rhs(&mut self, rhs: DefinitionRhs<'ast, T>) -> DefinitionRhs<'ast, T> {
        fold_definition_rhs(self, rhs)
    }

    fn fold_embed_call(&mut self, e: EmbedCall<'ast, T>) -> EmbedCall<'ast, T> {
        fold_embed_call(self, e)
    }

    fn fold_expression_or_spread(
        &mut self,
        e: TypedExpressionOrSpread<'ast, T>,
    ) -> TypedExpressionOrSpread<'ast, T> {
        match e {
            TypedExpressionOrSpread::Expression(e) => {
                TypedExpressionOrSpread::Expression(self.fold_expression(e))
            }
            TypedExpressionOrSpread::Spread(s) => {
                TypedExpressionOrSpread::Spread(self.fold_spread(s))
            }
        }
    }

    fn fold_spread(&mut self, s: TypedSpread<'ast, T>) -> TypedSpread<'ast, T> {
        TypedSpread {
            array: self.fold_array_expression(s.array),
        }
    }

    fn fold_canonical_constant_identifier(
        &mut self,
        i: CanonicalConstantIdentifier<'ast>,
    ) -> CanonicalConstantIdentifier<'ast> {
        CanonicalConstantIdentifier {
            module: self.fold_module_id(i.module),
            id: i.id,
        }
    }

    fn fold_module_id(&mut self, i: OwnedModuleId) -> OwnedModuleId {
        i
    }

    fn fold_expression(&mut self, e: TypedExpression<'ast, T>) -> TypedExpression<'ast, T> {
        fold_expression(self, e)
    }

    fn fold_block_expression<E: Fold<Self>>(
        &mut self,
        block: BlockExpression<'ast, T, E>,
    ) -> BlockExpression<'ast, T, E> {
        fold_block_expression(self, block)
    }

    fn fold_conditional_expression<
        E: Expr<'ast, T>
            + Fold<Self>
            + Block<'ast, T>
            + Conditional<'ast, T>
            + From<TypedExpression<'ast, T>>,
    >(
        &mut self,
        ty: &E::Ty,
        e: ConditionalExpression<'ast, T, E>,
    ) -> ConditionalOrExpression<'ast, T, E> {
        fold_conditional_expression(self, ty, e)
    }

    fn fold_binary_expression<
        L: Expr<'ast, T> + Fold<Self>,
        R: Expr<'ast, T> + Fold<Self>,
        E: Expr<'ast, T> + Fold<Self>,
        Op,
    >(
        &mut self,
        ty: &E::Ty,
        e: BinaryExpression<Op, L, R, E>,
    ) -> BinaryOrExpression<Op, L, R, E, E::Inner> {
        fold_binary_expression(self, ty, e)
    }

    fn fold_eq_expression<E: Expr<'ast, T> + Fold<Self>>(
        &mut self,
        e: EqExpression<E, BooleanExpression<'ast, T>>,
    ) -> BinaryOrExpression<OpEq, E, E, BooleanExpression<'ast, T>, BooleanExpression<'ast, T>>
    {
        fold_binary_expression(self, &Type::Boolean, e)
    }

    fn fold_unary_expression<In: Expr<'ast, T> + Fold<Self>, E: Expr<'ast, T> + Fold<Self>, Op>(
        &mut self,
        ty: &E::Ty,
        e: UnaryExpression<Op, In, E>,
    ) -> UnaryOrExpression<Op, In, E, E::Inner> {
        fold_unary_expression(self, ty, e)
    }

    fn fold_member_expression<
        E: Expr<'ast, T> + Member<'ast, T> + From<TypedExpression<'ast, T>>,
    >(
        &mut self,
        ty: &E::Ty,
        e: MemberExpression<'ast, T, E>,
    ) -> MemberOrExpression<'ast, T, E> {
        fold_member_expression(self, ty, e)
    }

    fn fold_slice_expression(&mut self, e: SliceExpression<'ast, T>) -> SliceOrExpression<'ast, T> {
        fold_slice_expression(self, e)
    }

    fn fold_repeat_expression(
        &mut self,
        e: RepeatExpression<'ast, T>,
    ) -> RepeatOrExpression<'ast, T> {
        fold_repeat_expression(self, e)
    }

    fn fold_identifier_expression<
        E: Expr<'ast, T> + Id<'ast, T> + From<TypedExpression<'ast, T>>,
    >(
        &mut self,
        ty: &E::Ty,
        e: IdentifierExpression<'ast, E>,
    ) -> IdentifierOrExpression<'ast, T, E> {
        fold_identifier_expression(self, ty, e)
    }

    fn fold_element_expression<
        E: Expr<'ast, T> + Element<'ast, T> + From<TypedExpression<'ast, T>>,
    >(
        &mut self,
        ty: &E::Ty,
        e: ElementExpression<'ast, T, E>,
    ) -> ElementOrExpression<'ast, T, E> {
        fold_element_expression(self, ty, e)
    }

    fn fold_function_call_expression<
        E: Id<'ast, T> + From<TypedExpression<'ast, T>> + Expr<'ast, T> + FunctionCall<'ast, T>,
    >(
        &mut self,
        ty: &E::Ty,
        e: FunctionCallExpression<'ast, T, E>,
    ) -> FunctionCallOrExpression<'ast, T, E> {
        fold_function_call_expression(self, ty, e)
    }

    fn fold_select_expression<
        E: Expr<'ast, T> + Select<'ast, T> + Conditional<'ast, T> + From<TypedExpression<'ast, T>>,
    >(
        &mut self,
        ty: &E::Ty,
        e: SelectExpression<'ast, T, E>,
    ) -> SelectOrExpression<'ast, T, E> {
        fold_select_expression(self, ty, e)
    }

    fn fold_array_expression(&mut self, e: ArrayExpression<'ast, T>) -> ArrayExpression<'ast, T> {
        fold_array_expression(self, e)
    }

    fn fold_struct_expression(
        &mut self,
        e: StructExpression<'ast, T>,
    ) -> StructExpression<'ast, T> {
        fold_struct_expression(self, e)
    }

    fn fold_tuple_expression(&mut self, e: TupleExpression<'ast, T>) -> TupleExpression<'ast, T> {
        fold_tuple_expression(self, e)
    }

    fn fold_int_expression(&mut self, e: IntExpression<'ast, T>) -> IntExpression<'ast, T> {
        fold_int_expression(self, e)
    }

    fn fold_field_expression_cases(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> FieldElementExpression<'ast, T> {
        fold_field_expression_cases(self, e)
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> FieldElementExpression<'ast, T> {
        fold_field_expression(self, e)
    }

    fn fold_boolean_expression_cases(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> BooleanExpression<'ast, T> {
        fold_boolean_expression_cases(self, e)
    }

    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> BooleanExpression<'ast, T> {
        fold_boolean_expression(self, e)
    }

    fn fold_uint_expression(&mut self, e: UExpression<'ast, T>) -> UExpression<'ast, T> {
        fold_uint_expression(self, e)
    }

    fn fold_uint_expression_cases(
        &mut self,
        bitwidth: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> UExpressionInner<'ast, T> {
        fold_uint_expression_cases(self, bitwidth, e)
    }

    fn fold_uint_expression_inner(
        &mut self,
        bitwidth: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> UExpressionInner<'ast, T> {
        fold_uint_expression_inner(self, bitwidth, e)
    }

    fn fold_array_expression_cases(
        &mut self,
        ty: &ArrayType<'ast, T>,
        e: ArrayExpressionInner<'ast, T>,
    ) -> ArrayExpressionInner<'ast, T> {
        fold_array_expression_cases(self, ty, e)
    }

    fn fold_array_expression_inner(
        &mut self,
        ty: &ArrayType<'ast, T>,
        e: ArrayExpressionInner<'ast, T>,
    ) -> ArrayExpressionInner<'ast, T> {
        fold_array_expression_inner(self, ty, e)
    }

    fn fold_tuple_expression_cases(
        &mut self,
        ty: &TupleType<'ast, T>,
        e: TupleExpressionInner<'ast, T>,
    ) -> TupleExpressionInner<'ast, T> {
        fold_tuple_expression_cases(self, ty, e)
    }

    fn fold_tuple_expression_inner(
        &mut self,
        ty: &TupleType<'ast, T>,
        e: TupleExpressionInner<'ast, T>,
    ) -> TupleExpressionInner<'ast, T> {
        fold_tuple_expression_inner(self, ty, e)
    }

    fn fold_struct_expression_cases(
        &mut self,
        ty: &StructType<'ast, T>,
        e: StructExpressionInner<'ast, T>,
    ) -> StructExpressionInner<'ast, T> {
        fold_struct_expression_cases(self, ty, e)
    }

    fn fold_struct_expression_inner(
        &mut self,
        ty: &StructType<'ast, T>,
        e: StructExpressionInner<'ast, T>,
    ) -> StructExpressionInner<'ast, T> {
        fold_struct_expression_inner(self, ty, e)
    }

    fn fold_field_value_expression(
        &mut self,
        v: FieldValueExpression<T>,
    ) -> ValueOrExpression<FieldValueExpression<T>, FieldElementExpression<'ast, T>> {
        fold_field_value_expression(self, v)
    }

    fn fold_boolean_value_expression(
        &mut self,
        v: BooleanValueExpression,
    ) -> ValueOrExpression<BooleanValueExpression, BooleanExpression<'ast, T>> {
        fold_boolean_value_expression(self, v)
    }

    fn fold_integer_value_expression(
        &mut self,
        v: IntValueExpression,
    ) -> ValueOrExpression<IntValueExpression, IntExpression<'ast, T>> {
        fold_integer_value_expression(self, v)
    }

    fn fold_struct_value_expression(
        &mut self,
        ty: &StructType<'ast, T>,
        v: StructValueExpression<'ast, T>,
    ) -> ValueOrExpression<StructValueExpression<'ast, T>, StructExpressionInner<'ast, T>> {
        fold_struct_value_expression(self, ty, v)
    }

    fn fold_array_value_expression(
        &mut self,
        ty: &ArrayType<'ast, T>,
        v: ArrayValueExpression<'ast, T>,
    ) -> ValueOrExpression<ArrayValueExpression<'ast, T>, ArrayExpressionInner<'ast, T>> {
        fold_array_value_expression(self, ty, v)
    }

    fn fold_tuple_value_expression(
        &mut self,
        ty: &TupleType<'ast, T>,
        v: TupleValueExpression<'ast, T>,
    ) -> ValueOrExpression<TupleValueExpression<'ast, T>, TupleExpressionInner<'ast, T>> {
        fold_tuple_value_expression(self, ty, v)
    }
}

pub fn fold_module<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    m: TypedModule<'ast, T>,
) -> TypedModule<'ast, T> {
    TypedModule {
        symbols: m
            .symbols
            .into_iter()
            .map(|s| f.fold_symbol_declaration(s))
            .collect(),
    }
}

pub fn fold_symbol_declaration<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    d: TypedSymbolDeclaration<'ast, T>,
) -> TypedSymbolDeclaration<'ast, T> {
    match d {
        TypedSymbolDeclaration::Function(d) => {
            TypedSymbolDeclaration::Function(f.fold_function_symbol_declaration(d))
        }
        TypedSymbolDeclaration::Constant(d) => {
            TypedSymbolDeclaration::Constant(f.fold_constant_symbol_declaration(d))
        }
    }
}

pub fn fold_function_symbol_declaration<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    d: TypedFunctionSymbolDeclaration<'ast, T>,
) -> TypedFunctionSymbolDeclaration<'ast, T> {
    TypedFunctionSymbolDeclaration {
        key: f.fold_declaration_function_key(d.key),
        symbol: f.fold_function_symbol(d.symbol),
    }
}

pub fn fold_constant_symbol_declaration<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    d: TypedConstantSymbolDeclaration<'ast, T>,
) -> TypedConstantSymbolDeclaration<'ast, T> {
    TypedConstantSymbolDeclaration {
        id: f.fold_canonical_constant_identifier(d.id),
        symbol: f.fold_constant_symbol(d.symbol),
    }
}

pub fn fold_definition_rhs<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    rhs: DefinitionRhs<'ast, T>,
) -> DefinitionRhs<'ast, T> {
    match rhs {
        DefinitionRhs::EmbedCall(c) => DefinitionRhs::EmbedCall(f.fold_embed_call(c)),
        DefinitionRhs::Expression(e) => DefinitionRhs::Expression(f.fold_expression(e)),
    }
}

pub fn fold_return_statement<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: ReturnStatement<'ast, T>,
) -> Vec<TypedStatement<'ast, T>> {
    vec![TypedStatement::Return(ReturnStatement::new(
        f.fold_expression(s.inner),
    ))]
}

pub fn fold_definition_statement<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: DefinitionStatement<'ast, T>,
) -> Vec<TypedStatement<'ast, T>> {
    let rhs = f.fold_definition_rhs(s.rhs);
    vec![TypedStatement::Definition(
        DefinitionStatement::new(f.fold_assignee(s.assignee), rhs).span(s.span),
    )]
}

pub fn fold_assertion_statement<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: AssertionStatement<'ast, T>,
) -> Vec<TypedStatement<'ast, T>> {
    vec![TypedStatement::Assertion(
        AssertionStatement::new(f.fold_boolean_expression(s.expression), s.error).span(s.span),
    )]
}

pub fn fold_for_statement<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: ForStatement<'ast, T>,
) -> Vec<TypedStatement<'ast, T>> {
    vec![TypedStatement::For(ForStatement::new(
        f.fold_variable(s.var),
        f.fold_uint_expression(s.from),
        f.fold_uint_expression(s.to),
        s.statements
            .into_iter()
            .flat_map(|s| f.fold_statement(s))
            .collect(),
    ))]
}

pub fn fold_log_statement<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: LogStatement<'ast, T>,
) -> Vec<TypedStatement<'ast, T>> {
    vec![TypedStatement::Log(LogStatement::new(
        s.format_string,
        s.expressions
            .into_iter()
            .map(|e| f.fold_expression(e))
            .collect(),
    ))]
}

pub fn fold_statement_cases<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: TypedStatement<'ast, T>,
) -> Vec<TypedStatement<'ast, T>> {
    match s {
        TypedStatement::Return(s) => f.fold_return_statement(s),
        TypedStatement::Definition(s) => f.fold_definition_statement(s),
        TypedStatement::Assertion(s) => f.fold_assertion_statement(s),
        TypedStatement::For(s) => f.fold_for_statement(s),
        TypedStatement::Log(s) => f.fold_log_statement(s),
        TypedStatement::Assembly(s) => f.fold_assembly_block(s),
    }
}

pub fn fold_assembly_block<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: AssemblyBlockStatement<'ast, T>,
) -> Vec<TypedStatement<'ast, T>> {
    vec![TypedStatement::Assembly(AssemblyBlockStatement::new(
        s.inner
            .into_iter()
            .flat_map(|s| f.fold_assembly_statement(s))
            .collect(),
    ))]
}

pub fn fold_assembly_assignment<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: AssemblyAssignment<'ast, T>,
) -> Vec<TypedAssemblyStatement<'ast, T>> {
    let assignee = f.fold_assignee(s.assignee);
    let expression = f.fold_expression(s.expression);
    vec![TypedAssemblyStatement::assignment(assignee, expression)]
}

pub fn fold_assembly_constraint<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: AssemblyConstraint<'ast, T>,
) -> Vec<TypedAssemblyStatement<'ast, T>> {
    let left = f.fold_field_expression(s.left);
    let right = f.fold_field_expression(s.right);
    vec![TypedAssemblyStatement::constraint(left, right, s.metadata)]
}

fn fold_assembly_statement<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: TypedAssemblyStatement<'ast, T>,
) -> Vec<TypedAssemblyStatement<'ast, T>> {
    let span = s.get_span();
    f.fold_assembly_statement_cases(s)
        .into_iter()
        .map(|s| s.span(span))
        .collect()
}

pub fn fold_assembly_statement_cases<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: TypedAssemblyStatement<'ast, T>,
) -> Vec<TypedAssemblyStatement<'ast, T>> {
    match s {
        TypedAssemblyStatement::Assignment(s) => f.fold_assembly_assignment(s),
        TypedAssemblyStatement::Constraint(s) => f.fold_assembly_constraint(s),
    }
}

fn fold_statement<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: TypedStatement<'ast, T>,
) -> Vec<TypedStatement<'ast, T>> {
    let span = s.get_span();
    f.fold_statement_cases(s)
        .into_iter()
        .map(|s| s.span(span))
        .collect()
}

pub fn fold_identifier_expression<
    'ast,
    T: Field,
    E: Expr<'ast, T> + Id<'ast, T> + From<TypedExpression<'ast, T>>,
    F: Folder<'ast, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: IdentifierExpression<'ast, E>,
) -> IdentifierOrExpression<'ast, T, E> {
    IdentifierOrExpression::Identifier(IdentifierExpression::new(f.fold_name(e.id)))
}

pub fn fold_embed_call<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: EmbedCall<'ast, T>,
) -> EmbedCall<'ast, T> {
    EmbedCall {
        arguments: e
            .arguments
            .into_iter()
            .map(|s| f.fold_expression(s))
            .collect(),
        ..e
    }
}

pub fn fold_expression<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: TypedExpression<'ast, T>,
) -> TypedExpression<'ast, T> {
    match e {
        TypedExpression::FieldElement(e) => f.fold_field_expression(e).into(),
        TypedExpression::Boolean(e) => f.fold_boolean_expression(e).into(),
        TypedExpression::Uint(e) => f.fold_uint_expression(e).into(),
        TypedExpression::Array(e) => f.fold_array_expression(e).into(),
        TypedExpression::Tuple(e) => f.fold_tuple_expression(e).into(),
        TypedExpression::Struct(e) => f.fold_struct_expression(e).into(),
        TypedExpression::Int(e) => f.fold_int_expression(e).into(),
    }
}

fn fold_array_expression_inner<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    ty: &ArrayType<'ast, T>,
    e: ArrayExpressionInner<'ast, T>,
) -> ArrayExpressionInner<'ast, T> {
    let span = e.get_span();
    f.fold_array_expression_cases(ty, e).span(span)
}

pub fn fold_array_expression_cases<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    ty: &ArrayType<'ast, T>,
    e: ArrayExpressionInner<'ast, T>,
) -> ArrayExpressionInner<'ast, T> {
    use ArrayExpressionInner::*;

    match e {
        Identifier(id) => match f.fold_identifier_expression(ty, id) {
            IdentifierOrExpression::Identifier(i) => ArrayExpressionInner::Identifier(i),
            IdentifierOrExpression::Expression(u) => u,
        },
        Block(block) => Block(f.fold_block_expression(block)),
        FunctionCall(function_call) => match f.fold_function_call_expression(ty, function_call) {
            FunctionCallOrExpression::FunctionCall(function_call) => FunctionCall(function_call),
            FunctionCallOrExpression::Expression(u) => u,
        },
        Value(function_call) => match f.fold_array_value_expression(ty, function_call) {
            ValueOrExpression::Value(value) => Value(value),
            ValueOrExpression::Expression(e) => e,
        },
        Conditional(c) => match f.fold_conditional_expression(ty, c) {
            ConditionalOrExpression::Conditional(s) => Conditional(s),
            ConditionalOrExpression::Expression(u) => u,
        },
        Select(select) => match f.fold_select_expression(ty, select) {
            SelectOrExpression::Select(s) => Select(s),
            SelectOrExpression::Expression(u) => u,
        },
        Member(m) => match f.fold_member_expression(ty, m) {
            MemberOrExpression::Member(m) => Member(m),
            MemberOrExpression::Expression(u) => u,
        },
        Slice(s) => match f.fold_slice_expression(s) {
            SliceOrExpression::Slice(m) => Slice(m),
            SliceOrExpression::Expression(u) => u,
        },
        Repeat(s) => match f.fold_repeat_expression(s) {
            RepeatOrExpression::Repeat(m) => Repeat(m),
            RepeatOrExpression::Expression(u) => u,
        },
        Element(m) => match f.fold_element_expression(ty, m) {
            ElementOrExpression::Element(m) => Element(m),
            ElementOrExpression::Expression(u) => u,
        },
    }
}

fn fold_struct_expression_inner<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    ty: &StructType<'ast, T>,
    e: StructExpressionInner<'ast, T>,
) -> StructExpressionInner<'ast, T> {
    let span = e.get_span();
    f.fold_struct_expression_cases(ty, e).span(span)
}

pub fn fold_struct_expression_cases<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    ty: &StructType<'ast, T>,
    e: StructExpressionInner<'ast, T>,
) -> StructExpressionInner<'ast, T> {
    use StructExpressionInner::*;

    match e {
        Identifier(id) => match f.fold_identifier_expression(ty, id) {
            IdentifierOrExpression::Identifier(i) => Identifier(i),
            IdentifierOrExpression::Expression(u) => u,
        },
        Block(block) => Block(f.fold_block_expression(block)),
        Value(function_call) => match f.fold_struct_value_expression(ty, function_call) {
            ValueOrExpression::Value(value) => Value(value),
            ValueOrExpression::Expression(e) => e,
        },
        FunctionCall(function_call) => match f.fold_function_call_expression(ty, function_call) {
            FunctionCallOrExpression::FunctionCall(function_call) => FunctionCall(function_call),
            FunctionCallOrExpression::Expression(u) => u,
        },
        Conditional(c) => match f.fold_conditional_expression(ty, c) {
            ConditionalOrExpression::Conditional(s) => Conditional(s),
            ConditionalOrExpression::Expression(u) => u,
        },
        Select(select) => match f.fold_select_expression(ty, select) {
            SelectOrExpression::Select(s) => Select(s),
            SelectOrExpression::Expression(u) => u,
        },
        Member(m) => match f.fold_member_expression(ty, m) {
            MemberOrExpression::Member(m) => Member(m),
            MemberOrExpression::Expression(u) => u,
        },
        Element(m) => match f.fold_element_expression(ty, m) {
            ElementOrExpression::Element(m) => Element(m),
            ElementOrExpression::Expression(u) => u,
        },
    }
}

fn fold_tuple_expression_inner<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    ty: &TupleType<'ast, T>,
    e: TupleExpressionInner<'ast, T>,
) -> TupleExpressionInner<'ast, T> {
    let span = e.get_span();
    f.fold_tuple_expression_cases(ty, e).span(span)
}

pub fn fold_tuple_expression_cases<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    ty: &TupleType<'ast, T>,
    e: TupleExpressionInner<'ast, T>,
) -> TupleExpressionInner<'ast, T> {
    use TupleExpressionInner::*;

    match e {
        Block(block) => Block(f.fold_block_expression(block)),
        Identifier(id) => match f.fold_identifier_expression(ty, id) {
            IdentifierOrExpression::Identifier(i) => Identifier(i),
            IdentifierOrExpression::Expression(u) => u,
        },
        Value(function_call) => match f.fold_tuple_value_expression(ty, function_call) {
            ValueOrExpression::Value(value) => Value(value),
            ValueOrExpression::Expression(e) => e,
        },
        FunctionCall(function_call) => match f.fold_function_call_expression(ty, function_call) {
            FunctionCallOrExpression::FunctionCall(function_call) => FunctionCall(function_call),
            FunctionCallOrExpression::Expression(u) => u,
        },
        Conditional(c) => match f.fold_conditional_expression(ty, c) {
            ConditionalOrExpression::Conditional(s) => Conditional(s),
            ConditionalOrExpression::Expression(u) => u,
        },
        Select(select) => match f.fold_select_expression(ty, select) {
            SelectOrExpression::Select(s) => Select(s),
            SelectOrExpression::Expression(u) => u,
        },
        Member(m) => match f.fold_member_expression(ty, m) {
            MemberOrExpression::Member(m) => Member(m),
            MemberOrExpression::Expression(u) => u,
        },
        Element(m) => match f.fold_element_expression(ty, m) {
            ElementOrExpression::Element(m) => Element(m),
            ElementOrExpression::Expression(u) => u,
        },
    }
}

fn fold_field_expression<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: FieldElementExpression<'ast, T>,
) -> FieldElementExpression<'ast, T> {
    let span = e.get_span();
    f.fold_field_expression_cases(e).span(span)
}

pub fn fold_field_expression_cases<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: FieldElementExpression<'ast, T>,
) -> FieldElementExpression<'ast, T> {
    use FieldElementExpression::*;

    match e {
        Identifier(id) => match f.fold_identifier_expression(&Type::FieldElement, id) {
            IdentifierOrExpression::Identifier(i) => Identifier(i),
            IdentifierOrExpression::Expression(u) => u,
        },
        Block(block) => Block(f.fold_block_expression(block)),
        Value(value) => match f.fold_field_value_expression(value) {
            ValueOrExpression::Value(value) => Value(value),
            ValueOrExpression::Expression(e) => e,
        },
        Add(e) => match f.fold_binary_expression(&Type::FieldElement, e) {
            BinaryOrExpression::Binary(e) => Add(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Sub(e) => match f.fold_binary_expression(&Type::FieldElement, e) {
            BinaryOrExpression::Binary(e) => Sub(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Mult(e) => match f.fold_binary_expression(&Type::FieldElement, e) {
            BinaryOrExpression::Binary(e) => Mult(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Div(e) => match f.fold_binary_expression(&Type::FieldElement, e) {
            BinaryOrExpression::Binary(e) => Div(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Pow(e) => match f.fold_binary_expression(&Type::FieldElement, e) {
            BinaryOrExpression::Binary(e) => Pow(e),
            BinaryOrExpression::Expression(u) => u,
        },
        And(e) => match f.fold_binary_expression(&Type::FieldElement, e) {
            BinaryOrExpression::Binary(e) => And(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Or(e) => match f.fold_binary_expression(&Type::FieldElement, e) {
            BinaryOrExpression::Binary(e) => Or(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Xor(e) => match f.fold_binary_expression(&Type::FieldElement, e) {
            BinaryOrExpression::Binary(e) => Xor(e),
            BinaryOrExpression::Expression(u) => u,
        },
        LeftShift(e) => match f.fold_binary_expression(&Type::FieldElement, e) {
            BinaryOrExpression::Binary(e) => LeftShift(e),
            BinaryOrExpression::Expression(u) => u,
        },
        RightShift(e) => match f.fold_binary_expression(&Type::FieldElement, e) {
            BinaryOrExpression::Binary(e) => RightShift(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Neg(e) => match f.fold_unary_expression(&Type::FieldElement, e) {
            UnaryOrExpression::Unary(e) => Neg(e),
            UnaryOrExpression::Expression(u) => u,
        },
        Pos(e) => match f.fold_unary_expression(&Type::FieldElement, e) {
            UnaryOrExpression::Unary(e) => Pos(e),
            UnaryOrExpression::Expression(u) => u,
        },
        Conditional(c) => match f.fold_conditional_expression(&Type::FieldElement, c) {
            ConditionalOrExpression::Conditional(s) => Conditional(s),
            ConditionalOrExpression::Expression(u) => u,
        },
        FunctionCall(function_call) => {
            match f.fold_function_call_expression(&Type::FieldElement, function_call) {
                FunctionCallOrExpression::FunctionCall(function_call) => {
                    FunctionCall(function_call)
                }
                FunctionCallOrExpression::Expression(u) => u,
            }
        }
        Select(select) => match f.fold_select_expression(&Type::FieldElement, select) {
            SelectOrExpression::Select(s) => Select(s),
            SelectOrExpression::Expression(u) => u,
        },
        Member(m) => match f.fold_member_expression(&Type::FieldElement, m) {
            MemberOrExpression::Member(m) => Member(m),
            MemberOrExpression::Expression(u) => u,
        },
        Element(m) => match f.fold_element_expression(&Type::FieldElement, m) {
            ElementOrExpression::Element(m) => Element(m),
            ElementOrExpression::Expression(u) => u,
        },
    }
}

pub fn fold_conditional_expression<
    'ast,
    T: Field,
    E: Expr<'ast, T> + Fold<F> + Conditional<'ast, T> + From<TypedExpression<'ast, T>>,
    F: Folder<'ast, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: ConditionalExpression<'ast, T, E>,
) -> ConditionalOrExpression<'ast, T, E> {
    ConditionalOrExpression::Conditional(
        ConditionalExpression::new(
            f.fold_boolean_expression(*e.condition),
            e.consequence.fold(f),
            e.alternative.fold(f),
            e.kind,
        )
        .span(e.span),
    )
}

pub fn fold_binary_expression<
    'ast,
    T: Field,
    L: Expr<'ast, T> + Fold<F> + From<TypedExpression<'ast, T>>,
    R: Expr<'ast, T> + Fold<F> + From<TypedExpression<'ast, T>>,
    E: Expr<'ast, T> + Fold<F> + From<TypedExpression<'ast, T>>,
    F: Folder<'ast, T>,
    Op,
>(
    f: &mut F,
    _: &E::Ty,
    e: BinaryExpression<Op, L, R, E>,
) -> BinaryOrExpression<Op, L, R, E, E::Inner> {
    BinaryOrExpression::Binary(BinaryExpression::new(e.left.fold(f), e.right.fold(f)))
}

pub fn fold_unary_expression<
    'ast,
    T: Field,
    In: Expr<'ast, T> + Fold<F> + From<TypedExpression<'ast, T>>,
    E: Expr<'ast, T> + Fold<F> + From<TypedExpression<'ast, T>>,
    F: Folder<'ast, T>,
    Op,
>(
    f: &mut F,
    _: &E::Ty,
    e: UnaryExpression<Op, In, E>,
) -> UnaryOrExpression<Op, In, E, E::Inner> {
    UnaryOrExpression::Unary(UnaryExpression::new(e.inner.fold(f)))
}

pub fn fold_member_expression<
    'ast,
    T: Field,
    E: Expr<'ast, T> + Member<'ast, T> + From<TypedExpression<'ast, T>>,
    F: Folder<'ast, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: MemberExpression<'ast, T, E>,
) -> MemberOrExpression<'ast, T, E> {
    MemberOrExpression::Member(MemberExpression::new(
        f.fold_struct_expression(*e.struc),
        e.id,
    ))
}

pub fn fold_slice_expression<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: SliceExpression<'ast, T>,
) -> SliceOrExpression<'ast, T> {
    SliceOrExpression::Slice(SliceExpression::new(
        f.fold_array_expression(*e.array),
        f.fold_uint_expression(*e.from),
        f.fold_uint_expression(*e.to),
    ))
}

pub fn fold_repeat_expression<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: RepeatExpression<'ast, T>,
) -> RepeatOrExpression<'ast, T> {
    RepeatOrExpression::Repeat(RepeatExpression::new(
        f.fold_expression(*e.e),
        f.fold_uint_expression(*e.count),
    ))
}

pub fn fold_element_expression<
    'ast,
    T: Field,
    E: Expr<'ast, T> + Element<'ast, T> + From<TypedExpression<'ast, T>>,
    F: Folder<'ast, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: ElementExpression<'ast, T, E>,
) -> ElementOrExpression<'ast, T, E> {
    ElementOrExpression::Element(
        ElementExpression::new(f.fold_tuple_expression(*e.tuple), e.index).span(e.span),
    )
}

pub fn fold_select_expression<
    'ast,
    T: Field,
    E: Expr<'ast, T> + Select<'ast, T> + Conditional<'ast, T> + From<TypedExpression<'ast, T>>,
    F: Folder<'ast, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: SelectExpression<'ast, T, E>,
) -> SelectOrExpression<'ast, T, E> {
    SelectOrExpression::Select(
        SelectExpression::new(
            f.fold_array_expression(*e.array),
            f.fold_uint_expression(*e.index),
        )
        .span(e.span),
    )
}

pub fn fold_int_expression<'ast, T: Field, F: Folder<'ast, T>>(
    _: &mut F,
    _: IntExpression<'ast, T>,
) -> IntExpression<'ast, T> {
    unreachable!()
}

fn fold_boolean_expression<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: BooleanExpression<'ast, T>,
) -> BooleanExpression<'ast, T> {
    let span = e.get_span();
    f.fold_boolean_expression_cases(e).span(span)
}

pub fn fold_boolean_expression_cases<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: BooleanExpression<'ast, T>,
) -> BooleanExpression<'ast, T> {
    use BooleanExpression::*;

    match e {
        Identifier(id) => match f.fold_identifier_expression(&Type::Boolean, id) {
            IdentifierOrExpression::Identifier(i) => Identifier(i),
            IdentifierOrExpression::Expression(u) => u,
        },
        Block(block) => BooleanExpression::Block(f.fold_block_expression(block)),
        Value(e) => match f.fold_boolean_value_expression(e) {
            ValueOrExpression::Value(e) => Value(e),
            ValueOrExpression::Expression(u) => u,
        },
        FieldEq(e) => match f.fold_eq_expression(e) {
            BinaryOrExpression::Binary(e) => FieldEq(e),
            BinaryOrExpression::Expression(u) => u,
        },
        BoolEq(e) => match f.fold_eq_expression(e) {
            BinaryOrExpression::Binary(e) => BoolEq(e),
            BinaryOrExpression::Expression(u) => u,
        },
        ArrayEq(e) => match f.fold_eq_expression(e) {
            BinaryOrExpression::Binary(e) => ArrayEq(e),
            BinaryOrExpression::Expression(u) => u,
        },
        StructEq(e) => match f.fold_eq_expression(e) {
            BinaryOrExpression::Binary(e) => StructEq(e),
            BinaryOrExpression::Expression(u) => u,
        },
        TupleEq(e) => match f.fold_eq_expression(e) {
            BinaryOrExpression::Binary(e) => TupleEq(e),
            BinaryOrExpression::Expression(u) => u,
        },
        UintEq(e) => match f.fold_eq_expression(e) {
            BinaryOrExpression::Binary(e) => UintEq(e),
            BinaryOrExpression::Expression(u) => u,
        },
        FieldLt(e) => match f.fold_binary_expression(&Type::Boolean, e) {
            BinaryOrExpression::Binary(e) => FieldLt(e),
            BinaryOrExpression::Expression(u) => u,
        },
        FieldLe(e) => match f.fold_binary_expression(&Type::Boolean, e) {
            BinaryOrExpression::Binary(e) => FieldLe(e),
            BinaryOrExpression::Expression(u) => u,
        },
        UintLt(e) => match f.fold_binary_expression(&Type::Boolean, e) {
            BinaryOrExpression::Binary(e) => UintLt(e),
            BinaryOrExpression::Expression(u) => u,
        },
        UintLe(e) => match f.fold_binary_expression(&Type::Boolean, e) {
            BinaryOrExpression::Binary(e) => UintLe(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Or(e) => match f.fold_binary_expression(&Type::Boolean, e) {
            BinaryOrExpression::Binary(e) => Or(e),
            BinaryOrExpression::Expression(u) => u,
        },
        And(e) => match f.fold_binary_expression(&Type::Boolean, e) {
            BinaryOrExpression::Binary(e) => And(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Not(e) => match f.fold_unary_expression(&Type::Boolean, e) {
            UnaryOrExpression::Unary(e) => Not(e),
            UnaryOrExpression::Expression(u) => u,
        },
        FunctionCall(function_call) => {
            match f.fold_function_call_expression(&Type::Boolean, function_call) {
                FunctionCallOrExpression::FunctionCall(function_call) => {
                    FunctionCall(function_call)
                }
                FunctionCallOrExpression::Expression(u) => u,
            }
        }
        Conditional(c) => match f.fold_conditional_expression(&Type::Boolean, c) {
            ConditionalOrExpression::Conditional(s) => Conditional(s),
            ConditionalOrExpression::Expression(u) => u,
        },
        Select(select) => match f.fold_select_expression(&Type::Boolean, select) {
            SelectOrExpression::Select(s) => Select(s),
            SelectOrExpression::Expression(u) => u,
        },
        Member(m) => match f.fold_member_expression(&Type::Boolean, m) {
            MemberOrExpression::Member(m) => Member(m),
            MemberOrExpression::Expression(u) => u,
        },
        Element(m) => match f.fold_element_expression(&Type::Boolean, m) {
            ElementOrExpression::Element(m) => Element(m),
            ElementOrExpression::Expression(u) => u,
        },
    }
}

pub fn fold_uint_expression<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: UExpression<'ast, T>,
) -> UExpression<'ast, T> {
    UExpression {
        inner: f.fold_uint_expression_inner(e.bitwidth, e.inner),
        ..e
    }
}

fn fold_uint_expression_inner<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    ty: UBitwidth,
    e: UExpressionInner<'ast, T>,
) -> UExpressionInner<'ast, T> {
    let span = e.get_span();
    f.fold_uint_expression_cases(ty, e).span(span)
}

pub fn fold_uint_expression_cases<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    ty: UBitwidth,
    e: UExpressionInner<'ast, T>,
) -> UExpressionInner<'ast, T> {
    use UExpressionInner::*;

    match e {
        Identifier(id) => match f.fold_identifier_expression(&ty, id) {
            IdentifierOrExpression::Identifier(i) => Identifier(i),
            IdentifierOrExpression::Expression(u) => u,
        },
        Block(block) => Block(f.fold_block_expression(block)),
        Value(v) => Value(v),
        Add(e) => match f.fold_binary_expression(&ty, e) {
            BinaryOrExpression::Binary(e) => Add(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Sub(e) => match f.fold_binary_expression(&ty, e) {
            BinaryOrExpression::Binary(e) => Sub(e),
            BinaryOrExpression::Expression(u) => u,
        },
        FloorSub(e) => match f.fold_binary_expression(&ty, e) {
            BinaryOrExpression::Binary(e) => FloorSub(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Mult(e) => match f.fold_binary_expression(&ty, e) {
            BinaryOrExpression::Binary(e) => Mult(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Div(e) => match f.fold_binary_expression(&ty, e) {
            BinaryOrExpression::Binary(e) => Div(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Rem(e) => match f.fold_binary_expression(&ty, e) {
            BinaryOrExpression::Binary(e) => Rem(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Xor(e) => match f.fold_binary_expression(&ty, e) {
            BinaryOrExpression::Binary(e) => Xor(e),
            BinaryOrExpression::Expression(u) => u,
        },
        And(e) => match f.fold_binary_expression(&ty, e) {
            BinaryOrExpression::Binary(e) => And(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Or(e) => match f.fold_binary_expression(&ty, e) {
            BinaryOrExpression::Binary(e) => Or(e),
            BinaryOrExpression::Expression(u) => u,
        },
        LeftShift(e) => match f.fold_binary_expression(&ty, e) {
            BinaryOrExpression::Binary(e) => LeftShift(e),
            BinaryOrExpression::Expression(u) => u,
        },
        RightShift(e) => match f.fold_binary_expression(&ty, e) {
            BinaryOrExpression::Binary(e) => RightShift(e),
            BinaryOrExpression::Expression(u) => u,
        },
        Not(e) => match f.fold_unary_expression(&ty, e) {
            UnaryOrExpression::Unary(e) => Not(e),
            UnaryOrExpression::Expression(u) => u,
        },
        Neg(e) => match f.fold_unary_expression(&ty, e) {
            UnaryOrExpression::Unary(e) => Neg(e),
            UnaryOrExpression::Expression(u) => u,
        },
        Pos(e) => match f.fold_unary_expression(&ty, e) {
            UnaryOrExpression::Unary(e) => Pos(e),
            UnaryOrExpression::Expression(u) => u,
        },
        FunctionCall(function_call) => match f.fold_function_call_expression(&ty, function_call) {
            FunctionCallOrExpression::FunctionCall(function_call) => FunctionCall(function_call),
            FunctionCallOrExpression::Expression(u) => u,
        },
        Select(select) => match f.fold_select_expression(&ty, select) {
            SelectOrExpression::Select(s) => Select(s),
            SelectOrExpression::Expression(u) => u,
        },
        Conditional(c) => match f.fold_conditional_expression(&ty, c) {
            ConditionalOrExpression::Conditional(s) => Conditional(s),
            ConditionalOrExpression::Expression(u) => u,
        },
        Member(m) => match f.fold_member_expression(&ty, m) {
            MemberOrExpression::Member(m) => UExpressionInner::Member(m),
            MemberOrExpression::Expression(u) => u,
        },
        Element(m) => match f.fold_element_expression(&ty, m) {
            ElementOrExpression::Element(m) => Element(m),
            ElementOrExpression::Expression(u) => u,
        },
    }
}

pub fn fold_block_expression<'ast, T: Field, E: Fold<F>, F: Folder<'ast, T>>(
    f: &mut F,
    block: BlockExpression<'ast, T, E>,
) -> BlockExpression<'ast, T, E> {
    BlockExpression::new(
        block
            .statements
            .into_iter()
            .flat_map(|s| f.fold_statement(s))
            .collect(),
        block.value.fold(f),
    )
    .span(block.span)
}

pub fn fold_declaration_function_key<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    key: DeclarationFunctionKey<'ast, T>,
) -> DeclarationFunctionKey<'ast, T> {
    DeclarationFunctionKey {
        module: f.fold_module_id(key.module),
        signature: f.fold_signature(key.signature),
        ..key
    }
}

pub fn fold_function_call_expression<
    'ast,
    T: Field,
    E: Id<'ast, T> + From<TypedExpression<'ast, T>> + Expr<'ast, T> + FunctionCall<'ast, T>,
    F: Folder<'ast, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: FunctionCallExpression<'ast, T, E>,
) -> FunctionCallOrExpression<'ast, T, E> {
    FunctionCallOrExpression::FunctionCall(
        FunctionCallExpression::new(
            f.fold_declaration_function_key(e.function_key),
            e.generics
                .into_iter()
                .map(|g| g.map(|g| f.fold_uint_expression(g)))
                .collect(),
            e.arguments
                .into_iter()
                .map(|e| f.fold_expression(e))
                .collect(),
        )
        .span(e.span),
    )
}

pub fn fold_function<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    fun: TypedFunction<'ast, T>,
) -> TypedFunction<'ast, T> {
    TypedFunction {
        arguments: fun
            .arguments
            .into_iter()
            .map(|a| f.fold_parameter(a))
            .collect(),
        statements: fun
            .statements
            .into_iter()
            .flat_map(|s| f.fold_statement(s))
            .collect(),
        signature: f.fold_signature(fun.signature),
    }
}

fn fold_signature<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: DeclarationSignature<'ast, T>,
) -> DeclarationSignature<'ast, T> {
    DeclarationSignature {
        generics: s.generics,
        inputs: s
            .inputs
            .into_iter()
            .map(|o| f.fold_declaration_type(o))
            .collect(),
        output: Box::new(f.fold_declaration_type(*s.output)),
    }
}

pub fn fold_declaration_constant<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    c: DeclarationConstant<'ast, T>,
) -> DeclarationConstant<'ast, T> {
    match c {
        DeclarationConstant::Expression(e) => DeclarationConstant::Expression(f.fold_expression(e)),
        DeclarationConstant::Constant(c) => {
            DeclarationConstant::Constant(f.fold_canonical_constant_identifier(c))
        }
        c => c,
    }
}

pub fn fold_array_expression<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: ArrayExpression<'ast, T>,
) -> ArrayExpression<'ast, T> {
    let ty = f.fold_array_type(*e.ty);

    ArrayExpression {
        inner: f.fold_array_expression_inner(&ty, e.inner),
        ty: Box::new(ty),
    }
}

pub fn fold_struct_expression<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: StructExpression<'ast, T>,
) -> StructExpression<'ast, T> {
    let ty = f.fold_struct_type(e.ty);
    StructExpression {
        inner: f.fold_struct_expression_inner(&ty, e.inner),
        ty,
    }
}

pub fn fold_tuple_expression<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: TupleExpression<'ast, T>,
) -> TupleExpression<'ast, T> {
    let ty = f.fold_tuple_type(e.ty);
    TupleExpression {
        inner: f.fold_tuple_expression_inner(&ty, e.inner),
        ty,
    }
}

pub fn fold_integer_value_expression<'ast, T: Field, F: Folder<'ast, T>>(
    _f: &mut F,
    a: IntValueExpression,
) -> ValueOrExpression<IntValueExpression, IntExpression<'ast, T>> {
    ValueOrExpression::Value(a)
}

pub fn fold_boolean_value_expression<'ast, T: Field, F: Folder<'ast, T>>(
    _f: &mut F,
    a: BooleanValueExpression,
) -> ValueOrExpression<BooleanValueExpression, BooleanExpression<'ast, T>> {
    ValueOrExpression::Value(a)
}

pub fn fold_field_value_expression<'ast, T: Field, F: Folder<'ast, T>>(
    _f: &mut F,
    a: FieldValueExpression<T>,
) -> ValueOrExpression<FieldValueExpression<T>, FieldElementExpression<'ast, T>> {
    ValueOrExpression::Value(a)
}

pub fn fold_struct_value_expression<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    _ty: &StructType<'ast, T>,
    a: StructValueExpression<'ast, T>,
) -> ValueOrExpression<StructValueExpression<'ast, T>, StructExpressionInner<'ast, T>> {
    ValueOrExpression::Value(StructValueExpression {
        value: a.value.into_iter().map(|v| f.fold_expression(v)).collect(),
        ..a
    })
}

pub fn fold_array_value_expression<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    _ty: &ArrayType<'ast, T>,
    a: ArrayValueExpression<'ast, T>,
) -> ValueOrExpression<ArrayValueExpression<'ast, T>, ArrayExpressionInner<'ast, T>> {
    ValueOrExpression::Value(ArrayValueExpression {
        value: a
            .value
            .into_iter()
            .map(|v| f.fold_expression_or_spread(v))
            .collect(),
        ..a
    })
}

pub fn fold_tuple_value_expression<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    _ty: &TupleType<'ast, T>,
    a: TupleValueExpression<'ast, T>,
) -> ValueOrExpression<TupleValueExpression<'ast, T>, TupleExpressionInner<'ast, T>> {
    ValueOrExpression::Value(TupleValueExpression {
        value: a.value.into_iter().map(|v| f.fold_expression(v)).collect(),
        ..a
    })
}

pub fn fold_constant<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    c: TypedConstant<'ast, T>,
) -> TypedConstant<'ast, T> {
    TypedConstant {
        expression: f.fold_expression(c.expression),
        ty: f.fold_declaration_type(c.ty),
    }
}

pub fn fold_constant_symbol<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: TypedConstantSymbol<'ast, T>,
) -> TypedConstantSymbol<'ast, T> {
    match s {
        TypedConstantSymbol::Here(tc) => TypedConstantSymbol::Here(f.fold_constant(tc)),
        TypedConstantSymbol::There(id) => {
            TypedConstantSymbol::There(f.fold_canonical_constant_identifier(id))
        }
    }
}

pub fn fold_function_symbol<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: TypedFunctionSymbol<'ast, T>,
) -> TypedFunctionSymbol<'ast, T> {
    match s {
        TypedFunctionSymbol::Here(fun) => TypedFunctionSymbol::Here(f.fold_function(fun)),
        TypedFunctionSymbol::There(key) => {
            TypedFunctionSymbol::There(f.fold_declaration_function_key(key))
        }
        s => s,
    }
}

pub fn fold_assignee<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    a: TypedAssignee<'ast, T>,
) -> TypedAssignee<'ast, T> {
    match a {
        TypedAssignee::Identifier(v) => TypedAssignee::Identifier(f.fold_variable(v)),
        TypedAssignee::Select(a, index) => TypedAssignee::Select(
            Box::new(f.fold_assignee(*a)),
            Box::new(f.fold_uint_expression(*index)),
        ),
        TypedAssignee::Member(s, m) => TypedAssignee::Member(Box::new(f.fold_assignee(*s)), m),
        TypedAssignee::Element(s, index) => {
            TypedAssignee::Element(Box::new(f.fold_assignee(*s)), index)
        }
    }
}

pub fn fold_program<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    p: TypedProgram<'ast, T>,
) -> TypedProgram<'ast, T> {
    TypedProgram {
        modules: p
            .modules
            .into_iter()
            .map(|(module_id, module)| (f.fold_module_id(module_id), f.fold_module(module)))
            .collect(),
        main: f.fold_module_id(p.main),
        ..p
    }
}
