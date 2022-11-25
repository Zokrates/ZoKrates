// Generic walk through a typed AST. Not mutating in place

use crate::typed::types::*;
use crate::typed::*;
use zokrates_field::Field;

use super::identifier::IdTrait;

pub trait Fold<I: IdTrait, T: Field>: Sized {
    fn fold<F: Folder<I, T>>(self, f: &mut F) -> Self;
}

impl<I: IdTrait, T: Field> Fold<I, T> for FieldElementExpression<I, T> {
    fn fold<F: Folder<I, T>>(self, f: &mut F) -> Self {
        f.fold_field_expression(self)
    }
}

impl<I: IdTrait, T: Field> Fold<I, T> for BooleanExpression<I, T> {
    fn fold<F: Folder<I, T>>(self, f: &mut F) -> Self {
        f.fold_boolean_expression(self)
    }
}

impl<I: IdTrait, T: Field> Fold<I, T> for UExpression<I, T> {
    fn fold<F: Folder<I, T>>(self, f: &mut F) -> Self {
        f.fold_uint_expression(self)
    }
}

impl<I: IdTrait, T: Field> Fold<I, T> for StructExpression<I, T> {
    fn fold<F: Folder<I, T>>(self, f: &mut F) -> Self {
        f.fold_struct_expression(self)
    }
}

impl<I: IdTrait, T: Field> Fold<I, T> for ArrayExpression<I, T> {
    fn fold<F: Folder<I, T>>(self, f: &mut F) -> Self {
        f.fold_array_expression(self)
    }
}

impl<I: IdTrait, T: Field> Fold<I, T> for TupleExpression<I, T> {
    fn fold<F: Folder<I, T>>(self, f: &mut F) -> Self {
        f.fold_tuple_expression(self)
    }
}

pub trait Folder<I: IdTrait, T: Field>: Sized {
    fn fold_program(&mut self, p: TypedProgram<I, T>) -> TypedProgram<I, T> {
        fold_program(self, p)
    }

    fn fold_module(&mut self, m: TypedModule<I, T>) -> TypedModule<I, T> {
        fold_module(self, m)
    }

    fn fold_symbol_declaration(
        &mut self,
        s: TypedSymbolDeclaration<I, T>,
    ) -> TypedSymbolDeclaration<I, T> {
        fold_symbol_declaration(self, s)
    }

    fn fold_function_symbol_declaration(
        &mut self,
        s: TypedFunctionSymbolDeclaration<I, T>,
    ) -> TypedFunctionSymbolDeclaration<I, T> {
        fold_function_symbol_declaration(self, s)
    }

    fn fold_constant_symbol_declaration(
        &mut self,
        s: TypedConstantSymbolDeclaration<I, T>,
    ) -> TypedConstantSymbolDeclaration<I, T> {
        fold_constant_symbol_declaration(self, s)
    }

    fn fold_constant(&mut self, c: TypedConstant<I, T>) -> TypedConstant<I, T> {
        fold_constant(self, c)
    }

    fn fold_constant_symbol(&mut self, s: TypedConstantSymbol<I, T>) -> TypedConstantSymbol<I, T> {
        fold_constant_symbol(self, s)
    }

    fn fold_function_symbol(&mut self, s: TypedFunctionSymbol<I, T>) -> TypedFunctionSymbol<I, T> {
        fold_function_symbol(self, s)
    }

    fn fold_declaration_function_key(
        &mut self,
        key: DeclarationFunctionKey<I, T>,
    ) -> DeclarationFunctionKey<I, T> {
        fold_declaration_function_key(self, key)
    }

    fn fold_function(&mut self, f: TypedFunction<I, T>) -> TypedFunction<I, T> {
        fold_function(self, f)
    }

    fn fold_signature(&mut self, s: DeclarationSignature<I, T>) -> DeclarationSignature<I, T> {
        fold_signature(self, s)
    }

    fn fold_declaration_constant(
        &mut self,
        c: DeclarationConstant<I, T>,
    ) -> DeclarationConstant<I, T> {
        fold_declaration_constant(self, c)
    }

    fn fold_parameter(&mut self, p: DeclarationParameter<I, T>) -> DeclarationParameter<I, T> {
        DeclarationParameter {
            id: self.fold_declaration_variable(p.id),
            ..p
        }
    }

    fn fold_name(&mut self, n: Identifier<I>) -> Identifier<I> {
        let id = match n.id {
            CoreIdentifier::Constant(c) => {
                CoreIdentifier::Constant(self.fold_canonical_constant_identifier(c))
            }
            id => id,
        };

        Identifier { id, ..n }
    }

    fn fold_variable(&mut self, v: Variable<I, T>) -> Variable<I, T> {
        Variable {
            id: self.fold_name(v.id),
            _type: self.fold_type(v._type),
            is_mutable: v.is_mutable,
        }
    }

    fn fold_declaration_variable(
        &mut self,
        v: DeclarationVariable<I, T>,
    ) -> DeclarationVariable<I, T> {
        DeclarationVariable {
            id: self.fold_name(v.id),
            _type: self.fold_declaration_type(v._type),
            is_mutable: v.is_mutable,
        }
    }

    fn fold_type(&mut self, t: Type<I, T>) -> Type<I, T> {
        use self::GType::*;

        match t {
            Array(array_type) => Array(self.fold_array_type(array_type)),
            Struct(struct_type) => Struct(self.fold_struct_type(struct_type)),
            Tuple(tuple_type) => Tuple(self.fold_tuple_type(tuple_type)),
            t => t,
        }
    }

    fn fold_array_type(&mut self, t: ArrayType<I, T>) -> ArrayType<I, T> {
        ArrayType {
            ty: box self.fold_type(*t.ty),
            size: box self.fold_uint_expression(*t.size),
        }
    }

    fn fold_tuple_type(&mut self, t: TupleType<I, T>) -> TupleType<I, T> {
        TupleType {
            elements: t.elements.into_iter().map(|t| self.fold_type(t)).collect(),
        }
    }

    fn fold_struct_type(&mut self, t: StructType<I, T>) -> StructType<I, T> {
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
                    ty: box self.fold_type(*m.ty),
                    ..m
                })
                .collect(),
            ..t
        }
    }

    fn fold_declaration_type(&mut self, t: DeclarationType<I, T>) -> DeclarationType<I, T> {
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
        t: DeclarationArrayType<I, T>,
    ) -> DeclarationArrayType<I, T> {
        DeclarationArrayType {
            ty: box self.fold_declaration_type(*t.ty),
            size: box self.fold_declaration_constant(*t.size),
        }
    }

    fn fold_declaration_tuple_type(
        &mut self,
        t: DeclarationTupleType<I, T>,
    ) -> DeclarationTupleType<I, T> {
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
        t: DeclarationStructType<I, T>,
    ) -> DeclarationStructType<I, T> {
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
                    ty: box self.fold_declaration_type(*m.ty),
                    ..m
                })
                .collect(),
            ..t
        }
    }

    fn fold_assignee(&mut self, a: TypedAssignee<I, T>) -> TypedAssignee<I, T> {
        fold_assignee(self, a)
    }

    fn fold_statement(&mut self, s: TypedStatement<I, T>) -> Vec<TypedStatement<I, T>> {
        fold_statement(self, s)
    }

    fn fold_definition_rhs(&mut self, rhs: DefinitionRhs<I, T>) -> DefinitionRhs<I, T> {
        fold_definition_rhs(self, rhs)
    }

    fn fold_embed_call(&mut self, e: EmbedCall<I, T>) -> EmbedCall<I, T> {
        fold_embed_call(self, e)
    }

    fn fold_expression_or_spread(
        &mut self,
        e: TypedExpressionOrSpread<I, T>,
    ) -> TypedExpressionOrSpread<I, T> {
        match e {
            TypedExpressionOrSpread::Expression(e) => {
                TypedExpressionOrSpread::Expression(self.fold_expression(e))
            }
            TypedExpressionOrSpread::Spread(s) => {
                TypedExpressionOrSpread::Spread(self.fold_spread(s))
            }
        }
    }

    fn fold_spread(&mut self, s: TypedSpread<I, T>) -> TypedSpread<I, T> {
        TypedSpread {
            array: self.fold_array_expression(s.array),
        }
    }

    fn fold_canonical_constant_identifier(
        &mut self,
        i: CanonicalConstantIdentifier<I>,
    ) -> CanonicalConstantIdentifier<I> {
        CanonicalConstantIdentifier {
            module: self.fold_module_id(i.module),
            id: i.id,
        }
    }

    fn fold_module_id(&mut self, i: OwnedTypedModuleId) -> OwnedTypedModuleId {
        i
    }

    fn fold_expression(&mut self, e: TypedExpression<I, T>) -> TypedExpression<I, T> {
        fold_expression(self, e)
    }

    fn fold_block_expression<E: Fold<I, T>>(
        &mut self,
        block: BlockExpression<I, T, E>,
    ) -> BlockExpression<I, T, E> {
        fold_block_expression(self, block)
    }

    fn fold_conditional_expression<
        E: Expr<I, T> + Fold<I, T> + Block<I, T> + Conditional<I, T> + From<TypedExpression<I, T>>,
    >(
        &mut self,
        ty: &E::Ty,
        e: ConditionalExpression<I, T, E>,
    ) -> ConditionalOrExpression<I, T, E> {
        fold_conditional_expression(self, ty, e)
    }

    fn fold_member_expression<E: Expr<I, T> + Member<I, T> + From<TypedExpression<I, T>>>(
        &mut self,
        ty: &E::Ty,
        e: MemberExpression<I, T, E>,
    ) -> MemberOrExpression<I, T, E> {
        fold_member_expression(self, ty, e)
    }

    fn fold_identifier_expression<E: Expr<I, T> + Id<I, T> + From<TypedExpression<I, T>>>(
        &mut self,
        ty: &E::Ty,
        e: IdentifierExpression<I, E>,
    ) -> IdentifierOrExpression<I, T, E> {
        fold_identifier_expression(self, ty, e)
    }

    fn fold_element_expression<E: Expr<I, T> + Element<I, T> + From<TypedExpression<I, T>>>(
        &mut self,
        ty: &E::Ty,
        e: ElementExpression<I, T, E>,
    ) -> ElementOrExpression<I, T, E> {
        fold_element_expression(self, ty, e)
    }

    fn fold_eq_expression<E: Expr<I, T> + PartialEq + Constant + Fold<I, T>>(
        &mut self,
        e: EqExpression<E>,
    ) -> EqOrBoolean<I, T, E> {
        fold_eq_expression(self, e)
    }

    fn fold_function_call_expression<
        E: Id<I, T> + From<TypedExpression<I, T>> + Expr<I, T> + FunctionCall<I, T>,
    >(
        &mut self,
        ty: &E::Ty,
        e: FunctionCallExpression<I, T, E>,
    ) -> FunctionCallOrExpression<I, T, E> {
        fold_function_call_expression(self, ty, e)
    }

    fn fold_select_expression<
        E: Expr<I, T> + Select<I, T> + Conditional<I, T> + From<TypedExpression<I, T>>,
    >(
        &mut self,
        ty: &E::Ty,
        e: SelectExpression<I, T, E>,
    ) -> SelectOrExpression<I, T, E> {
        fold_select_expression(self, ty, e)
    }

    fn fold_array_expression(&mut self, e: ArrayExpression<I, T>) -> ArrayExpression<I, T> {
        fold_array_expression(self, e)
    }

    fn fold_struct_expression(&mut self, e: StructExpression<I, T>) -> StructExpression<I, T> {
        fold_struct_expression(self, e)
    }

    fn fold_tuple_expression(&mut self, e: TupleExpression<I, T>) -> TupleExpression<I, T> {
        fold_tuple_expression(self, e)
    }

    fn fold_int_expression(&mut self, e: IntExpression<I, T>) -> IntExpression<I, T> {
        fold_int_expression(self, e)
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<I, T>,
    ) -> FieldElementExpression<I, T> {
        fold_field_expression(self, e)
    }

    fn fold_boolean_expression(&mut self, e: BooleanExpression<I, T>) -> BooleanExpression<I, T> {
        fold_boolean_expression(self, e)
    }

    fn fold_uint_expression(&mut self, e: UExpression<I, T>) -> UExpression<I, T> {
        fold_uint_expression(self, e)
    }

    fn fold_uint_expression_inner(
        &mut self,
        bitwidth: UBitwidth,
        e: UExpressionInner<I, T>,
    ) -> UExpressionInner<I, T> {
        fold_uint_expression_inner(self, bitwidth, e)
    }

    fn fold_array_expression_inner(
        &mut self,
        ty: &ArrayType<I, T>,
        e: ArrayExpressionInner<I, T>,
    ) -> ArrayExpressionInner<I, T> {
        fold_array_expression_inner(self, ty, e)
    }

    fn fold_tuple_expression_inner(
        &mut self,
        ty: &TupleType<I, T>,
        e: TupleExpressionInner<I, T>,
    ) -> TupleExpressionInner<I, T> {
        fold_tuple_expression_inner(self, ty, e)
    }

    fn fold_struct_expression_inner(
        &mut self,
        ty: &StructType<I, T>,
        e: StructExpressionInner<I, T>,
    ) -> StructExpressionInner<I, T> {
        fold_struct_expression_inner(self, ty, e)
    }
}

pub fn fold_module<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    m: TypedModule<I, T>,
) -> TypedModule<I, T> {
    TypedModule {
        symbols: m
            .symbols
            .into_iter()
            .map(|s| f.fold_symbol_declaration(s))
            .collect(),
    }
}

pub fn fold_symbol_declaration<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    d: TypedSymbolDeclaration<I, T>,
) -> TypedSymbolDeclaration<I, T> {
    match d {
        TypedSymbolDeclaration::Function(d) => {
            TypedSymbolDeclaration::Function(f.fold_function_symbol_declaration(d))
        }
        TypedSymbolDeclaration::Constant(d) => {
            TypedSymbolDeclaration::Constant(f.fold_constant_symbol_declaration(d))
        }
    }
}

pub fn fold_function_symbol_declaration<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    d: TypedFunctionSymbolDeclaration<I, T>,
) -> TypedFunctionSymbolDeclaration<I, T> {
    TypedFunctionSymbolDeclaration {
        key: f.fold_declaration_function_key(d.key),
        symbol: f.fold_function_symbol(d.symbol),
    }
}

pub fn fold_constant_symbol_declaration<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    d: TypedConstantSymbolDeclaration<I, T>,
) -> TypedConstantSymbolDeclaration<I, T> {
    TypedConstantSymbolDeclaration {
        id: f.fold_canonical_constant_identifier(d.id),
        symbol: f.fold_constant_symbol(d.symbol),
    }
}

pub fn fold_definition_rhs<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    rhs: DefinitionRhs<I, T>,
) -> DefinitionRhs<I, T> {
    match rhs {
        DefinitionRhs::EmbedCall(c) => DefinitionRhs::EmbedCall(f.fold_embed_call(c)),
        DefinitionRhs::Expression(e) => DefinitionRhs::Expression(f.fold_expression(e)),
    }
}

pub fn fold_statement<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    s: TypedStatement<I, T>,
) -> Vec<TypedStatement<I, T>> {
    let res = match s {
        TypedStatement::Return(e) => TypedStatement::Return(f.fold_expression(e)),
        TypedStatement::Definition(a, e) => {
            TypedStatement::Definition(f.fold_assignee(a), f.fold_definition_rhs(e))
        }
        TypedStatement::Assertion(e, error) => {
            TypedStatement::Assertion(f.fold_boolean_expression(e), error)
        }
        TypedStatement::For(v, from, to, statements) => TypedStatement::For(
            f.fold_variable(v),
            f.fold_uint_expression(from),
            f.fold_uint_expression(to),
            statements
                .into_iter()
                .flat_map(|s| f.fold_statement(s))
                .collect(),
        ),
        TypedStatement::Log(s, e) => {
            TypedStatement::Log(s, e.into_iter().map(|e| f.fold_expression(e)).collect())
        }
        s => s,
    };
    vec![res]
}

pub fn fold_identifier_expression<
    I: IdTrait,
    T: Field,
    E: Expr<I, T> + Id<I, T> + From<TypedExpression<I, T>>,
    F: Folder<I, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: IdentifierExpression<I, E>,
) -> IdentifierOrExpression<I, T, E> {
    IdentifierOrExpression::Identifier(IdentifierExpression::new(f.fold_name(e.id)))
}

pub fn fold_embed_call<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    e: EmbedCall<I, T>,
) -> EmbedCall<I, T> {
    EmbedCall {
        arguments: e
            .arguments
            .into_iter()
            .map(|s| f.fold_expression(s))
            .collect(),
        ..e
    }
}

pub fn fold_expression<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    e: TypedExpression<I, T>,
) -> TypedExpression<I, T> {
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

pub fn fold_array_expression_inner<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    ty: &ArrayType<I, T>,
    e: ArrayExpressionInner<I, T>,
) -> ArrayExpressionInner<I, T> {
    use ArrayExpressionInner::*;

    match e {
        Identifier(id) => match f.fold_identifier_expression(ty, id) {
            IdentifierOrExpression::Identifier(i) => ArrayExpressionInner::Identifier(i),
            IdentifierOrExpression::Expression(u) => u,
        },
        Block(block) => Block(f.fold_block_expression(block)),
        Value(exprs) => Value(
            exprs
                .into_iter()
                .map(|e| f.fold_expression_or_spread(e))
                .collect(),
        ),
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
        Slice(box array, box from, box to) => {
            let array = f.fold_array_expression(array);
            let from = f.fold_uint_expression(from);
            let to = f.fold_uint_expression(to);
            Slice(box array, box from, box to)
        }
        Repeat(box e, box count) => {
            let e = f.fold_expression(e);
            let count = f.fold_uint_expression(count);
            Repeat(box e, box count)
        }
        Element(m) => match f.fold_element_expression(ty, m) {
            ElementOrExpression::Element(m) => Element(m),
            ElementOrExpression::Expression(u) => u,
        },
    }
}

pub fn fold_struct_expression_inner<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    ty: &StructType<I, T>,
    e: StructExpressionInner<I, T>,
) -> StructExpressionInner<I, T> {
    use StructExpressionInner::*;

    match e {
        Identifier(id) => match f.fold_identifier_expression(ty, id) {
            IdentifierOrExpression::Identifier(i) => Identifier(i),
            IdentifierOrExpression::Expression(u) => u,
        },
        Block(block) => Block(f.fold_block_expression(block)),
        Value(exprs) => Value(exprs.into_iter().map(|e| f.fold_expression(e)).collect()),
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

pub fn fold_tuple_expression_inner<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    ty: &TupleType<I, T>,
    e: TupleExpressionInner<I, T>,
) -> TupleExpressionInner<I, T> {
    use TupleExpressionInner::*;

    match e {
        Block(block) => Block(f.fold_block_expression(block)),
        Identifier(id) => match f.fold_identifier_expression(ty, id) {
            IdentifierOrExpression::Identifier(i) => Identifier(i),
            IdentifierOrExpression::Expression(u) => u,
        },
        Value(exprs) => Value(exprs.into_iter().map(|e| f.fold_expression(e)).collect()),
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

pub fn fold_field_expression<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    e: FieldElementExpression<I, T>,
) -> FieldElementExpression<I, T> {
    use FieldElementExpression::*;

    match e {
        Identifier(id) => match f.fold_identifier_expression(&Type::FieldElement, id) {
            IdentifierOrExpression::Identifier(i) => Identifier(i),
            IdentifierOrExpression::Expression(u) => u,
        },
        Block(block) => Block(f.fold_block_expression(block)),
        Number(n) => Number(n),
        Add(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            Add(box e1, box e2)
        }
        Sub(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            Sub(box e1, box e2)
        }
        Mult(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            Mult(box e1, box e2)
        }
        Div(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            Div(box e1, box e2)
        }
        Pow(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_uint_expression(e2);
            Pow(box e1, box e2)
        }
        Neg(box e) => {
            let e = f.fold_field_expression(e);

            Neg(box e)
        }
        Pos(box e) => {
            let e = f.fold_field_expression(e);

            Pos(box e)
        }
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
    I: IdTrait,
    T: Field,
    E: Expr<I, T> + Fold<I, T> + Conditional<I, T> + From<TypedExpression<I, T>>,
    F: Folder<I, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: ConditionalExpression<I, T, E>,
) -> ConditionalOrExpression<I, T, E> {
    ConditionalOrExpression::Conditional(ConditionalExpression::new(
        f.fold_boolean_expression(*e.condition),
        e.consequence.fold(f),
        e.alternative.fold(f),
        e.kind,
    ))
}

pub fn fold_member_expression<
    I: IdTrait,
    T: Field,
    E: Expr<I, T> + Member<I, T> + From<TypedExpression<I, T>>,
    F: Folder<I, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: MemberExpression<I, T, E>,
) -> MemberOrExpression<I, T, E> {
    MemberOrExpression::Member(MemberExpression::new(
        f.fold_struct_expression(*e.struc),
        e.id,
    ))
}

pub fn fold_element_expression<
    I: IdTrait,
    T: Field,
    E: Expr<I, T> + Element<I, T> + From<TypedExpression<I, T>>,
    F: Folder<I, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: ElementExpression<I, T, E>,
) -> ElementOrExpression<I, T, E> {
    ElementOrExpression::Element(ElementExpression::new(
        f.fold_tuple_expression(*e.tuple),
        e.index,
    ))
}

pub fn fold_eq_expression<I: IdTrait, T: Field, E: Fold<I, T>, F: Folder<I, T>>(
    f: &mut F,
    e: EqExpression<E>,
) -> EqOrBoolean<I, T, E> {
    EqOrBoolean::Eq(EqExpression::new(e.left.fold(f), e.right.fold(f)))
}

pub fn fold_select_expression<
    I: IdTrait,
    T: Field,
    E: Expr<I, T> + Select<I, T> + Conditional<I, T> + From<TypedExpression<I, T>>,
    F: Folder<I, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: SelectExpression<I, T, E>,
) -> SelectOrExpression<I, T, E> {
    SelectOrExpression::Select(SelectExpression::new(
        f.fold_array_expression(*e.array),
        f.fold_uint_expression(*e.index),
    ))
}

pub fn fold_int_expression<I: IdTrait, T: Field, F: Folder<I, T>>(
    _: &mut F,
    _: IntExpression<I, T>,
) -> IntExpression<I, T> {
    unreachable!()
}

pub fn fold_boolean_expression<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    e: BooleanExpression<I, T>,
) -> BooleanExpression<I, T> {
    use BooleanExpression::*;

    match e {
        Identifier(id) => match f.fold_identifier_expression(&Type::Boolean, id) {
            IdentifierOrExpression::Identifier(i) => Identifier(i),
            IdentifierOrExpression::Expression(u) => u,
        },
        Block(block) => BooleanExpression::Block(f.fold_block_expression(block)),
        Value(v) => BooleanExpression::Value(v),
        FieldEq(e) => match f.fold_eq_expression(e) {
            EqOrBoolean::Eq(e) => BooleanExpression::FieldEq(e),
            EqOrBoolean::Boolean(u) => u,
        },
        BoolEq(e) => match f.fold_eq_expression(e) {
            EqOrBoolean::Eq(e) => BooleanExpression::BoolEq(e),
            EqOrBoolean::Boolean(u) => u,
        },
        ArrayEq(e) => match f.fold_eq_expression(e) {
            EqOrBoolean::Eq(e) => BooleanExpression::ArrayEq(e),
            EqOrBoolean::Boolean(u) => u,
        },
        StructEq(e) => match f.fold_eq_expression(e) {
            EqOrBoolean::Eq(e) => BooleanExpression::StructEq(e),
            EqOrBoolean::Boolean(u) => u,
        },
        TupleEq(e) => match f.fold_eq_expression(e) {
            EqOrBoolean::Eq(e) => BooleanExpression::TupleEq(e),
            EqOrBoolean::Boolean(u) => u,
        },
        UintEq(e) => match f.fold_eq_expression(e) {
            EqOrBoolean::Eq(e) => BooleanExpression::UintEq(e),
            EqOrBoolean::Boolean(u) => u,
        },
        FieldLt(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            FieldLt(box e1, box e2)
        }
        FieldLe(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            FieldLe(box e1, box e2)
        }
        FieldGt(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            FieldGt(box e1, box e2)
        }
        FieldGe(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            FieldGe(box e1, box e2)
        }
        UintLt(box e1, box e2) => {
            let e1 = f.fold_uint_expression(e1);
            let e2 = f.fold_uint_expression(e2);
            UintLt(box e1, box e2)
        }
        UintLe(box e1, box e2) => {
            let e1 = f.fold_uint_expression(e1);
            let e2 = f.fold_uint_expression(e2);
            UintLe(box e1, box e2)
        }
        UintGt(box e1, box e2) => {
            let e1 = f.fold_uint_expression(e1);
            let e2 = f.fold_uint_expression(e2);
            UintGt(box e1, box e2)
        }
        UintGe(box e1, box e2) => {
            let e1 = f.fold_uint_expression(e1);
            let e2 = f.fold_uint_expression(e2);
            UintGe(box e1, box e2)
        }
        Or(box e1, box e2) => {
            let e1 = f.fold_boolean_expression(e1);
            let e2 = f.fold_boolean_expression(e2);
            Or(box e1, box e2)
        }
        And(box e1, box e2) => {
            let e1 = f.fold_boolean_expression(e1);
            let e2 = f.fold_boolean_expression(e2);
            And(box e1, box e2)
        }
        Not(box e) => {
            let e = f.fold_boolean_expression(e);
            Not(box e)
        }
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

pub fn fold_uint_expression<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    e: UExpression<I, T>,
) -> UExpression<I, T> {
    UExpression {
        inner: f.fold_uint_expression_inner(e.bitwidth, e.inner),
        ..e
    }
}

pub fn fold_uint_expression_inner<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    ty: UBitwidth,
    e: UExpressionInner<I, T>,
) -> UExpressionInner<I, T> {
    use UExpressionInner::*;

    match e {
        Identifier(id) => match f.fold_identifier_expression(&ty, id) {
            IdentifierOrExpression::Identifier(i) => Identifier(i),
            IdentifierOrExpression::Expression(u) => u,
        },
        Block(block) => Block(f.fold_block_expression(block)),
        Value(v) => Value(v),
        Add(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            Add(box left, box right)
        }
        Sub(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            Sub(box left, box right)
        }
        FloorSub(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            FloorSub(box left, box right)
        }
        Mult(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            Mult(box left, box right)
        }
        Div(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            Div(box left, box right)
        }
        Rem(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            Rem(box left, box right)
        }
        Xor(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            Xor(box left, box right)
        }
        And(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            And(box left, box right)
        }
        Or(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            Or(box left, box right)
        }
        LeftShift(box e, box by) => {
            let e = f.fold_uint_expression(e);
            let by = f.fold_uint_expression(by);

            LeftShift(box e, box by)
        }
        RightShift(box e, box by) => {
            let e = f.fold_uint_expression(e);
            let by = f.fold_uint_expression(by);

            RightShift(box e, box by)
        }
        Not(box e) => {
            let e = f.fold_uint_expression(e);

            Not(box e)
        }
        Neg(box e) => {
            let e = f.fold_uint_expression(e);

            Neg(box e)
        }
        Pos(box e) => {
            let e = f.fold_uint_expression(e);

            Pos(box e)
        }
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

pub fn fold_block_expression<I: IdTrait, T: Field, E: Fold<I, T>, F: Folder<I, T>>(
    f: &mut F,
    block: BlockExpression<I, T, E>,
) -> BlockExpression<I, T, E> {
    BlockExpression {
        statements: block
            .statements
            .into_iter()
            .flat_map(|s| f.fold_statement(s))
            .collect(),
        value: box block.value.fold(f),
    }
}

pub fn fold_declaration_function_key<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    key: DeclarationFunctionKey<I, T>,
) -> DeclarationFunctionKey<I, T> {
    DeclarationFunctionKey {
        module: f.fold_module_id(key.module),
        signature: f.fold_signature(key.signature),
        ..key
    }
}

pub fn fold_function_call_expression<
    I: IdTrait,
    T: Field,
    E: Id<I, T> + From<TypedExpression<I, T>> + Expr<I, T> + FunctionCall<I, T>,
    F: Folder<I, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: FunctionCallExpression<I, T, E>,
) -> FunctionCallOrExpression<I, T, E> {
    FunctionCallOrExpression::FunctionCall(FunctionCallExpression::new(
        f.fold_declaration_function_key(e.function_key),
        e.generics
            .into_iter()
            .map(|g| g.map(|g| f.fold_uint_expression(g)))
            .collect(),
        e.arguments
            .into_iter()
            .map(|e| f.fold_expression(e))
            .collect(),
    ))
}

pub fn fold_function<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    fun: TypedFunction<I, T>,
) -> TypedFunction<I, T> {
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

fn fold_signature<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    s: DeclarationSignature<I, T>,
) -> DeclarationSignature<I, T> {
    DeclarationSignature {
        generics: s.generics,
        inputs: s
            .inputs
            .into_iter()
            .map(|o| f.fold_declaration_type(o))
            .collect(),
        output: box f.fold_declaration_type(*s.output),
    }
}

pub fn fold_declaration_constant<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    c: DeclarationConstant<I, T>,
) -> DeclarationConstant<I, T> {
    match c {
        DeclarationConstant::Expression(e) => DeclarationConstant::Expression(f.fold_expression(e)),
        DeclarationConstant::Constant(c) => {
            DeclarationConstant::Constant(f.fold_canonical_constant_identifier(c))
        }
        c => c,
    }
}

pub fn fold_array_expression<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    e: ArrayExpression<I, T>,
) -> ArrayExpression<I, T> {
    let ty = f.fold_array_type(*e.ty);

    ArrayExpression {
        inner: f.fold_array_expression_inner(&ty, e.inner),
        ty: box ty,
    }
}

pub fn fold_struct_expression<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    e: StructExpression<I, T>,
) -> StructExpression<I, T> {
    let ty = f.fold_struct_type(e.ty);
    StructExpression {
        inner: f.fold_struct_expression_inner(&ty, e.inner),
        ty,
    }
}

pub fn fold_tuple_expression<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    e: TupleExpression<I, T>,
) -> TupleExpression<I, T> {
    let ty = f.fold_tuple_type(e.ty);
    TupleExpression {
        inner: f.fold_tuple_expression_inner(&ty, e.inner),
        ty,
    }
}

pub fn fold_constant<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    c: TypedConstant<I, T>,
) -> TypedConstant<I, T> {
    TypedConstant {
        expression: f.fold_expression(c.expression),
        ty: f.fold_declaration_type(c.ty),
    }
}

pub fn fold_constant_symbol<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    s: TypedConstantSymbol<I, T>,
) -> TypedConstantSymbol<I, T> {
    match s {
        TypedConstantSymbol::Here(tc) => TypedConstantSymbol::Here(f.fold_constant(tc)),
        TypedConstantSymbol::There(id) => {
            TypedConstantSymbol::There(f.fold_canonical_constant_identifier(id))
        }
    }
}

pub fn fold_function_symbol<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    s: TypedFunctionSymbol<I, T>,
) -> TypedFunctionSymbol<I, T> {
    match s {
        TypedFunctionSymbol::Here(fun) => TypedFunctionSymbol::Here(f.fold_function(fun)),
        TypedFunctionSymbol::There(key) => {
            TypedFunctionSymbol::There(f.fold_declaration_function_key(key))
        }
        s => s,
    }
}

pub fn fold_assignee<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    a: TypedAssignee<I, T>,
) -> TypedAssignee<I, T> {
    match a {
        TypedAssignee::Identifier(v) => TypedAssignee::Identifier(f.fold_variable(v)),
        TypedAssignee::Select(box a, box index) => {
            TypedAssignee::Select(box f.fold_assignee(a), box f.fold_uint_expression(index))
        }
        TypedAssignee::Member(box s, m) => TypedAssignee::Member(box f.fold_assignee(s), m),
        TypedAssignee::Element(box s, index) => {
            TypedAssignee::Element(box f.fold_assignee(s), index)
        }
    }
}

pub fn fold_program<I: IdTrait, T: Field, F: Folder<I, T>>(
    f: &mut F,
    p: TypedProgram<I, T>,
) -> TypedProgram<I, T> {
    TypedProgram {
        modules: p
            .modules
            .into_iter()
            .map(|(module_id, module)| (f.fold_module_id(module_id), f.fold_module(module)))
            .collect(),
        main: f.fold_module_id(p.main),
    }
}
