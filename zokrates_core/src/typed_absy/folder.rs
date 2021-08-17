// Generic walk through a typed AST. Not mutating in place

use crate::typed_absy::types::*;
use crate::typed_absy::*;
use zokrates_field::Field;

pub trait Fold<'ast, T: Field>: Sized {
    fn fold<F: Folder<'ast, T>>(self, f: &mut F) -> Self;
}

impl<'ast, T: Field> Fold<'ast, T> for FieldElementExpression<'ast, T> {
    fn fold<F: Folder<'ast, T>>(self, f: &mut F) -> Self {
        f.fold_field_expression(self)
    }
}

impl<'ast, T: Field> Fold<'ast, T> for BooleanExpression<'ast, T> {
    fn fold<F: Folder<'ast, T>>(self, f: &mut F) -> Self {
        f.fold_boolean_expression(self)
    }
}

impl<'ast, T: Field> Fold<'ast, T> for UExpression<'ast, T> {
    fn fold<F: Folder<'ast, T>>(self, f: &mut F) -> Self {
        f.fold_uint_expression(self)
    }
}

impl<'ast, T: Field> Fold<'ast, T> for StructExpression<'ast, T> {
    fn fold<F: Folder<'ast, T>>(self, f: &mut F) -> Self {
        f.fold_struct_expression(self)
    }
}

impl<'ast, T: Field> Fold<'ast, T> for ArrayExpression<'ast, T> {
    fn fold<F: Folder<'ast, T>>(self, f: &mut F) -> Self {
        f.fold_array_expression(self)
    }
}

pub trait Folder<'ast, T: Field>: Sized {
    fn fold_program(&mut self, p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        fold_program(self, p)
    }

    fn fold_module(&mut self, m: TypedModule<'ast, T>) -> TypedModule<'ast, T> {
        fold_module(self, m)
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
        key: DeclarationFunctionKey<'ast>,
    ) -> DeclarationFunctionKey<'ast> {
        fold_declaration_function_key(self, key)
    }

    fn fold_function(&mut self, f: TypedFunction<'ast, T>) -> TypedFunction<'ast, T> {
        fold_function(self, f)
    }

    fn fold_signature(&mut self, s: DeclarationSignature<'ast>) -> DeclarationSignature<'ast> {
        fold_signature(self, s)
    }

    fn fold_declaration_constant(
        &mut self,
        c: DeclarationConstant<'ast>,
    ) -> DeclarationConstant<'ast> {
        fold_declaration_constant(self, c)
    }

    fn fold_parameter(&mut self, p: DeclarationParameter<'ast>) -> DeclarationParameter<'ast> {
        DeclarationParameter {
            id: self.fold_declaration_variable(p.id),
            ..p
        }
    }

    fn fold_name(&mut self, n: Identifier<'ast>) -> Identifier<'ast> {
        n
    }

    fn fold_variable(&mut self, v: Variable<'ast, T>) -> Variable<'ast, T> {
        Variable {
            id: self.fold_name(v.id),
            _type: self.fold_type(v._type),
        }
    }

    fn fold_declaration_variable(
        &mut self,
        v: DeclarationVariable<'ast>,
    ) -> DeclarationVariable<'ast> {
        DeclarationVariable {
            id: self.fold_name(v.id),
            _type: self.fold_declaration_type(v._type),
        }
    }

    fn fold_type(&mut self, t: Type<'ast, T>) -> Type<'ast, T> {
        use self::GType::*;

        match t {
            Array(array_type) => Array(self.fold_array_type(array_type)),
            Struct(struct_type) => Struct(self.fold_struct_type(struct_type)),
            t => t,
        }
    }

    fn fold_types(&mut self, tys: Types<'ast, T>) -> Types<'ast, T> {
        fold_types(self, tys)
    }

    fn fold_array_type(&mut self, t: ArrayType<'ast, T>) -> ArrayType<'ast, T> {
        ArrayType {
            ty: box self.fold_type(*t.ty),
            size: self.fold_uint_expression(t.size),
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
                    ty: box self.fold_type(*m.ty),
                    ..m
                })
                .collect(),
            ..t
        }
    }

    fn fold_declaration_type(&mut self, t: DeclarationType<'ast>) -> DeclarationType<'ast> {
        use self::GType::*;

        match t {
            Array(array_type) => Array(self.fold_declaration_array_type(array_type)),
            Struct(struct_type) => Struct(self.fold_declaration_struct_type(struct_type)),
            t => t,
        }
    }

    fn fold_declaration_array_type(
        &mut self,
        t: DeclarationArrayType<'ast>,
    ) -> DeclarationArrayType<'ast> {
        DeclarationArrayType {
            ty: box self.fold_declaration_type(*t.ty),
            size: self.fold_declaration_constant(t.size),
        }
    }

    fn fold_declaration_struct_type(
        &mut self,
        t: DeclarationStructType<'ast>,
    ) -> DeclarationStructType<'ast> {
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

    fn fold_assignee(&mut self, a: TypedAssignee<'ast, T>) -> TypedAssignee<'ast, T> {
        fold_assignee(self, a)
    }

    fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        fold_statement(self, s)
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
            ty: box self.fold_declaration_type(*i.ty),
        }
    }

    fn fold_module_id(&mut self, i: OwnedTypedModuleId) -> OwnedTypedModuleId {
        i
    }

    fn fold_expression(&mut self, e: TypedExpression<'ast, T>) -> TypedExpression<'ast, T> {
        match e {
            TypedExpression::FieldElement(e) => self.fold_field_expression(e).into(),
            TypedExpression::Boolean(e) => self.fold_boolean_expression(e).into(),
            TypedExpression::Uint(e) => self.fold_uint_expression(e).into(),
            TypedExpression::Array(e) => self.fold_array_expression(e).into(),
            TypedExpression::Struct(e) => self.fold_struct_expression(e).into(),
            TypedExpression::Int(e) => self.fold_int_expression(e).into(),
        }
    }

    fn fold_block_expression<E: Fold<'ast, T>>(
        &mut self,
        block: BlockExpression<'ast, T, E>,
    ) -> BlockExpression<'ast, T, E> {
        fold_block_expression(self, block)
    }

    fn fold_if_else_expression<
        E: Expr<'ast, T>
            + Fold<'ast, T>
            + Block<'ast, T>
            + IfElse<'ast, T>
            + From<TypedExpression<'ast, T>>,
    >(
        &mut self,
        ty: &E::Ty,
        e: IfElseExpression<'ast, T, E>,
    ) -> IfElseOrExpression<'ast, T, E> {
        fold_if_else_expression(self, ty, e)
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
        E: Expr<'ast, T> + Select<'ast, T> + IfElse<'ast, T> + From<TypedExpression<'ast, T>>,
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

    fn fold_expression_list(
        &mut self,
        es: TypedExpressionList<'ast, T>,
    ) -> TypedExpressionList<'ast, T> {
        fold_expression_list(self, es)
    }

    fn fold_expression_list_inner(
        &mut self,
        tys: Types<'ast, T>,
        es: TypedExpressionListInner<'ast, T>,
    ) -> TypedExpressionListInner<'ast, T> {
        fold_expression_list_inner(self, tys, es)
    }

    fn fold_int_expression(&mut self, e: IntExpression<'ast, T>) -> IntExpression<'ast, T> {
        fold_int_expression(self, e)
    }

    fn fold_field_expression(
        &mut self,
        e: FieldElementExpression<'ast, T>,
    ) -> FieldElementExpression<'ast, T> {
        fold_field_expression(self, e)
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

    fn fold_uint_expression_inner(
        &mut self,
        bitwidth: UBitwidth,
        e: UExpressionInner<'ast, T>,
    ) -> UExpressionInner<'ast, T> {
        fold_uint_expression_inner(self, bitwidth, e)
    }

    fn fold_array_expression_inner(
        &mut self,
        ty: &ArrayType<'ast, T>,
        e: ArrayExpressionInner<'ast, T>,
    ) -> ArrayExpressionInner<'ast, T> {
        fold_array_expression_inner(self, ty, e)
    }

    fn fold_struct_expression_inner(
        &mut self,
        ty: &StructType<'ast, T>,
        e: StructExpressionInner<'ast, T>,
    ) -> StructExpressionInner<'ast, T> {
        fold_struct_expression_inner(self, ty, e)
    }
}

pub fn fold_module<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    m: TypedModule<'ast, T>,
) -> TypedModule<'ast, T> {
    TypedModule {
        constants: m
            .constants
            .into_iter()
            .map(|(id, tc)| {
                (
                    f.fold_canonical_constant_identifier(id),
                    f.fold_constant_symbol(tc),
                )
            })
            .collect(),
        functions: m
            .functions
            .into_iter()
            .map(|(key, fun)| {
                (
                    f.fold_declaration_function_key(key),
                    f.fold_function_symbol(fun),
                )
            })
            .collect(),
    }
}

pub fn fold_statement<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    s: TypedStatement<'ast, T>,
) -> Vec<TypedStatement<'ast, T>> {
    let res = match s {
        TypedStatement::Return(expressions) => TypedStatement::Return(
            expressions
                .into_iter()
                .map(|e| f.fold_expression(e))
                .collect(),
        ),
        TypedStatement::Definition(a, e) => {
            TypedStatement::Definition(f.fold_assignee(a), f.fold_expression(e))
        }
        TypedStatement::Declaration(v) => TypedStatement::Declaration(f.fold_variable(v)),
        TypedStatement::Assertion(e) => TypedStatement::Assertion(f.fold_boolean_expression(e)),
        TypedStatement::For(v, from, to, statements) => TypedStatement::For(
            f.fold_variable(v),
            f.fold_uint_expression(from),
            f.fold_uint_expression(to),
            statements
                .into_iter()
                .flat_map(|s| f.fold_statement(s))
                .collect(),
        ),
        TypedStatement::MultipleDefinition(assignees, elist) => TypedStatement::MultipleDefinition(
            assignees.into_iter().map(|a| f.fold_assignee(a)).collect(),
            f.fold_expression_list(elist),
        ),
        s => s,
    };
    vec![res]
}

pub fn fold_array_expression_inner<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    ty: &ArrayType<'ast, T>,
    e: ArrayExpressionInner<'ast, T>,
) -> ArrayExpressionInner<'ast, T> {
    match e {
        ArrayExpressionInner::Block(block) => {
            ArrayExpressionInner::Block(f.fold_block_expression(block))
        }
        ArrayExpressionInner::Identifier(id) => ArrayExpressionInner::Identifier(f.fold_name(id)),
        ArrayExpressionInner::Value(exprs) => ArrayExpressionInner::Value(
            exprs
                .into_iter()
                .map(|e| f.fold_expression_or_spread(e))
                .collect(),
        ),
        ArrayExpressionInner::FunctionCall(function_call) => {
            match f.fold_function_call_expression(ty, function_call) {
                FunctionCallOrExpression::FunctionCall(function_call) => {
                    ArrayExpressionInner::FunctionCall(function_call)
                }
                FunctionCallOrExpression::Expression(u) => u,
            }
        }
        ArrayExpressionInner::IfElse(c) => match f.fold_if_else_expression(ty, c) {
            IfElseOrExpression::IfElse(s) => ArrayExpressionInner::IfElse(s),
            IfElseOrExpression::Expression(u) => u,
        },
        ArrayExpressionInner::Select(select) => match f.fold_select_expression(ty, select) {
            SelectOrExpression::Select(s) => ArrayExpressionInner::Select(s),
            SelectOrExpression::Expression(u) => u,
        },
        ArrayExpressionInner::Member(m) => match f.fold_member_expression(ty, m) {
            MemberOrExpression::Member(m) => ArrayExpressionInner::Member(m),
            MemberOrExpression::Expression(u) => u,
        },
        ArrayExpressionInner::Slice(box array, box from, box to) => {
            let array = f.fold_array_expression(array);
            let from = f.fold_uint_expression(from);
            let to = f.fold_uint_expression(to);
            ArrayExpressionInner::Slice(box array, box from, box to)
        }
        ArrayExpressionInner::Repeat(box e, box count) => {
            let e = f.fold_expression(e);
            let count = f.fold_uint_expression(count);
            ArrayExpressionInner::Repeat(box e, box count)
        }
    }
}

pub fn fold_struct_expression_inner<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    ty: &StructType<'ast, T>,
    e: StructExpressionInner<'ast, T>,
) -> StructExpressionInner<'ast, T> {
    match e {
        StructExpressionInner::Block(block) => {
            StructExpressionInner::Block(f.fold_block_expression(block))
        }
        StructExpressionInner::Identifier(id) => StructExpressionInner::Identifier(f.fold_name(id)),
        StructExpressionInner::Value(exprs) => {
            StructExpressionInner::Value(exprs.into_iter().map(|e| f.fold_expression(e)).collect())
        }
        StructExpressionInner::FunctionCall(function_call) => {
            match f.fold_function_call_expression(ty, function_call) {
                FunctionCallOrExpression::FunctionCall(function_call) => {
                    StructExpressionInner::FunctionCall(function_call)
                }
                FunctionCallOrExpression::Expression(u) => u,
            }
        }
        StructExpressionInner::IfElse(c) => match f.fold_if_else_expression(ty, c) {
            IfElseOrExpression::IfElse(s) => StructExpressionInner::IfElse(s),
            IfElseOrExpression::Expression(u) => u,
        },
        StructExpressionInner::Select(select) => match f.fold_select_expression(ty, select) {
            SelectOrExpression::Select(s) => StructExpressionInner::Select(s),
            SelectOrExpression::Expression(u) => u,
        },
        StructExpressionInner::Member(m) => match f.fold_member_expression(ty, m) {
            MemberOrExpression::Member(m) => StructExpressionInner::Member(m),
            MemberOrExpression::Expression(u) => u,
        },
    }
}

pub fn fold_field_expression<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: FieldElementExpression<'ast, T>,
) -> FieldElementExpression<'ast, T> {
    match e {
        FieldElementExpression::Block(block) => {
            FieldElementExpression::Block(f.fold_block_expression(block))
        }
        FieldElementExpression::Number(n) => FieldElementExpression::Number(n),
        FieldElementExpression::Identifier(id) => {
            FieldElementExpression::Identifier(f.fold_name(id))
        }
        FieldElementExpression::Add(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            FieldElementExpression::Add(box e1, box e2)
        }
        FieldElementExpression::Sub(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            FieldElementExpression::Sub(box e1, box e2)
        }
        FieldElementExpression::Mult(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            FieldElementExpression::Mult(box e1, box e2)
        }
        FieldElementExpression::Div(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            FieldElementExpression::Div(box e1, box e2)
        }
        FieldElementExpression::Pow(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_uint_expression(e2);
            FieldElementExpression::Pow(box e1, box e2)
        }
        FieldElementExpression::Neg(box e) => {
            let e = f.fold_field_expression(e);

            FieldElementExpression::Neg(box e)
        }
        FieldElementExpression::Pos(box e) => {
            let e = f.fold_field_expression(e);

            FieldElementExpression::Pos(box e)
        }
        FieldElementExpression::IfElse(c) => {
            match f.fold_if_else_expression(&Type::FieldElement, c) {
                IfElseOrExpression::IfElse(s) => FieldElementExpression::IfElse(s),
                IfElseOrExpression::Expression(u) => u,
            }
        }
        FieldElementExpression::FunctionCall(function_call) => {
            match f.fold_function_call_expression(&Type::FieldElement, function_call) {
                FunctionCallOrExpression::FunctionCall(function_call) => {
                    FieldElementExpression::FunctionCall(function_call)
                }
                FunctionCallOrExpression::Expression(u) => u,
            }
        }
        FieldElementExpression::Select(select) => {
            match f.fold_select_expression(&Type::FieldElement, select) {
                SelectOrExpression::Select(s) => FieldElementExpression::Select(s),
                SelectOrExpression::Expression(u) => u,
            }
        }
        FieldElementExpression::Member(m) => match f.fold_member_expression(&Type::FieldElement, m)
        {
            MemberOrExpression::Member(m) => FieldElementExpression::Member(m),
            MemberOrExpression::Expression(u) => u,
        },
    }
}

pub fn fold_if_else_expression<
    'ast,
    T: Field,
    E: Expr<'ast, T> + Fold<'ast, T> + IfElse<'ast, T> + From<TypedExpression<'ast, T>>,
    F: Folder<'ast, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: IfElseExpression<'ast, T, E>,
) -> IfElseOrExpression<'ast, T, E> {
    IfElseOrExpression::IfElse(IfElseExpression::new(
        f.fold_boolean_expression(*e.condition),
        e.consequence.fold(f),
        e.alternative.fold(f),
    ))
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

pub fn fold_select_expression<
    'ast,
    T: Field,
    E: Expr<'ast, T> + Select<'ast, T> + IfElse<'ast, T> + From<TypedExpression<'ast, T>>,
    F: Folder<'ast, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: SelectExpression<'ast, T, E>,
) -> SelectOrExpression<'ast, T, E> {
    SelectOrExpression::Select(SelectExpression::new(
        f.fold_array_expression(*e.array),
        f.fold_uint_expression(*e.index),
    ))
}

pub fn fold_int_expression<'ast, T: Field, F: Folder<'ast, T>>(
    _: &mut F,
    _: IntExpression<'ast, T>,
) -> IntExpression<'ast, T> {
    unreachable!()
}

pub fn fold_boolean_expression<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: BooleanExpression<'ast, T>,
) -> BooleanExpression<'ast, T> {
    match e {
        BooleanExpression::Block(block) => BooleanExpression::Block(f.fold_block_expression(block)),
        BooleanExpression::Value(v) => BooleanExpression::Value(v),
        BooleanExpression::Identifier(id) => BooleanExpression::Identifier(f.fold_name(id)),
        BooleanExpression::FieldEq(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            BooleanExpression::FieldEq(box e1, box e2)
        }
        BooleanExpression::BoolEq(box e1, box e2) => {
            let e1 = f.fold_boolean_expression(e1);
            let e2 = f.fold_boolean_expression(e2);
            BooleanExpression::BoolEq(box e1, box e2)
        }
        BooleanExpression::ArrayEq(box e1, box e2) => {
            let e1 = f.fold_array_expression(e1);
            let e2 = f.fold_array_expression(e2);
            BooleanExpression::ArrayEq(box e1, box e2)
        }
        BooleanExpression::StructEq(box e1, box e2) => {
            let e1 = f.fold_struct_expression(e1);
            let e2 = f.fold_struct_expression(e2);
            BooleanExpression::StructEq(box e1, box e2)
        }
        BooleanExpression::UintEq(box e1, box e2) => {
            let e1 = f.fold_uint_expression(e1);
            let e2 = f.fold_uint_expression(e2);
            BooleanExpression::UintEq(box e1, box e2)
        }
        BooleanExpression::FieldLt(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            BooleanExpression::FieldLt(box e1, box e2)
        }
        BooleanExpression::FieldLe(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            BooleanExpression::FieldLe(box e1, box e2)
        }
        BooleanExpression::FieldGt(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            BooleanExpression::FieldGt(box e1, box e2)
        }
        BooleanExpression::FieldGe(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1);
            let e2 = f.fold_field_expression(e2);
            BooleanExpression::FieldGe(box e1, box e2)
        }
        BooleanExpression::UintLt(box e1, box e2) => {
            let e1 = f.fold_uint_expression(e1);
            let e2 = f.fold_uint_expression(e2);
            BooleanExpression::UintLt(box e1, box e2)
        }
        BooleanExpression::UintLe(box e1, box e2) => {
            let e1 = f.fold_uint_expression(e1);
            let e2 = f.fold_uint_expression(e2);
            BooleanExpression::UintLe(box e1, box e2)
        }
        BooleanExpression::UintGt(box e1, box e2) => {
            let e1 = f.fold_uint_expression(e1);
            let e2 = f.fold_uint_expression(e2);
            BooleanExpression::UintGt(box e1, box e2)
        }
        BooleanExpression::UintGe(box e1, box e2) => {
            let e1 = f.fold_uint_expression(e1);
            let e2 = f.fold_uint_expression(e2);
            BooleanExpression::UintGe(box e1, box e2)
        }
        BooleanExpression::Or(box e1, box e2) => {
            let e1 = f.fold_boolean_expression(e1);
            let e2 = f.fold_boolean_expression(e2);
            BooleanExpression::Or(box e1, box e2)
        }
        BooleanExpression::And(box e1, box e2) => {
            let e1 = f.fold_boolean_expression(e1);
            let e2 = f.fold_boolean_expression(e2);
            BooleanExpression::And(box e1, box e2)
        }
        BooleanExpression::Not(box e) => {
            let e = f.fold_boolean_expression(e);
            BooleanExpression::Not(box e)
        }
        BooleanExpression::FunctionCall(function_call) => {
            match f.fold_function_call_expression(&Type::Boolean, function_call) {
                FunctionCallOrExpression::FunctionCall(function_call) => {
                    BooleanExpression::FunctionCall(function_call)
                }
                FunctionCallOrExpression::Expression(u) => u,
            }
        }
        BooleanExpression::IfElse(c) => match f.fold_if_else_expression(&Type::Boolean, c) {
            IfElseOrExpression::IfElse(s) => BooleanExpression::IfElse(s),
            IfElseOrExpression::Expression(u) => u,
        },
        BooleanExpression::Select(select) => match f.fold_select_expression(&Type::Boolean, select)
        {
            SelectOrExpression::Select(s) => BooleanExpression::Select(s),
            SelectOrExpression::Expression(u) => u,
        },
        BooleanExpression::Member(m) => match f.fold_member_expression(&Type::Boolean, m) {
            MemberOrExpression::Member(m) => BooleanExpression::Member(m),
            MemberOrExpression::Expression(u) => u,
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

pub fn fold_uint_expression_inner<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    ty: UBitwidth,
    e: UExpressionInner<'ast, T>,
) -> UExpressionInner<'ast, T> {
    match e {
        UExpressionInner::Block(block) => UExpressionInner::Block(f.fold_block_expression(block)),
        UExpressionInner::Value(v) => UExpressionInner::Value(v),
        UExpressionInner::Identifier(id) => UExpressionInner::Identifier(f.fold_name(id)),
        UExpressionInner::Add(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            UExpressionInner::Add(box left, box right)
        }
        UExpressionInner::Sub(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            UExpressionInner::Sub(box left, box right)
        }
        UExpressionInner::FloorSub(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            UExpressionInner::FloorSub(box left, box right)
        }
        UExpressionInner::Mult(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            UExpressionInner::Mult(box left, box right)
        }
        UExpressionInner::Div(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            UExpressionInner::Div(box left, box right)
        }
        UExpressionInner::Rem(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            UExpressionInner::Rem(box left, box right)
        }
        UExpressionInner::Xor(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            UExpressionInner::Xor(box left, box right)
        }
        UExpressionInner::And(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            UExpressionInner::And(box left, box right)
        }
        UExpressionInner::Or(box left, box right) => {
            let left = f.fold_uint_expression(left);
            let right = f.fold_uint_expression(right);

            UExpressionInner::Or(box left, box right)
        }
        UExpressionInner::LeftShift(box e, box by) => {
            let e = f.fold_uint_expression(e);
            let by = f.fold_uint_expression(by);

            UExpressionInner::LeftShift(box e, box by)
        }
        UExpressionInner::RightShift(box e, box by) => {
            let e = f.fold_uint_expression(e);
            let by = f.fold_uint_expression(by);

            UExpressionInner::RightShift(box e, box by)
        }
        UExpressionInner::Not(box e) => {
            let e = f.fold_uint_expression(e);

            UExpressionInner::Not(box e)
        }
        UExpressionInner::Neg(box e) => {
            let e = f.fold_uint_expression(e);

            UExpressionInner::Neg(box e)
        }
        UExpressionInner::Pos(box e) => {
            let e = f.fold_uint_expression(e);

            UExpressionInner::Pos(box e)
        }
        UExpressionInner::FunctionCall(function_call) => {
            match f.fold_function_call_expression(&ty, function_call) {
                FunctionCallOrExpression::FunctionCall(function_call) => {
                    UExpressionInner::FunctionCall(function_call)
                }
                FunctionCallOrExpression::Expression(u) => u,
            }
        }
        UExpressionInner::Select(select) => match f.fold_select_expression(&ty, select) {
            SelectOrExpression::Select(s) => UExpressionInner::Select(s),
            SelectOrExpression::Expression(u) => u,
        },
        UExpressionInner::IfElse(c) => match f.fold_if_else_expression(&ty, c) {
            IfElseOrExpression::IfElse(s) => UExpressionInner::IfElse(s),
            IfElseOrExpression::Expression(u) => u,
        },
        UExpressionInner::Member(m) => match f.fold_member_expression(&ty, m) {
            MemberOrExpression::Member(m) => UExpressionInner::Member(m),
            MemberOrExpression::Expression(u) => u,
        },
    }
}

pub fn fold_block_expression<'ast, T: Field, E: Fold<'ast, T>, F: Folder<'ast, T>>(
    f: &mut F,
    block: BlockExpression<'ast, T, E>,
) -> BlockExpression<'ast, T, E> {
    BlockExpression {
        statements: block
            .statements
            .into_iter()
            .flat_map(|s| f.fold_statement(s))
            .collect(),
        value: box block.value.fold(f),
    }
}

pub fn fold_declaration_function_key<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    key: DeclarationFunctionKey<'ast>,
) -> DeclarationFunctionKey<'ast> {
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
    s: DeclarationSignature<'ast>,
) -> DeclarationSignature<'ast> {
    DeclarationSignature {
        generics: s.generics,
        inputs: s
            .inputs
            .into_iter()
            .map(|o| f.fold_declaration_type(o))
            .collect(),
        outputs: s
            .outputs
            .into_iter()
            .map(|o| f.fold_declaration_type(o))
            .collect(),
    }
}

fn fold_declaration_constant<'ast, T: Field, F: Folder<'ast, T>>(
    _: &mut F,
    c: DeclarationConstant<'ast>,
) -> DeclarationConstant<'ast> {
    c
}

pub fn fold_array_expression<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    e: ArrayExpression<'ast, T>,
) -> ArrayExpression<'ast, T> {
    let ty = f.fold_array_type(*e.ty);

    ArrayExpression {
        inner: f.fold_array_expression_inner(&ty, e.inner),
        ty: box ty,
    }
}

pub fn fold_expression_list<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    es: TypedExpressionList<'ast, T>,
) -> TypedExpressionList<'ast, T> {
    let types = f.fold_types(es.types);

    TypedExpressionList {
        inner: f.fold_expression_list_inner(types.clone(), es.inner),
        types,
    }
}

pub fn fold_types<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    tys: Types<'ast, T>,
) -> Types<'ast, T> {
    Types {
        inner: tys.inner.into_iter().map(|t| f.fold_type(t)).collect(),
    }
}

pub fn fold_expression_list_inner<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    tys: Types<'ast, T>,
    es: TypedExpressionListInner<'ast, T>,
) -> TypedExpressionListInner<'ast, T> {
    match es {
        TypedExpressionListInner::FunctionCall(function_call) => {
            match f.fold_function_call_expression(&tys, function_call) {
                FunctionCallOrExpression::FunctionCall(function_call) => {
                    TypedExpressionListInner::FunctionCall(function_call)
                }
                FunctionCallOrExpression::Expression(u) => u,
            }
        }
        TypedExpressionListInner::EmbedCall(embed, generics, arguments) => {
            TypedExpressionListInner::EmbedCall(
                embed,
                generics,
                arguments
                    .into_iter()
                    .map(|a| f.fold_expression(a))
                    .collect(),
            )
        }
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

pub fn fold_constant<'ast, T: Field, F: Folder<'ast, T>>(
    f: &mut F,
    c: TypedConstant<'ast, T>,
) -> TypedConstant<'ast, T> {
    TypedConstant {
        expression: f.fold_expression(c.expression),
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
        TypedAssignee::Select(box a, box index) => {
            TypedAssignee::Select(box f.fold_assignee(a), box f.fold_uint_expression(index))
        }
        TypedAssignee::Member(box s, m) => TypedAssignee::Member(box f.fold_assignee(s), m),
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
    }
}
