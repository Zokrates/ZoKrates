// Generic walk through a typed AST. Not mutating in place

use crate::typed_absy::types::*;
use crate::typed_absy::*;
use zokrates_field::Field;

pub trait ResultFold<'ast, T: Field>: Sized {
    fn fold<F: ResultFolder<'ast, T>>(self, f: &mut F) -> Result<Self, F::Error>;
}

impl<'ast, T: Field> ResultFold<'ast, T> for FieldElementExpression<'ast, T> {
    fn fold<F: ResultFolder<'ast, T>>(self, f: &mut F) -> Result<Self, F::Error> {
        f.fold_field_expression(self)
    }
}

impl<'ast, T: Field> ResultFold<'ast, T> for BooleanExpression<'ast, T> {
    fn fold<F: ResultFolder<'ast, T>>(self, f: &mut F) -> Result<Self, F::Error> {
        f.fold_boolean_expression(self)
    }
}

impl<'ast, T: Field> ResultFold<'ast, T> for UExpression<'ast, T> {
    fn fold<F: ResultFolder<'ast, T>>(self, f: &mut F) -> Result<Self, F::Error> {
        f.fold_uint_expression(self)
    }
}

impl<'ast, T: Field> ResultFold<'ast, T> for ArrayExpression<'ast, T> {
    fn fold<F: ResultFolder<'ast, T>>(self, f: &mut F) -> Result<Self, F::Error> {
        f.fold_array_expression(self)
    }
}

impl<'ast, T: Field> ResultFold<'ast, T> for StructExpression<'ast, T> {
    fn fold<F: ResultFolder<'ast, T>>(self, f: &mut F) -> Result<Self, F::Error> {
        f.fold_struct_expression(self)
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
        key: DeclarationFunctionKey<'ast>,
    ) -> Result<DeclarationFunctionKey<'ast>, Self::Error> {
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
        s: DeclarationSignature<'ast>,
    ) -> Result<DeclarationSignature<'ast>, Self::Error> {
        fold_signature(self, s)
    }

    fn fold_declaration_constant(
        &mut self,
        c: DeclarationConstant<'ast>,
    ) -> Result<DeclarationConstant<'ast>, Self::Error> {
        fold_declaration_constant(self, c)
    }

    fn fold_parameter(
        &mut self,
        p: DeclarationParameter<'ast>,
    ) -> Result<DeclarationParameter<'ast>, Self::Error> {
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
            ty: box self.fold_declaration_type(*i.ty)?,
        })
    }

    fn fold_module_id(&mut self, i: OwnedTypedModuleId) -> Result<OwnedTypedModuleId, Self::Error> {
        Ok(i)
    }

    fn fold_name(&mut self, n: Identifier<'ast>) -> Result<Identifier<'ast>, Self::Error> {
        Ok(n)
    }

    fn fold_variable(&mut self, v: Variable<'ast, T>) -> Result<Variable<'ast, T>, Self::Error> {
        Ok(Variable {
            id: self.fold_name(v.id)?,
            _type: self.fold_type(v._type)?,
        })
    }

    fn fold_declaration_variable(
        &mut self,
        v: DeclarationVariable<'ast>,
    ) -> Result<DeclarationVariable<'ast>, Self::Error> {
        Ok(DeclarationVariable {
            id: self.fold_name(v.id)?,
            _type: self.fold_declaration_type(v._type)?,
        })
    }

    fn fold_type(&mut self, t: Type<'ast, T>) -> Result<Type<'ast, T>, Self::Error> {
        use self::GType::*;

        match t {
            Array(array_type) => Ok(Array(self.fold_array_type(array_type)?)),
            Struct(struct_type) => Ok(Struct(self.fold_struct_type(struct_type)?)),
            t => Ok(t),
        }
    }

    fn fold_types(&mut self, tys: Types<'ast, T>) -> Result<Types<'ast, T>, Self::Error> {
        fold_types(self, tys)
    }

    fn fold_if_else_expression<
        E: Expr<'ast, T> + PartialEq + IfElse<'ast, T> + ResultFold<'ast, T>,
    >(
        &mut self,
        ty: &E::Ty,
        e: IfElseExpression<'ast, T, E>,
    ) -> Result<IfElseOrExpression<'ast, T, E>, Self::Error> {
        fold_if_else_expression(self, ty, e)
    }

    fn fold_block_expression<E: ResultFold<'ast, T>>(
        &mut self,
        block: BlockExpression<'ast, T, E>,
    ) -> Result<BlockExpression<'ast, T, E>, Self::Error> {
        fold_block_expression(self, block)
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

    fn fold_select_expression<
        E: Expr<'ast, T> + Select<'ast, T> + From<TypedExpression<'ast, T>>,
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
            ty: box self.fold_type(*t.ty)?,
            size: self.fold_uint_expression(t.size)?,
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
                    self.fold_type(*m.ty)
                        .map(|ty| StructMember { ty: box ty, id })
                })
                .collect::<Result<_, _>>()?,
            ..t
        })
    }

    fn fold_declaration_type(
        &mut self,
        t: DeclarationType<'ast>,
    ) -> Result<DeclarationType<'ast>, Self::Error> {
        Ok(t)
    }

    fn fold_declaration_array_type(
        &mut self,
        t: DeclarationArrayType<'ast>,
    ) -> Result<DeclarationArrayType<'ast>, Self::Error> {
        Ok(DeclarationArrayType {
            ty: box self.fold_declaration_type(*t.ty)?,
            size: self.fold_declaration_constant(t.size)?,
        })
    }

    fn fold_declaration_struct_type(
        &mut self,
        t: DeclarationStructType<'ast>,
    ) -> Result<DeclarationStructType<'ast>, Self::Error> {
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
                        .map(|ty| DeclarationStructMember { ty: box ty, id })
                })
                .collect::<Result<_, _>>()?,
            ..t
        })
    }

    fn fold_assignee(
        &mut self,
        a: TypedAssignee<'ast, T>,
    ) -> Result<TypedAssignee<'ast, T>, Self::Error> {
        match a {
            TypedAssignee::Identifier(v) => Ok(TypedAssignee::Identifier(self.fold_variable(v)?)),
            TypedAssignee::Select(box a, box index) => Ok(TypedAssignee::Select(
                box self.fold_assignee(a)?,
                box self.fold_uint_expression(index)?,
            )),
            TypedAssignee::Member(box s, m) => {
                Ok(TypedAssignee::Member(box self.fold_assignee(s)?, m))
            }
        }
    }

    fn fold_statement(
        &mut self,
        s: TypedStatement<'ast, T>,
    ) -> Result<Vec<TypedStatement<'ast, T>>, Self::Error> {
        fold_statement(self, s)
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
        match e {
            TypedExpression::FieldElement(e) => Ok(self.fold_field_expression(e)?.into()),
            TypedExpression::Boolean(e) => Ok(self.fold_boolean_expression(e)?.into()),
            TypedExpression::Uint(e) => Ok(self.fold_uint_expression(e)?.into()),
            TypedExpression::Array(e) => Ok(self.fold_array_expression(e)?.into()),
            TypedExpression::Struct(e) => Ok(self.fold_struct_expression(e)?.into()),
            TypedExpression::Int(e) => Ok(self.fold_int_expression(e)?.into()),
        }
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

    fn fold_expression_list_inner(
        &mut self,
        tys: &Types<'ast, T>,
        es: TypedExpressionListInner<'ast, T>,
    ) -> Result<TypedExpressionListInner<'ast, T>, Self::Error> {
        fold_expression_list_inner(self, tys, es)
    }

    fn fold_expression_list(
        &mut self,
        es: TypedExpressionList<'ast, T>,
    ) -> Result<TypedExpressionList<'ast, T>, Self::Error> {
        fold_expression_list(self, es)
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
    fn fold_boolean_expression(
        &mut self,
        e: BooleanExpression<'ast, T>,
    ) -> Result<BooleanExpression<'ast, T>, Self::Error> {
        fold_boolean_expression(self, e)
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

    fn fold_array_expression_inner(
        &mut self,
        ty: &ArrayType<'ast, T>,
        e: ArrayExpressionInner<'ast, T>,
    ) -> Result<ArrayExpressionInner<'ast, T>, Self::Error> {
        fold_array_expression_inner(self, ty, e)
    }
    fn fold_struct_expression_inner(
        &mut self,
        ty: &StructType<'ast, T>,
        e: StructExpressionInner<'ast, T>,
    ) -> Result<StructExpressionInner<'ast, T>, Self::Error> {
        fold_struct_expression_inner(self, ty, e)
    }
}

pub fn fold_statement<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    s: TypedStatement<'ast, T>,
) -> Result<Vec<TypedStatement<'ast, T>>, F::Error> {
    let res = match s {
        TypedStatement::Return(expressions) => TypedStatement::Return(
            expressions
                .into_iter()
                .map(|e| f.fold_expression(e))
                .collect::<Result<_, _>>()?,
        ),
        TypedStatement::Definition(a, e) => {
            TypedStatement::Definition(f.fold_assignee(a)?, f.fold_expression(e)?)
        }
        TypedStatement::Declaration(v) => TypedStatement::Declaration(f.fold_variable(v)?),
        TypedStatement::Assertion(e) => TypedStatement::Assertion(f.fold_boolean_expression(e)?),
        TypedStatement::For(v, from, to, statements) => TypedStatement::For(
            f.fold_variable(v)?,
            f.fold_uint_expression(from)?,
            f.fold_uint_expression(to)?,
            statements
                .into_iter()
                .map(|s| f.fold_statement(s))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .flatten()
                .collect(),
        ),
        TypedStatement::MultipleDefinition(variables, elist) => TypedStatement::MultipleDefinition(
            variables
                .into_iter()
                .map(|v| f.fold_assignee(v))
                .collect::<Result<_, _>>()?,
            f.fold_expression_list(elist)?,
        ),
        s => s,
    };
    Ok(vec![res])
}

pub fn fold_array_expression_inner<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    ty: &ArrayType<'ast, T>,
    e: ArrayExpressionInner<'ast, T>,
) -> Result<ArrayExpressionInner<'ast, T>, F::Error> {
    let e = match e {
        ArrayExpressionInner::Block(block) => {
            ArrayExpressionInner::Block(f.fold_block_expression(block)?)
        }
        ArrayExpressionInner::Identifier(id) => ArrayExpressionInner::Identifier(f.fold_name(id)?),
        ArrayExpressionInner::Value(exprs) => ArrayExpressionInner::Value(
            exprs
                .into_iter()
                .map(|e| f.fold_expression_or_spread(e))
                .collect::<Result<_, _>>()?,
        ),
        ArrayExpressionInner::FunctionCall(function_call) => {
            match f.fold_function_call_expression(ty, function_call)? {
                FunctionCallOrExpression::FunctionCall(c) => ArrayExpressionInner::FunctionCall(c),
                FunctionCallOrExpression::Expression(u) => u,
            }
        }
        ArrayExpressionInner::IfElse(c) => match f.fold_if_else_expression(ty, c)? {
            IfElseOrExpression::IfElse(c) => ArrayExpressionInner::IfElse(c),
            IfElseOrExpression::Expression(u) => u,
        },
        ArrayExpressionInner::Member(m) => match f.fold_member_expression(ty, m)? {
            MemberOrExpression::Member(m) => ArrayExpressionInner::Member(m),
            MemberOrExpression::Expression(u) => u,
        },
        ArrayExpressionInner::Select(select) => match f.fold_select_expression(ty, select)? {
            SelectOrExpression::Select(m) => ArrayExpressionInner::Select(m),
            SelectOrExpression::Expression(u) => u,
        },
        ArrayExpressionInner::Slice(box array, box from, box to) => {
            let array = f.fold_array_expression(array)?;
            let from = f.fold_uint_expression(from)?;
            let to = f.fold_uint_expression(to)?;
            ArrayExpressionInner::Slice(box array, box from, box to)
        }
        ArrayExpressionInner::Repeat(box e, box count) => {
            let e = f.fold_expression(e)?;
            let count = f.fold_uint_expression(count)?;
            ArrayExpressionInner::Repeat(box e, box count)
        }
    };
    Ok(e)
}

pub fn fold_struct_expression_inner<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    ty: &StructType<'ast, T>,
    e: StructExpressionInner<'ast, T>,
) -> Result<StructExpressionInner<'ast, T>, F::Error> {
    let e = match e {
        StructExpressionInner::Block(block) => {
            StructExpressionInner::Block(f.fold_block_expression(block)?)
        }
        StructExpressionInner::Identifier(id) => {
            StructExpressionInner::Identifier(f.fold_name(id)?)
        }
        StructExpressionInner::Value(exprs) => StructExpressionInner::Value(
            exprs
                .into_iter()
                .map(|e| f.fold_expression(e))
                .collect::<Result<_, _>>()?,
        ),
        StructExpressionInner::FunctionCall(function_call) => {
            match f.fold_function_call_expression(ty, function_call)? {
                FunctionCallOrExpression::FunctionCall(c) => StructExpressionInner::FunctionCall(c),
                FunctionCallOrExpression::Expression(u) => u,
            }
        }
        StructExpressionInner::IfElse(c) => match f.fold_if_else_expression(ty, c)? {
            IfElseOrExpression::IfElse(c) => StructExpressionInner::IfElse(c),
            IfElseOrExpression::Expression(u) => u,
        },
        StructExpressionInner::Member(m) => match f.fold_member_expression(ty, m)? {
            MemberOrExpression::Member(m) => StructExpressionInner::Member(m),
            MemberOrExpression::Expression(u) => u,
        },
        StructExpressionInner::Select(select) => match f.fold_select_expression(ty, select)? {
            SelectOrExpression::Select(m) => StructExpressionInner::Select(m),
            SelectOrExpression::Expression(u) => u,
        },
    };
    Ok(e)
}

pub fn fold_field_expression<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    e: FieldElementExpression<'ast, T>,
) -> Result<FieldElementExpression<'ast, T>, F::Error> {
    let e = match e {
        FieldElementExpression::Block(block) => {
            FieldElementExpression::Block(f.fold_block_expression(block)?)
        }
        FieldElementExpression::Number(n) => FieldElementExpression::Number(n),
        FieldElementExpression::Identifier(id) => {
            FieldElementExpression::Identifier(f.fold_name(id)?)
        }
        FieldElementExpression::Add(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1)?;
            let e2 = f.fold_field_expression(e2)?;
            FieldElementExpression::Add(box e1, box e2)
        }
        FieldElementExpression::Sub(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1)?;
            let e2 = f.fold_field_expression(e2)?;
            FieldElementExpression::Sub(box e1, box e2)
        }
        FieldElementExpression::Mult(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1)?;
            let e2 = f.fold_field_expression(e2)?;
            FieldElementExpression::Mult(box e1, box e2)
        }
        FieldElementExpression::Div(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1)?;
            let e2 = f.fold_field_expression(e2)?;
            FieldElementExpression::Div(box e1, box e2)
        }
        FieldElementExpression::Pow(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1)?;
            let e2 = f.fold_uint_expression(e2)?;
            FieldElementExpression::Pow(box e1, box e2)
        }
        FieldElementExpression::Neg(box e) => {
            let e = f.fold_field_expression(e)?;

            FieldElementExpression::Neg(box e)
        }
        FieldElementExpression::Pos(box e) => {
            let e = f.fold_field_expression(e)?;

            FieldElementExpression::Pos(box e)
        }
        FieldElementExpression::IfElse(c) => {
            match f.fold_if_else_expression(&Type::FieldElement, c)? {
                IfElseOrExpression::IfElse(c) => FieldElementExpression::IfElse(c),
                IfElseOrExpression::Expression(u) => u,
            }
        }
        FieldElementExpression::FunctionCall(function_call) => {
            match f.fold_function_call_expression(&Type::FieldElement, function_call)? {
                FunctionCallOrExpression::FunctionCall(c) => {
                    FieldElementExpression::FunctionCall(c)
                }
                FunctionCallOrExpression::Expression(u) => u,
            }
        }
        FieldElementExpression::Member(m) => {
            match f.fold_member_expression(&Type::FieldElement, m)? {
                MemberOrExpression::Member(m) => FieldElementExpression::Member(m),
                MemberOrExpression::Expression(u) => u,
            }
        }
        FieldElementExpression::Select(select) => {
            match f.fold_select_expression(&Type::FieldElement, select)? {
                SelectOrExpression::Select(s) => FieldElementExpression::Select(s),
                SelectOrExpression::Expression(u) => u,
            }
        }
    };
    Ok(e)
}

pub fn fold_int_expression<'ast, T: Field, F: ResultFolder<'ast, T>>(
    _: &mut F,
    _: IntExpression<'ast, T>,
) -> Result<IntExpression<'ast, T>, F::Error> {
    unreachable!()
}

pub fn fold_block_expression<'ast, T: Field, E: ResultFold<'ast, T>, F: ResultFolder<'ast, T>>(
    f: &mut F,
    block: BlockExpression<'ast, T, E>,
) -> Result<BlockExpression<'ast, T, E>, F::Error> {
    Ok(BlockExpression {
        statements: block
            .statements
            .into_iter()
            .map(|s| f.fold_statement(s))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect(),
        value: box block.value.fold(f)?,
    })
}

pub fn fold_if_else_expression<
    'ast,
    T: Field,
    E: Expr<'ast, T>
        + IfElse<'ast, T>
        + PartialEq
        + ResultFold<'ast, T>
        + From<TypedExpression<'ast, T>>,
    F: ResultFolder<'ast, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: IfElseExpression<'ast, T, E>,
) -> Result<IfElseOrExpression<'ast, T, E>, F::Error> {
    Ok(IfElseOrExpression::IfElse(IfElseExpression::new(
        f.fold_boolean_expression(*e.condition)?,
        e.consequence.fold(f)?,
        e.alternative.fold(f)?,
    )))
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
    Ok(MemberOrExpression::Member(MemberExpression::new(
        f.fold_struct_expression(*e.struc)?,
        e.id,
    )))
}

pub fn fold_select_expression<
    'ast,
    T: Field,
    E: Expr<'ast, T> + Select<'ast, T> + From<TypedExpression<'ast, T>>,
    F: ResultFolder<'ast, T>,
>(
    f: &mut F,
    _: &E::Ty,
    e: SelectExpression<'ast, T, E>,
) -> Result<SelectOrExpression<'ast, T, E>, F::Error> {
    Ok(SelectOrExpression::Select(SelectExpression::new(
        f.fold_array_expression(*e.array)?,
        f.fold_uint_expression(*e.index)?,
    )))
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
    Ok(FunctionCallOrExpression::Expression(E::function_call(
        f.fold_declaration_function_key(e.function_key)?,
        e.generics
            .into_iter()
            .map(|g| g.map(|g| f.fold_uint_expression(g)).transpose())
            .collect::<Result<_, _>>()?,
        e.arguments
            .into_iter()
            .map(|e| f.fold_expression(e))
            .collect::<Result<_, _>>()?,
    )))
}

pub fn fold_boolean_expression<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    e: BooleanExpression<'ast, T>,
) -> Result<BooleanExpression<'ast, T>, F::Error> {
    let e = match e {
        BooleanExpression::Block(block) => {
            BooleanExpression::Block(f.fold_block_expression(block)?)
        }
        BooleanExpression::Value(v) => BooleanExpression::Value(v),
        BooleanExpression::Identifier(id) => BooleanExpression::Identifier(f.fold_name(id)?),
        BooleanExpression::FieldEq(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1)?;
            let e2 = f.fold_field_expression(e2)?;
            BooleanExpression::FieldEq(box e1, box e2)
        }
        BooleanExpression::BoolEq(box e1, box e2) => {
            let e1 = f.fold_boolean_expression(e1)?;
            let e2 = f.fold_boolean_expression(e2)?;
            BooleanExpression::BoolEq(box e1, box e2)
        }
        BooleanExpression::ArrayEq(box e1, box e2) => {
            let e1 = f.fold_array_expression(e1)?;
            let e2 = f.fold_array_expression(e2)?;
            BooleanExpression::ArrayEq(box e1, box e2)
        }
        BooleanExpression::StructEq(box e1, box e2) => {
            let e1 = f.fold_struct_expression(e1)?;
            let e2 = f.fold_struct_expression(e2)?;
            BooleanExpression::StructEq(box e1, box e2)
        }
        BooleanExpression::UintEq(box e1, box e2) => {
            let e1 = f.fold_uint_expression(e1)?;
            let e2 = f.fold_uint_expression(e2)?;
            BooleanExpression::UintEq(box e1, box e2)
        }
        BooleanExpression::FieldLt(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1)?;
            let e2 = f.fold_field_expression(e2)?;
            BooleanExpression::FieldLt(box e1, box e2)
        }
        BooleanExpression::FieldLe(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1)?;
            let e2 = f.fold_field_expression(e2)?;
            BooleanExpression::FieldLe(box e1, box e2)
        }
        BooleanExpression::FieldGt(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1)?;
            let e2 = f.fold_field_expression(e2)?;
            BooleanExpression::FieldGt(box e1, box e2)
        }
        BooleanExpression::FieldGe(box e1, box e2) => {
            let e1 = f.fold_field_expression(e1)?;
            let e2 = f.fold_field_expression(e2)?;
            BooleanExpression::FieldGe(box e1, box e2)
        }
        BooleanExpression::UintLt(box e1, box e2) => {
            let e1 = f.fold_uint_expression(e1)?;
            let e2 = f.fold_uint_expression(e2)?;
            BooleanExpression::UintLt(box e1, box e2)
        }
        BooleanExpression::UintLe(box e1, box e2) => {
            let e1 = f.fold_uint_expression(e1)?;
            let e2 = f.fold_uint_expression(e2)?;
            BooleanExpression::UintLe(box e1, box e2)
        }
        BooleanExpression::UintGt(box e1, box e2) => {
            let e1 = f.fold_uint_expression(e1)?;
            let e2 = f.fold_uint_expression(e2)?;
            BooleanExpression::UintGt(box e1, box e2)
        }
        BooleanExpression::UintGe(box e1, box e2) => {
            let e1 = f.fold_uint_expression(e1)?;
            let e2 = f.fold_uint_expression(e2)?;
            BooleanExpression::UintGe(box e1, box e2)
        }
        BooleanExpression::Or(box e1, box e2) => {
            let e1 = f.fold_boolean_expression(e1)?;
            let e2 = f.fold_boolean_expression(e2)?;
            BooleanExpression::Or(box e1, box e2)
        }
        BooleanExpression::And(box e1, box e2) => {
            let e1 = f.fold_boolean_expression(e1)?;
            let e2 = f.fold_boolean_expression(e2)?;
            BooleanExpression::And(box e1, box e2)
        }
        BooleanExpression::Not(box e) => {
            let e = f.fold_boolean_expression(e)?;
            BooleanExpression::Not(box e)
        }
        BooleanExpression::FunctionCall(function_call) => {
            match f.fold_function_call_expression(&Type::Boolean, function_call)? {
                FunctionCallOrExpression::FunctionCall(c) => BooleanExpression::FunctionCall(c),
                FunctionCallOrExpression::Expression(u) => u,
            }
        }
        BooleanExpression::IfElse(c) => match f.fold_if_else_expression(&Type::Boolean, c)? {
            IfElseOrExpression::IfElse(c) => BooleanExpression::IfElse(c),
            IfElseOrExpression::Expression(u) => u,
        },
        BooleanExpression::Select(select) => {
            match f.fold_select_expression(&Type::Boolean, select)? {
                SelectOrExpression::Select(s) => BooleanExpression::Select(s),
                SelectOrExpression::Expression(u) => u,
            }
        }
        BooleanExpression::Member(m) => match f.fold_member_expression(&Type::Boolean, m)? {
            MemberOrExpression::Member(m) => BooleanExpression::Member(m),
            MemberOrExpression::Expression(u) => u,
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

pub fn fold_uint_expression_inner<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    ty: UBitwidth,
    e: UExpressionInner<'ast, T>,
) -> Result<UExpressionInner<'ast, T>, F::Error> {
    let e = match e {
        UExpressionInner::Block(block) => UExpressionInner::Block(f.fold_block_expression(block)?),
        UExpressionInner::Value(v) => UExpressionInner::Value(v),
        UExpressionInner::Identifier(id) => UExpressionInner::Identifier(f.fold_name(id)?),
        UExpressionInner::Add(box left, box right) => {
            let left = f.fold_uint_expression(left)?;
            let right = f.fold_uint_expression(right)?;

            UExpressionInner::Add(box left, box right)
        }
        UExpressionInner::Sub(box left, box right) => {
            let left = f.fold_uint_expression(left)?;
            let right = f.fold_uint_expression(right)?;

            UExpressionInner::Sub(box left, box right)
        }
        UExpressionInner::FloorSub(box left, box right) => {
            let left = f.fold_uint_expression(left)?;
            let right = f.fold_uint_expression(right)?;

            UExpressionInner::FloorSub(box left, box right)
        }
        UExpressionInner::Mult(box left, box right) => {
            let left = f.fold_uint_expression(left)?;
            let right = f.fold_uint_expression(right)?;

            UExpressionInner::Mult(box left, box right)
        }
        UExpressionInner::Div(box left, box right) => {
            let left = f.fold_uint_expression(left)?;
            let right = f.fold_uint_expression(right)?;

            UExpressionInner::Div(box left, box right)
        }
        UExpressionInner::Rem(box left, box right) => {
            let left = f.fold_uint_expression(left)?;
            let right = f.fold_uint_expression(right)?;

            UExpressionInner::Rem(box left, box right)
        }
        UExpressionInner::Xor(box left, box right) => {
            let left = f.fold_uint_expression(left)?;
            let right = f.fold_uint_expression(right)?;

            UExpressionInner::Xor(box left, box right)
        }
        UExpressionInner::And(box left, box right) => {
            let left = f.fold_uint_expression(left)?;
            let right = f.fold_uint_expression(right)?;

            UExpressionInner::And(box left, box right)
        }
        UExpressionInner::Or(box left, box right) => {
            let left = f.fold_uint_expression(left)?;
            let right = f.fold_uint_expression(right)?;

            UExpressionInner::Or(box left, box right)
        }
        UExpressionInner::LeftShift(box e, box by) => {
            let e = f.fold_uint_expression(e)?;
            let by = f.fold_uint_expression(by)?;

            UExpressionInner::LeftShift(box e, box by)
        }
        UExpressionInner::RightShift(box e, box by) => {
            let e = f.fold_uint_expression(e)?;
            let by = f.fold_uint_expression(by)?;

            UExpressionInner::RightShift(box e, box by)
        }
        UExpressionInner::Not(box e) => {
            let e = f.fold_uint_expression(e)?;

            UExpressionInner::Not(box e)
        }
        UExpressionInner::Neg(box e) => {
            let e = f.fold_uint_expression(e)?;

            UExpressionInner::Neg(box e)
        }
        UExpressionInner::Pos(box e) => {
            let e = f.fold_uint_expression(e)?;

            UExpressionInner::Pos(box e)
        }
        UExpressionInner::FunctionCall(function_call) => {
            match f.fold_function_call_expression(&ty, function_call)? {
                FunctionCallOrExpression::FunctionCall(c) => UExpressionInner::FunctionCall(c),
                FunctionCallOrExpression::Expression(u) => u,
            }
        }
        UExpressionInner::Select(select) => match f.fold_select_expression(&ty, select)? {
            SelectOrExpression::Select(s) => UExpressionInner::Select(s),
            SelectOrExpression::Expression(u) => u,
        },
        UExpressionInner::IfElse(c) => match f.fold_if_else_expression(&ty, c)? {
            IfElseOrExpression::IfElse(c) => UExpressionInner::IfElse(c),
            IfElseOrExpression::Expression(u) => u,
        },
        UExpressionInner::Member(m) => match f.fold_member_expression(&ty, m)? {
            MemberOrExpression::Member(m) => UExpressionInner::Member(m),
            MemberOrExpression::Expression(u) => u,
        },
    };
    Ok(e)
}

pub fn fold_declaration_function_key<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    key: DeclarationFunctionKey<'ast>,
) -> Result<DeclarationFunctionKey<'ast>, F::Error> {
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

fn fold_signature<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    s: DeclarationSignature<'ast>,
) -> Result<DeclarationSignature<'ast>, F::Error> {
    Ok(DeclarationSignature {
        generics: s.generics,
        inputs: s
            .inputs
            .into_iter()
            .map(|o| f.fold_declaration_type(o))
            .collect::<Result<_, _>>()?,
        outputs: s
            .outputs
            .into_iter()
            .map(|o| f.fold_declaration_type(o))
            .collect::<Result<_, _>>()?,
    })
}

fn fold_declaration_constant<'ast, T: Field, F: ResultFolder<'ast, T>>(
    _: &mut F,
    c: DeclarationConstant<'ast>,
) -> Result<DeclarationConstant<'ast>, F::Error> {
    Ok(c)
}

pub fn fold_array_expression<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    e: ArrayExpression<'ast, T>,
) -> Result<ArrayExpression<'ast, T>, F::Error> {
    let ty = f.fold_array_type(*e.ty)?;

    Ok(ArrayExpression {
        inner: f.fold_array_expression_inner(&ty, e.inner)?,
        ty: box ty,
    })
}

pub fn fold_expression_list<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    es: TypedExpressionList<'ast, T>,
) -> Result<TypedExpressionList<'ast, T>, F::Error> {
    let types = f.fold_types(es.types)?;

    Ok(TypedExpressionList {
        inner: f.fold_expression_list_inner(&types, es.inner)?,
        types,
    })
}

pub fn fold_types<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    tys: Types<'ast, T>,
) -> Result<Types<'ast, T>, F::Error> {
    Ok(Types {
        inner: tys
            .inner
            .into_iter()
            .map(|t| f.fold_type(t))
            .collect::<Result<_, _>>()?,
    })
}

pub fn fold_expression_list_inner<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    tys: &Types<'ast, T>,
    es: TypedExpressionListInner<'ast, T>,
) -> Result<TypedExpressionListInner<'ast, T>, F::Error> {
    match es {
        TypedExpressionListInner::FunctionCall(function_call) => {
            match f.fold_function_call_expression(tys, function_call)? {
                FunctionCallOrExpression::FunctionCall(function_call) => {
                    Ok(TypedExpressionListInner::FunctionCall(function_call))
                }
                FunctionCallOrExpression::Expression(list) => Ok(list),
            }
        }
        TypedExpressionListInner::EmbedCall(embed, generics, arguments) => {
            Ok(TypedExpressionListInner::EmbedCall(
                embed,
                generics,
                arguments
                    .into_iter()
                    .map(|a| f.fold_expression(a))
                    .collect::<Result<_, _>>()?,
            ))
        }
    }
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

pub fn fold_constant<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    c: TypedConstant<'ast, T>,
) -> Result<TypedConstant<'ast, T>, F::Error> {
    Ok(TypedConstant {
        expression: f.fold_expression(c.expression)?,
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

pub fn fold_module<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    m: TypedModule<'ast, T>,
) -> Result<TypedModule<'ast, T>, F::Error> {
    Ok(TypedModule {
        constants: m
            .constants
            .into_iter()
            .map(|(key, tc)| f.fold_constant_symbol(tc).map(|tc| (key, tc)))
            .collect::<Result<_, _>>()?,
        functions: m
            .functions
            .into_iter()
            .map(|(key, fun)| f.fold_function_symbol(fun).map(|f| (key, f)))
            .collect::<Result<_, _>>()?,
    })
}

pub fn fold_program<'ast, T: Field, F: ResultFolder<'ast, T>>(
    f: &mut F,
    p: TypedProgram<'ast, T>,
) -> Result<TypedProgram<'ast, T>, F::Error> {
    Ok(TypedProgram {
        modules: p
            .modules
            .into_iter()
            .map(|(module_id, module)| f.fold_module(module).map(|m| (module_id, m)))
            .collect::<Result<_, _>>()?,
        main: f.fold_module_id(p.main)?,
    })
}
