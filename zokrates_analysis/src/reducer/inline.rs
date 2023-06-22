// The inlining phase takes a call site (fun::<gen>(args)) and inlines it:

// Given:
// ```
// def foo<n>(field a) -> field {
//     a = a;
//     n = n;
//     return a;
// }
// ```
//
// The call site
// ```
// foo::<42>(x)
// ```
//
// Becomes
// inputs: [a]
// arguments: [x]
// generics_bindings: [n = 42]
// statements:
// n = 42
// a = a
// n = n
// return_expression: a

// Notes:
// - The body of the function is *not* in SSA form

use zokrates_ast::common::FlatEmbed;
use zokrates_ast::typed::types::{ConcreteGenericsAssignment, IntoType};
use zokrates_ast::typed::CoreIdentifier;

use zokrates_ast::typed::TypedAssignee;
use zokrates_ast::typed::UBitwidth;
use zokrates_ast::typed::{
    ConcreteFunctionKey, ConcreteSignature, ConcreteVariable, DeclarationFunctionKey, Expr,
    Signature, Type, TypedExpression, TypedFunctionSymbol, TypedFunctionSymbolDeclaration,
    TypedProgram, TypedStatement, UExpression, UExpressionInner, Variable,
};
use zokrates_field::Field;

pub enum InlineError<'ast, T> {
    Generic(DeclarationFunctionKey<'ast, T>, ConcreteFunctionKey<'ast>),
    Flat(FlatEmbed, Vec<u32>, Type<'ast, T>),
    NonConstant,
}

fn get_canonical_function<'ast, T: Field>(
    function_key: &DeclarationFunctionKey<'ast, T>,
    program: &TypedProgram<'ast, T>,
) -> TypedFunctionSymbolDeclaration<'ast, T> {
    let s = program
        .modules
        .get(&function_key.module)
        .unwrap()
        .functions_iter()
        .find(|d| d.key == *function_key)
        .unwrap();

    match &s.symbol {
        TypedFunctionSymbol::There(key) => get_canonical_function(key, program),
        _ => s.clone(),
    }
}

pub struct InlineValue<'ast, T> {
    /// the pre-SSA input variables to assign the arguments to
    pub input_variables: Vec<Variable<'ast, T>>,
    /// the pre-SSA statements for this call, including definition of the generic parameters
    pub statements: Vec<TypedStatement<'ast, T>>,
    /// the pre-SSA return value for this call
    pub return_value: TypedExpression<'ast, T>,
}

type InlineResult<'ast, T> = Result<InlineValue<'ast, T>, InlineError<'ast, T>>;

pub fn inline_call<'a, 'ast, T: Field, E: Expr<'ast, T>>(
    k: &DeclarationFunctionKey<'ast, T>,
    generics: &[Option<UExpression<'ast, T>>],
    arguments: &[TypedExpression<'ast, T>],
    output_ty: &E::Ty,
    program: &TypedProgram<'ast, T>,
) -> InlineResult<'ast, T> {
    use zokrates_ast::typed::Typed;
    let output_type = output_ty.clone().into_type();

    // we try to get concrete values for explicit generics
    let generics_values: Vec<Option<u32>> = generics
        .iter()
        .map(|g| {
            g.as_ref()
                .map(|g| match g.as_inner() {
                    UExpressionInner::Value(v) => Ok(v.value as u32),
                    _ => Err(()),
                })
                .transpose()
        })
        .collect::<Result<_, _>>()
        .map_err(|_| InlineError::NonConstant)?;

    // we infer a signature based on inputs and outputs
    let inferred_signature = Signature::new()
        .generics(generics.to_vec().clone())
        .inputs(arguments.iter().map(|a| a.get_type()).collect())
        .output(output_type.clone());

    // we try to get concrete values for the whole signature
    let inferred_signature = match ConcreteSignature::try_from(inferred_signature) {
        Ok(s) => s,
        Err(_) => {
            return Err(InlineError::NonConstant);
        }
    };

    let decl = get_canonical_function(k, program);

    // get an assignment of generics for this call site
    let assignment: ConcreteGenericsAssignment<'ast> = k
        .signature
        .specialize(generics_values, &inferred_signature)
        .map_err(|_| {
            InlineError::Generic(
                k.clone(),
                ConcreteFunctionKey {
                    module: decl.key.module.clone(),
                    id: decl.key.id,
                    signature: inferred_signature.clone(),
                },
            )
        })?;

    let f = match decl.symbol {
        TypedFunctionSymbol::Here(f) => Ok(f),
        TypedFunctionSymbol::Flat(e) => Err(InlineError::Flat(
            e,
            e.generics::<T>(&assignment),
            output_type,
        )),
        _ => unreachable!(),
    }?;

    assert_eq!(f.arguments.len(), arguments.len());

    let generic_bindings = assignment.0.into_iter().map(|(identifier, value)| {
        TypedStatement::definition(
            TypedAssignee::Identifier(Variable::uint(
                CoreIdentifier::from(identifier),
                UBitwidth::B32,
            )),
            TypedExpression::from(UExpression::from(value)),
        )
    });

    let input_variables: Vec<Variable<'ast, T>> = f
        .arguments
        .into_iter()
        .zip(inferred_signature.inputs.clone())
        .map(|(p, t)| ConcreteVariable::new(p.id.id, t))
        .map(Variable::from)
        .collect();

    let (statements, mut returns): (Vec<_>, Vec<_>) = generic_bindings
        .chain(f.statements)
        .partition(|s| !matches!(s, TypedStatement::Return(..)));

    assert_eq!(returns.len(), 1);

    let return_value = match returns.pop().unwrap() {
        TypedStatement::Return(e) => e.inner,
        _ => unreachable!(),
    };

    Ok(InlineValue {
        input_variables,
        statements,
        return_value,
    })
}
