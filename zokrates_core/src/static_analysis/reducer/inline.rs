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
// ```
// # Call foo::<42> with a_0 := x
// n_0 = 42
// a_1 = a_0
// n_1 = n_0
// # Pop call with #CALL_RETURN_AT_INDEX_0_0 := a_1

// Notes:
// - The body of the function is in SSA form
// - The return value(s) are assigned to internal variables

use crate::static_analysis::reducer::Output;
use crate::static_analysis::reducer::ShallowTransformer;
use crate::static_analysis::reducer::Versions;

use zokrates_ast::common::FlatEmbed;
use zokrates_ast::typed::types::{ConcreteGenericsAssignment, IntoType};
use zokrates_ast::typed::CoreIdentifier;
use zokrates_ast::typed::Identifier;
use zokrates_ast::typed::{
    ConcreteFunctionKey, ConcreteSignature, ConcreteVariable, DeclarationFunctionKey, Expr,
    Signature, Type, TypedExpression, TypedFunctionSymbol, TypedFunctionSymbolDeclaration,
    TypedProgram, TypedStatement, UExpression, UExpressionInner, Variable,
};
use zokrates_field::Field;

pub enum InlineError<'ast, T> {
    Generic(DeclarationFunctionKey<'ast, T>, ConcreteFunctionKey<'ast>),
    Flat(
        FlatEmbed,
        Vec<u32>,
        Vec<TypedExpression<'ast, T>>,
        Type<'ast, T>,
    ),
    NonConstant(
        DeclarationFunctionKey<'ast, T>,
        Vec<Option<UExpression<'ast, T>>>,
        Vec<TypedExpression<'ast, T>>,
        Type<'ast, T>,
    ),
}

fn get_canonical_function<'ast, T: Field>(
    function_key: DeclarationFunctionKey<'ast, T>,
    program: &TypedProgram<'ast, T>,
) -> TypedFunctionSymbolDeclaration<'ast, T> {
    let s = program
        .modules
        .get(&function_key.module)
        .unwrap()
        .functions_iter()
        .find(|d| d.key == function_key)
        .unwrap();

    match &s.symbol {
        TypedFunctionSymbol::There(key) => get_canonical_function(key.clone(), program),
        _ => s.clone(),
    }
}

type InlineResult<'ast, T> = Result<
    Output<(Vec<TypedStatement<'ast, T>>, TypedExpression<'ast, T>), Vec<Versions<'ast>>>,
    InlineError<'ast, T>,
>;

pub fn inline_call<'a, 'ast, T: Field, E: Expr<'ast, T>>(
    k: DeclarationFunctionKey<'ast, T>,
    generics: Vec<Option<UExpression<'ast, T>>>,
    arguments: Vec<TypedExpression<'ast, T>>,
    output: &E::Ty,
    program: &TypedProgram<'ast, T>,
    versions: &'a mut Versions<'ast>,
) -> InlineResult<'ast, T> {
    use std::convert::TryFrom;

    use zokrates_ast::typed::Typed;
    let output_type = output.clone().into_type();

    // we try to get concrete values for explicit generics
    let generics_values: Vec<Option<u32>> = generics
        .iter()
        .map(|g| {
            g.as_ref()
                .map(|g| match g.as_inner() {
                    UExpressionInner::Value(v) => Ok(*v as u32),
                    _ => Err(()),
                })
                .transpose()
        })
        .collect::<Result<_, _>>()
        .map_err(|_| {
            InlineError::NonConstant(
                k.clone(),
                generics.clone(),
                arguments.clone(),
                output_type.clone(),
            )
        })?;

    // we infer a signature based on inputs and outputs
    // this is where we could handle explicit annotations
    let inferred_signature = Signature::new()
        .generics(generics.clone())
        .inputs(arguments.iter().map(|a| a.get_type()).collect())
        .output(output_type.clone());

    // we try to get concrete values for the whole signature. if this fails we should propagate again
    let inferred_signature = match ConcreteSignature::try_from(inferred_signature) {
        Ok(s) => s,
        Err(_) => {
            return Err(InlineError::NonConstant(
                k,
                generics,
                arguments,
                output_type,
            ));
        }
    };

    let decl = get_canonical_function(k.clone(), program);

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
            arguments.clone(),
            output_type,
        )),
        _ => unreachable!(),
    }?;

    assert_eq!(f.arguments.len(), arguments.len());

    let (ssa_f, incomplete_data) = match ShallowTransformer::transform(f, &assignment, versions) {
        Output::Complete(v) => (v, None),
        Output::Incomplete(statements, for_loop_versions) => (statements, Some(for_loop_versions)),
    };

    let call_log = TypedStatement::PushCallLog(decl.key.clone(), assignment.clone());

    let input_bindings: Vec<TypedStatement<'ast, T>> = ssa_f
        .arguments
        .into_iter()
        .zip(inferred_signature.inputs.clone())
        .map(|(p, t)| ConcreteVariable::new(p.id.id, t, false))
        .zip(arguments.clone())
        .map(|(v, a)| TypedStatement::definition(Variable::from(v).into(), a))
        .collect();

    let (statements, mut returns): (Vec<_>, Vec<_>) = ssa_f
        .statements
        .into_iter()
        .partition(|s| !matches!(s, TypedStatement::Return(..)));

    assert_eq!(returns.len(), 1);

    let return_expression = match returns.pop().unwrap() {
        TypedStatement::Return(e) => e,
        _ => unreachable!(),
    };

    let v: ConcreteVariable<'ast> = ConcreteVariable::new(
        Identifier::from(CoreIdentifier::Call(0)).version(
            *versions
                .entry(CoreIdentifier::Call(0))
                .and_modify(|e| *e += 1) // if it was already declared, we increment
                .or_insert(0),
        ),
        *inferred_signature.output.clone(),
        false,
    );

    let expression = TypedExpression::from(Variable::from(v.clone()));

    let output_binding = TypedStatement::definition(Variable::from(v).into(), return_expression);

    let pop_log = TypedStatement::PopCallLog;

    let statements: Vec<_> = std::iter::once(call_log)
        .chain(input_bindings)
        .chain(statements)
        .chain(std::iter::once(output_binding))
        .chain(std::iter::once(pop_log))
        .collect();

    Ok(incomplete_data
        .map(|d| Output::Incomplete((statements.clone(), expression.clone()), d))
        .unwrap_or_else(|| Output::Complete((statements, expression))))
}
