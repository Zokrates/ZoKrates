// The inlining phase takes a call site (fun::<gen>(args)) and inlines it:

// Given:
// ```
// def foo<n>(field a) -> field:
//		a = a
//		n = n
//		return a
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

use crate::embed::FlatEmbed;
use crate::static_analysis::reducer::Output;
use crate::static_analysis::reducer::ShallowTransformer;
use crate::static_analysis::reducer::Versions;
use crate::typed_absy::types::{ConcreteGenericsAssignment, IntoTypes};
use crate::typed_absy::CoreIdentifier;
use crate::typed_absy::Identifier;
use crate::typed_absy::TypedAssignee;
use crate::typed_absy::{
    ConcreteFunctionKey, ConcreteSignature, ConcreteVariable, DeclarationFunctionKey, Expr,
    Signature, TypedExpression, TypedFunctionSymbol, TypedFunctionSymbolDeclaration, TypedProgram,
    TypedStatement, Types, UExpression, UExpressionInner, Variable,
};
use zokrates_field::Field;

pub enum InlineError<'ast, T> {
    Generic(DeclarationFunctionKey<'ast, T>, ConcreteFunctionKey<'ast>),
    Flat(
        FlatEmbed,
        Vec<u32>,
        Vec<TypedExpression<'ast, T>>,
        Types<'ast, T>,
    ),
    NonConstant(
        DeclarationFunctionKey<'ast, T>,
        Vec<Option<UExpression<'ast, T>>>,
        Vec<TypedExpression<'ast, T>>,
        Types<'ast, T>,
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
    Output<
        (Vec<TypedStatement<'ast, T>>, Vec<TypedExpression<'ast, T>>),
        Vec<(Versions<'ast>, Versions<'ast>)>,
    >,
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

    use crate::typed_absy::Typed;

    let output_types = output.clone().into_types();

    // we try to get concrete values for explicit generics
    let generics_values: Vec<Option<u32>> = match generics
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
    {
        Ok(s) => s,
        Err(_) => {
            return Err(InlineError::NonConstant(
                k,
                generics,
                arguments,
                output_types,
            ))
        }
    };

    // we infer a signature based on inputs and outputs
    // this is where we could handle explicit annotations
    let inferred_signature = Signature::new()
        .generics(generics.clone())
        .inputs(arguments.iter().map(|a| a.get_type()).collect())
        .outputs(output_types.clone().inner);

    // we try to get concrete values for the whole signature. if this fails we should propagate again
    let inferred_signature = match ConcreteSignature::try_from(inferred_signature) {
        Ok(s) => s,
        Err(_) => {
            return Err(InlineError::NonConstant(
                k,
                generics,
                arguments,
                output_types,
            ));
        }
    };

    let decl = get_canonical_function(k.clone(), program);

    // get an assignment of generics for this call site
    let assignment: ConcreteGenericsAssignment<'ast> =
        match k.signature.specialize(generics_values, &inferred_signature) {
            Ok(a) => a,
            Err(_) => {
                return Err(InlineError::Generic(
                    k.clone(),
                    ConcreteFunctionKey {
                        module: decl.key.module,
                        id: decl.key.id,
                        signature: inferred_signature,
                    },
                ));
            }
        };

    let f = match decl.symbol {
        TypedFunctionSymbol::Here(f) => f,
        TypedFunctionSymbol::Flat(e) => {
            return Err(InlineError::Flat(
                e,
                e.generics::<T>(&assignment),
                arguments,
                output_types,
            ));
        }
        _ => unreachable!(),
    };

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
        .map(|(p, t)| ConcreteVariable::with_id_and_type(p.id.id, t))
        .zip(arguments.clone())
        .map(|(v, a)| TypedStatement::Definition(TypedAssignee::Identifier(v.into()), a))
        .collect();

    let (statements, mut returns): (Vec<_>, Vec<_>) = ssa_f
        .statements
        .into_iter()
        .partition(|s| !matches!(s, TypedStatement::Return(..)));

    assert_eq!(returns.len(), 1);

    let returns = match returns.pop().unwrap() {
        TypedStatement::Return(e) => e,
        _ => unreachable!(),
    };

    let res: Vec<ConcreteVariable<'ast>> = inferred_signature
        .outputs
        .iter()
        .enumerate()
        .map(|(i, t)| {
            ConcreteVariable::with_id_and_type(
                Identifier::from(CoreIdentifier::Call(i)).version(
                    *versions
                        .entry(CoreIdentifier::Call(i).clone())
                        .and_modify(|e| *e += 1) // if it was already declared, we increment
                        .or_insert(0),
                ),
                t.clone(),
            )
        })
        .collect();

    let expressions: Vec<TypedExpression<_>> = res
        .iter()
        .map(|v| TypedExpression::from(Variable::from(v.clone())))
        .collect();

    assert_eq!(res.len(), returns.len());

    let output_bindings: Vec<TypedStatement<'ast, T>> = res
        .into_iter()
        .zip(returns)
        .map(|(v, a)| TypedStatement::Definition(TypedAssignee::Identifier(v.into()), a))
        .collect();

    let pop_log = TypedStatement::PopCallLog;

    let statements: Vec<_> = std::iter::once(call_log)
        .chain(input_bindings)
        .chain(statements)
        .chain(output_bindings)
        .chain(std::iter::once(pop_log))
        .collect();

    Ok(incomplete_data
        .map(|d| Output::Incomplete((statements.clone(), expressions.clone()), d))
        .unwrap_or_else(|| Output::Complete((statements, expressions))))
}
