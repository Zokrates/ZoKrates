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

use static_analysis::reducer::Output;
use static_analysis::reducer::ShallowTransformer;
use static_analysis::reducer::Versions;
use typed_absy::CoreIdentifier;
use typed_absy::Identifier;
use typed_absy::{
    ConcreteSignature, ConcreteVariable, DeclarationFunctionKey, DeclarationSignature, Signature,
    Type, TypedExpression, TypedFunction, TypedFunctionSymbol, TypedModuleId, TypedModules,
    TypedStatement, Variable,
};
use zokrates_field::Field;

pub enum InlineError<'ast, T> {
    Generic(DeclarationSignature<'ast>, ConcreteSignature),
    Flat,
    NonConstant(
        TypedModuleId,
        DeclarationFunctionKey<'ast>,
        Vec<TypedExpression<'ast, T>>,
        Vec<Type<'ast, T>>,
    ),
}

fn get_canonical_function<'ast, T: Field>(
    module_id: TypedModuleId,
    function_key: DeclarationFunctionKey<'ast>,
    modules: &TypedModules<'ast, T>,
) -> (
    TypedModuleId,
    DeclarationFunctionKey<'ast>,
    TypedFunction<'ast, T>,
) {
    match modules
        .get(&module_id.clone())
        .unwrap()
        .functions
        .iter()
        .find(|(key, _)| function_key == **key)
        .unwrap()
    {
        (key, TypedFunctionSymbol::Here(f)) => (module_id, key.clone(), f.clone()),
        _ => unimplemented!(),
    }
}

pub fn inline_call<'a, 'ast, T: Field>(
    module_id: TypedModuleId,
    k: DeclarationFunctionKey<'ast>,
    arguments: Vec<TypedExpression<'ast, T>>,
    output_types: Vec<Type<'ast, T>>,
    modules: &TypedModules<'ast, T>,
    versions: &'a mut Versions<'ast>,
) -> Result<
    Output<(Vec<TypedStatement<'ast, T>>, Vec<TypedExpression<'ast, T>>), Vec<Versions<'ast>>>,
    InlineError<'ast, T>,
> {
    use std::convert::TryFrom;

    use typed_absy::Typed;

    // we infer a signature based on inputs and outputs
    // this is where we could handle explicit annotations
    let inferred_signature = Signature::new()
        .inputs(arguments.iter().map(|a| a.get_type()).collect())
        .outputs(output_types.clone());

    // we try to get concrete values for the whole signature. if this fails we should propagate again
    let inferred_signature = match ConcreteSignature::try_from(inferred_signature) {
        Ok(s) => s,
        Err(()) => {
            return Err(InlineError::NonConstant(
                module_id,
                k,
                arguments,
                output_types,
            ));
        }
    };

    let (module_id, decl_key, f) = get_canonical_function(module_id, k.clone(), modules);
    assert_eq!(f.arguments.len(), arguments.len());

    // get an assignment of generics for this call site
    let assignment = decl_key
        .signature
        .specialize(&inferred_signature)
        .map_err(|_| {
            InlineError::Generic(decl_key.signature.clone(), inferred_signature.clone())
        })?;

    let (ssa_f, incomplete_data) = match ShallowTransformer::transform(f, &assignment, versions) {
        Output::Complete(v) => (v, None),
        Output::Incomplete(statements, for_loop_versions) => (statements, Some(for_loop_versions)),
    };

    let call_log = TypedStatement::PushCallLog(
        module_id,
        decl_key.clone(),
        assignment,
        ssa_f
            .arguments
            .into_iter()
            .zip(inferred_signature.inputs.clone())
            .map(|(p, t)| ConcreteVariable::with_id_and_type(p.id.id, t))
            .zip(arguments)
            .collect(),
    );

    let (statements, returns): (Vec<_>, Vec<_>) =
        ssa_f.statements.into_iter().partition(|s| match s {
            TypedStatement::Return(..) => false,
            _ => true,
        });

    assert_eq!(returns.len(), 1);

    let returns = match returns[0].clone() {
        TypedStatement::Return(e) => e,
        _ => unreachable!(),
    };

    let res: Vec<ConcreteVariable<'ast>> = inferred_signature
        .outputs
        .iter()
        .enumerate()
        .map(|(i, t)| {
            ConcreteVariable::with_id_and_type(Identifier::from(CoreIdentifier::Call(i)), t.clone())
        })
        .collect();

    let expressions: Vec<TypedExpression<_>> = res
        .iter()
        .map(|v| TypedExpression::from(Variable::from(v.clone())))
        .collect();

    assert_eq!(res.len(), returns.len());

    let call_pop = TypedStatement::PopCallLog(res.into_iter().zip(returns).collect());

    let statements: Vec<_> = std::iter::once(call_log)
        .chain(statements)
        .chain(std::iter::once(call_pop))
        .collect();

    Ok(incomplete_data
        .map(|d| Output::Incomplete((statements.clone(), expressions.clone()), d))
        .unwrap_or_else(|| Output::Complete((statements, expressions))))
}
