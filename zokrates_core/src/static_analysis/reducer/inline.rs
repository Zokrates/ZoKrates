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
// # Pop call with _ret_foo_42_1 := a_1

// Notes:
// - The body of the function is in SSA form
// - The return value(s) are assigned to internal variables

use typed_absy::{
    ConcreteFunctionKey, ConcreteSignature, ConcreteVariable, DeclarationFunctionKey, FunctionKey,
    Signature, TypedExpression, TypedFunction, TypedFunctionSymbol, TypedModuleId, TypedModules,
    TypedStatement, Variable,
};
use zokrates_field::Field;

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

pub enum InlineError {
    Incompatible,
    NeedsPropagation,
}

pub fn inline_call<'ast, T: Field>(
    res: Vec<Variable<'ast, T>>,
    module_id: TypedModuleId,
    k: DeclarationFunctionKey<'ast>,
    arguments: Vec<TypedExpression<'ast, T>>,
    modules: &TypedModules<'ast, T>,
) -> Result<Vec<TypedStatement<'ast, T>>, Vec<TypedStatement<'ast, T>>> {
    use std::convert::TryFrom;

    let (module_id, decl_key, f) = get_canonical_function(module_id, k.clone(), modules);
    assert_eq!(f.arguments.len(), arguments.len());

    use typed_absy::Typed;

    // we infer a signature based on inputs and outputs
    // this is where we could handle explicit annotations
    let inferred_signature = Signature::new()
        .inputs(arguments.iter().map(|a| a.get_type()).collect())
        .outputs(res.iter().map(|v| v.get_type()).collect());

    // we try to get concrete values for the whole signature. if this fails we should propagate again
    let inferred_signature = ConcreteSignature::try_from(inferred_signature).unwrap();

    // get an assignment of generics for this call site
    let assignment = decl_key.signature.specialize(&inferred_signature).unwrap();

    let call_log = TypedStatement::PushCallLog(
        module_id,
        decl_key.clone(),
        assignment.into_iter().map(|x| x.1).collect(),
        f.arguments
            .into_iter()
            .zip(inferred_signature.inputs)
            .map(|(p, t)| ConcreteVariable::with_id_and_type(p.id.id, t))
            .zip(arguments)
            .collect(),
    );

    let (statements, returns): (Vec<_>, Vec<_>) = f.statements.into_iter().partition(|s| match s {
        TypedStatement::Return(..) => false,
        _ => true,
    });

    assert_eq!(returns.len(), 1);

    let returns = match returns[0].clone() {
        TypedStatement::Return(e) => e,
        _ => unreachable!(),
    };

    assert_eq!(res.len(), returns.len());

    let res = res
        .into_iter()
        .zip(inferred_signature.outputs)
        .map(|(v, t)| ConcreteVariable::with_id_and_type(v.id, t));

    let call_pop = TypedStatement::PopCallLog(res.zip(returns).collect());

    Ok(std::iter::once(call_log)
        .chain(statements)
        .chain(std::iter::once(call_pop))
        .collect())
}
