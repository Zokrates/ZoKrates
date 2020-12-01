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
use crate::static_analysis::reducer::CallCache;
use crate::static_analysis::reducer::Output;
use crate::static_analysis::reducer::ShallowTransformer;
use crate::static_analysis::reducer::Versions;
use crate::typed_absy::types::ConcreteGenericsAssignment;
use crate::typed_absy::CoreIdentifier;
use crate::typed_absy::Identifier;
use crate::typed_absy::TypedAssignee;
use crate::typed_absy::{
    ConcreteFunctionKey, ConcreteSignature, ConcreteVariable, DeclarationFunctionKey, Signature,
    Type, TypedExpression, TypedFunction, TypedFunctionSymbol, TypedProgram, TypedStatement,
    Variable,
};
use zokrates_field::Field;

pub enum InlineError<'ast, T> {
    Generic(DeclarationFunctionKey<'ast>, ConcreteFunctionKey<'ast>),
    Flat(FlatEmbed, Vec<TypedExpression<'ast, T>>, Vec<Type<'ast, T>>),
    NonConstant(
        DeclarationFunctionKey<'ast>,
        Vec<TypedExpression<'ast, T>>,
        Vec<Type<'ast, T>>,
    ),
}

fn get_canonical_function<'ast, T: Field>(
    function_key: DeclarationFunctionKey<'ast>,
    program: &TypedProgram<'ast, T>,
) -> Result<(DeclarationFunctionKey<'ast>, TypedFunction<'ast, T>), FlatEmbed> {
    match program
        .modules
        .get(&function_key.module)
        .unwrap()
        .functions
        .iter()
        .find(|(key, _)| function_key == **key)
        .unwrap()
    {
        (key, TypedFunctionSymbol::Here(f)) => Ok((key.clone(), f.clone())),
        (_, TypedFunctionSymbol::There(key)) => get_canonical_function(key.clone(), &program),
        (_, TypedFunctionSymbol::Flat(f)) => Err(f.clone()),
    }
}

pub fn inline_call<'a, 'ast, T: Field>(
    k: DeclarationFunctionKey<'ast>,
    arguments: Vec<TypedExpression<'ast, T>>,
    output_types: Vec<Type<'ast, T>>,
    program: &TypedProgram<'ast, T>,
    cache: &mut CallCache<'ast, T>,
    versions: &'a mut Versions<'ast>,
) -> Result<
    Output<(Vec<TypedStatement<'ast, T>>, Vec<TypedExpression<'ast, T>>), Vec<Versions<'ast>>>,
    InlineError<'ast, T>,
> {
    use std::convert::TryFrom;

    use crate::typed_absy::Typed;

    // we infer a signature based on inputs and outputs
    // this is where we could handle explicit annotations
    let inferred_signature = Signature::new()
        .inputs(arguments.iter().map(|a| a.get_type()).collect())
        .outputs(output_types.clone());

    // we try to get concrete values for the whole signature. if this fails we should propagate again
    let inferred_signature = match ConcreteSignature::try_from(inferred_signature) {
        Ok(s) => s,
        Err(()) => {
            return Err(InlineError::NonConstant(k, arguments, output_types));
        }
    };

    let (decl_key, f) = get_canonical_function(k.clone(), program)
        .map_err(|e| InlineError::Flat(e, arguments.clone(), output_types))?;
    assert_eq!(f.arguments.len(), arguments.len());

    // get an assignment of generics for this call site
    let assignment: ConcreteGenericsAssignment<'ast> = decl_key
        .signature
        .specialize(&inferred_signature)
        .map_err(|_| {
            InlineError::Generic(
                decl_key.clone(),
                ConcreteFunctionKey {
                    module: decl_key.module.clone(),
                    id: decl_key.id.clone(),
                    signature: inferred_signature.clone(),
                },
            )
        })?;

    let concrete_key = ConcreteFunctionKey {
        module: decl_key.module.clone(),
        id: decl_key.id.clone(),
        signature: inferred_signature.clone(),
    };

    match cache.get(&(concrete_key.clone(), arguments.clone())) {
        Some(v) => {
            return Ok(Output::Complete((vec![], v.clone())));
        }
        None => {}
    };

    let (ssa_f, incomplete_data) = match ShallowTransformer::transform(f, &assignment, versions) {
        Output::Complete(v) => (v, None),
        Output::Incomplete(statements, for_loop_versions) => (statements, Some(for_loop_versions)),
    };

    let call_log = TypedStatement::PushCallLog(decl_key.clone(), assignment);

    let input_bindings: Vec<TypedStatement<'ast, T>> = ssa_f
        .arguments
        .into_iter()
        .zip(inferred_signature.inputs.clone())
        .map(|(p, t)| ConcreteVariable::with_id_and_type(p.id.id, t))
        .zip(arguments.clone())
        .map(|(v, a)| TypedStatement::Definition(TypedAssignee::Identifier(v.into()), a))
        .collect();

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

    cache.insert(
        (concrete_key.clone(), arguments.clone()),
        expressions.clone(),
    );

    Ok(incomplete_data
        .map(|d| Output::Incomplete((statements.clone(), expressions.clone()), d))
        .unwrap_or_else(|| Output::Complete((statements, expressions))))
}
