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

use typed_absy::{TypedFunction, TypedStatement};

fn inline_call<'ast, T>(f: TypedFunction<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
    let call_log = TypedStatement::PushCallLog(k, gen, f.argument, a);

    let call_pop = TypedStatement::PopCallLog(v, f.returns);

    Ok(std::iter::once(call_log)
        .chain(f.statements)
        .chain(std::iter::once(call_pop))
        .collect())
}
