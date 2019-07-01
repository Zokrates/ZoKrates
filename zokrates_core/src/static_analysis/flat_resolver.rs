// Turn nested imports which end by a flat symbol into non-nested imports of that flat symbol

// Before
// // main.code
// import "myflatfun.code" as foo
//
// // myflatfun.code
// def myflatfun() -> ()
//    // hidden (flat code)

// After
// // main.code
// def foo() -> ():
//    // hidden (flat code)
//
// // myflatfun.code
// def myflatfun() -> ()
//    // hidden (flat code)

use crate::typed_absy::folder::*;
use crate::typed_absy::Folder;
use crate::typed_absy::*;
use absy::ModuleId;
use flat_absy::FlatFunction;
use types::FunctionKey;
use zokrates_field::field::Field;

pub struct FlatResolver<'ast, T: Field> {
    modules: TypedModules<'ast, T>,
}

impl<'ast, T: Field> FlatResolver<'ast, T> {
    fn with_modules(m: TypedModules<'ast, T>) -> Self {
        FlatResolver { modules: m }
    }

    pub fn resolve(p: TypedProgram<T>) -> TypedProgram<T> {
        FlatResolver::with_modules(p.modules.clone()).fold_program(p)
    }

    fn resolve_external_symbol(
        &self,
        key: &FunctionKey,
        module_id: &ModuleId,
    ) -> Option<FlatFunction<T>> {
        match self
            .modules
            .get(module_id)
            .unwrap()
            .functions
            .get(&key)
            .unwrap()
        {
            TypedFunctionSymbol::There(key, module_id) => {
                self.resolve_external_symbol(key, module_id)
            }
            TypedFunctionSymbol::Flat(f) => Some(f.clone()),
            _ => None,
        }
    }
}

impl<'ast, T: Field> Folder<'ast, T> for FlatResolver<'ast, T> {
    fn fold_function_symbol(
        &mut self,
        s: TypedFunctionSymbol<'ast, T>,
    ) -> TypedFunctionSymbol<'ast, T> {
        match s {
            TypedFunctionSymbol::There(key, module_id) => {
                match self.resolve_external_symbol(&key, &module_id) {
                    Some(f) => TypedFunctionSymbol::Flat(f),
                    None => TypedFunctionSymbol::There(key, module_id),
                }
            }
            s => fold_function_symbol(self, s),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use flat_absy::*;
    use types::{FunctionKey, Signature, Type};
    use zokrates_field::field::FieldPrime;

    #[test]
    fn remove_linked_flat_import() {
        let flat_fun = FlatFunction {
            arguments: vec![],
            signature: Signature::new().outputs(vec![Type::FieldElement]),
            statements: vec![FlatStatement::Return(FlatExpressionList {
                expressions: vec![FlatExpression::Number(FieldPrime::from(42))],
            })],
        };

        let main = TypedModule {
            functions: vec![
                (
                    FunctionKey::with_id("foo")
                        .signature(Signature::new().outputs(vec![Type::FieldElement])),
                    TypedFunctionSymbol::There(
                        FunctionKey::with_id("myflatfun")
                            .signature(Signature::new().outputs(vec![Type::FieldElement])),
                        String::from("other"),
                    ),
                ),
                (
                    FunctionKey::with_id("main")
                        .signature(Signature::new().outputs(vec![Type::FieldElement])),
                    TypedFunctionSymbol::Here(TypedFunction {
                        signature: Signature::new().outputs(vec![Type::FieldElement]),
                        arguments: vec![],
                        statements: vec![TypedStatement::Return(vec![
                            FieldElementExpression::FunctionCall(
                                FunctionKey::with_id("foo")
                                    .signature(Signature::new().outputs(vec![Type::FieldElement])),
                                vec![],
                            )
                            .into(),
                        ])],
                    }),
                ),
            ]
            .into_iter()
            .collect(),
            imports: vec![],
        };
        let other = TypedModule {
            functions: vec![(
                FunctionKey::with_id("myflatfun")
                    .signature(Signature::new().outputs(vec![Type::FieldElement])),
                TypedFunctionSymbol::Flat(flat_fun.clone()),
            )]
            .into_iter()
            .collect(),
            imports: vec![],
        };

        let prog = TypedProgram {
            main: String::from("main"),
            modules: vec![
                (String::from("main"), main),
                (String::from("other"), other.clone()),
            ]
            .into_iter()
            .collect(),
        };

        let new_main = TypedModule {
            functions: vec![
                (
                    FunctionKey::with_id("foo")
                        .signature(Signature::new().outputs(vec![Type::FieldElement])),
                    TypedFunctionSymbol::Flat(flat_fun),
                ),
                (
                    FunctionKey::with_id("main")
                        .signature(Signature::new().outputs(vec![Type::FieldElement])),
                    TypedFunctionSymbol::Here(TypedFunction {
                        signature: Signature::new().outputs(vec![Type::FieldElement]),
                        arguments: vec![],
                        statements: vec![TypedStatement::Return(vec![
                            FieldElementExpression::FunctionCall(
                                FunctionKey::with_id("foo")
                                    .signature(Signature::new().outputs(vec![Type::FieldElement])),
                                vec![],
                            )
                            .into(),
                        ])],
                    }),
                ),
            ]
            .into_iter()
            .collect(),
            imports: vec![],
        };

        let expected_prog = TypedProgram {
            main: String::from("main"),
            modules: vec![
                (String::from("main"), new_main),
                (String::from("other"), other),
            ]
            .into_iter()
            .collect(),
        };

        assert_eq!(FlatResolver::resolve(prog), expected_prog);
    }
}
