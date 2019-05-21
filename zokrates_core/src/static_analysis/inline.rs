use std::collections::HashMap;
use typed_absy::folder::fold_boolean_expression;
use typed_absy::folder::fold_field_array_expression;
use typed_absy::folder::fold_field_expression;
use typed_absy::folder::fold_statement;
use typed_absy::BooleanExpression;
use typed_absy::FieldElementArrayExpression;
use typed_absy::FieldElementExpression;
use typed_absy::TypedStatement;
use typed_absy::{
    Folder, TypedFunctionSymbol, TypedModule, TypedModuleId, TypedModules, TypedProgram,
};
use types::FunctionKey;
use zokrates_field::field::Field;

pub struct Inliner<'a, T: Field> {
    modules: &'a TypedModules<T>,
    symbols: &'a HashMap<FunctionKey, TypedFunctionSymbol<T>>,
    statement_buffer: Vec<TypedStatement<T>>,
}

impl<'a, T: Field> Inliner<'a, T> {
    fn with_modules_and_module_id(modules: &'a TypedModules<T>, module_id: TypedModuleId) -> Self {
        Inliner {
            modules,
            symbols: &modules.get(&module_id).unwrap().functions,
            statement_buffer: vec![],
        }
    }

    pub fn inline(p: TypedProgram<T>) -> TypedProgram<T> {
        let mut modules = p.modules.clone();
        modules.insert(String::from("main"), p.main.clone());
        Inliner::with_modules_and_module_id(&modules, String::from("main")).fold_program(p)
    }

    fn flush(self) -> Vec<TypedStatement<T>> {
        self.statement_buffer
    }
}

impl<'a, T: Field> Folder<T> for Inliner<'a, T> {
    fn fold_program(&mut self, p: TypedProgram<T>) -> TypedProgram<T> {
        let main_module = p.main;

        let (main_key, main) = main_module
            .functions
            .iter()
            .find(|(k, _)| k.id == "main")
            .unwrap();

        let main = self.fold_function_symbol(main.clone());

        TypedProgram {
            main: TypedModule {
                functions: std::iter::once((main_key.clone(), main)).collect(),
                imports: vec![],
            },
            modules: HashMap::new(),
        }
    }

    fn fold_statement(&mut self, s: TypedStatement<T>) -> Vec<TypedStatement<T>> {
        match s {
            TypedStatement::MultipleDefinition(..) => {
                println!("multidef!");
                unimplemented!()
            }
            s => fold_statement(self, s),
        }
    }

    fn fold_field_expression(&mut self, e: FieldElementExpression<T>) -> FieldElementExpression<T> {
        match e {
            FieldElementExpression::FunctionCall(key, expressions) => {
                // get the symbol
                let symbol = self.symbols.get(&key).cloned().unwrap();
                match symbol {
                    TypedFunctionSymbol::Here(f) => {
                        // if it's here, we can inline the call recursively with the same checker as the context is the same
                        let statements: Vec<_> = f
                            .statements
                            .clone()
                            .into_iter()
                            .flat_map(|s| self.fold_statement(s))
                            .collect();
                        self.statement_buffer.extend(statements);
                    }
                    TypedFunctionSymbol::There(function_key, typed_module_id) => {
                        // if it's there, create a new Inliner, inline there and get the statements back
                        let mut inliner = Inliner::with_modules_and_module_id(
                            self.modules,
                            typed_module_id.clone(),
                        );
                        let function = self
                            .modules
                            .get(&typed_module_id)
                            .unwrap()
                            .functions
                            .get(&function_key)
                            .unwrap();
                        inliner.fold_function_symbol(function.clone());
                        self.statement_buffer.extend(inliner.flush());
                    }
                    TypedFunctionSymbol::Flat(..) => unimplemented!(),
                }
                FieldElementExpression::Number(T::from(4242))
            }
            e => fold_field_expression(self, e),
        }
    }

    fn fold_field_array_expression(
        &mut self,
        e: FieldElementArrayExpression<T>,
    ) -> FieldElementArrayExpression<T> {
        match e {
            FieldElementArrayExpression::FunctionCall(..) => {
                println!("field element array call!");
                unimplemented!()
            }
            e => fold_field_array_expression(self, e),
        }
    }
}
