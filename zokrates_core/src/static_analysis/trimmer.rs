use typed_absy::TypedModule;
use typed_absy::TypedProgram;
use zokrates_field::Field;

pub struct Trimmer;

impl Trimmer {
    pub fn trim<'ast, T: Field>(p: TypedProgram<'ast, T>) -> TypedProgram<'ast, T> {
        let main_module_id = p.main;

        // get the main module
        let main_module = p.modules.get(&main_module_id).unwrap().clone();

        // get the main function in the main module
        let (main_key, main_function) = main_module
            .functions
            .into_iter()
            .find(|(k, _)| k.id == "main")
            .unwrap()
            .clone();

        TypedProgram {
            main: "main".into(),
            modules: vec![(
                main_module_id,
                TypedModule {
                    functions: vec![(main_key, main_function)].into_iter().collect(),
                },
            )]
            .into_iter()
            .collect(),
        }
    }
}
