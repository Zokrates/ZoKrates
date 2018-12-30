extern crate serde_json;

use std::io;
use zokrates_core::compile::{compile as generic_compile, CompileError};
use zokrates_core::field::{Field, FieldPrime};
use zokrates_core::ir;

#[derive(Serialize, Deserialize)]
pub struct Tests {
    pub tests: Vec<Test>,
}

#[derive(Serialize, Deserialize)]
pub struct Test {
    pub input: Input,
    pub output: Output,
}

#[derive(Serialize, Deserialize)]
pub struct Input {
    pub values: Vec<Val>,
}

#[derive(Serialize, Deserialize)]
#[allow(non_camel_case_types)]
pub enum Output {
    success { values: Vec<Val> },
    error(String),
}

type Val = String;

pub fn compare(result: &ir::ExecutionResult<FieldPrime>, expected: &Output) -> Result<(), String> {
    match (result, expected) {
        (Ok(output), Output::success { values }) => {
            let expected_output: Vec<_> = values
                .iter()
                .map(|o| FieldPrime::from_dec_string(o.clone()))
                .collect();
            let output = output.return_values();

            if output != expected_output {
                Err(format!(
                    "
Expected {:?}
Returned {:?}
	        ",
                    expected_output, output
                ))
            } else {
                Ok(())
            }
        }
        (Err(..), Output::error(..)) => {
            // TODO check errors match
            Ok(())
        }
        (Ok(output), Output::error(..)) => Err(format!(
            "
Expected an error
Returned {:?}
           ",
            output.return_values()
        )),
        (Err(..), Output::success { .. }) => panic!(),
    }
}

pub fn read_file(path: &str) -> String {
    use std::fs::File;
    use std::io::Read;
    let mut file = File::open(format!("./tests/bench/{}", path)).expect("Unable to open the file");
    let mut contents = String::new();
    file.read_to_string(&mut contents)
        .expect("Unable to read the file");

    contents
}

pub fn compile(code: &str) -> Result<ir::Prog<FieldPrime>, CompileError<FieldPrime>> {
    generic_compile::<FieldPrime, &[u8], &[u8], io::Error>(&mut code.as_bytes(), None, None)
}

macro_rules! zokrates_test {
    ($($name:ident,)*) => {
          $(
            #[test]
            fn $name() {
            	let code = read_file(&format!("./{}.code", stringify!($name)));
            	let bin = compile(&code).unwrap();

            	let test_str = read_file(&format!("./{}.json", stringify!($name)));

            	let t: Tests = serde_json::from_str(&test_str).unwrap();

            	for test in t.tests.into_iter() {
		            let input = &test.input.values;
					let output = bin.execute(&input.iter().map(|i| FieldPrime::from_dec_string(i.clone())).collect());

					let context = format!("
{}

Called with input ({})
	        ", code, input.iter().map(|i| format!("{}", i)).collect::<Vec<_>>().join(", "));

					match compare(&output, &test.output) {
						Err(e) => panic!("{}{}", context, e),
						Ok(..) => {}
					};
		        }
            }
          )*
    };
}
