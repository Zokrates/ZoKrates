extern crate serde_json;
extern crate zokrates_field;

use std::io;
use zokrates_core::compile::{compile as generic_compile, CompileErrors};
use zokrates_core::ir;
use zokrates_field::field::{Field, FieldPrime};

#[derive(Serialize, Deserialize)]
pub struct Tests {
    pub tests: Vec<Test>,
}

#[derive(Serialize, Deserialize)]
pub struct Input {
    pub values: Vec<Val>,
}

#[derive(Serialize, Deserialize)]
pub struct Test {
    pub input: Input,
    pub output: TestResult,
}

pub type TestResult = Result<Output, ir::Error>;

#[derive(PartialEq, Debug)]
pub struct ComparableResult(Result<Vec<FieldPrime>, ir::Error>);

#[derive(Serialize, Deserialize)]
pub struct Output {
    values: Vec<Val>,
}

type Val = String;

impl From<ir::ExecutionResult<FieldPrime>> for ComparableResult {
    fn from(r: ir::ExecutionResult<FieldPrime>) -> ComparableResult {
        ComparableResult(r.map(|v| v.return_values().iter().map(|&x| x.clone()).collect()))
    }
}

impl From<TestResult> for ComparableResult {
    fn from(r: TestResult) -> ComparableResult {
        ComparableResult(r.map(|v| {
            v.values
                .into_iter()
                .map(|v| FieldPrime::from_dec_string(v))
                .collect()
        }))
    }
}

pub fn compare(
    result: ir::ExecutionResult<FieldPrime>,
    expected: TestResult,
) -> Result<(), String> {
    // extract outputs from result
    let result = ComparableResult::from(result);
    // deserialize expected result
    let expected = ComparableResult::from(expected);

    if result != expected {
        return Err(format!(
            "Expected {:?} but found {:?}",
            expected.0, result.0
        ));
    }

    Ok(())
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

pub fn compile(code: &str) -> Result<ir::Prog<FieldPrime>, CompileErrors<FieldPrime>> {
    generic_compile::<FieldPrime, &[u8], &[u8], io::Error>(&mut code.as_bytes(), None, None)
}

macro_rules! zokrates_test {
    ($($name:ident,)*) => {
          $(
            #[test]
            fn $name() {

                use zokrates_field::field::{Field, FieldPrime};

                let code_string = $crate::utils::read_file(&format!("./{}.code", stringify!($name)));
                let test_string = $crate::utils::read_file(&format!("./{}.json", stringify!($name)));

                let bin = $crate::utils::compile(&code_string).unwrap();

                let t: $crate::utils::Tests = serde_json::from_str(&test_string).unwrap();

                for test in t.tests.into_iter() {
                    let input = &test.input.values;
                    let output = bin.execute(&input.iter().map(|v| FieldPrime::from_dec_string(v.clone())).collect());

                    let context = format!("
{}

Called with input ({})
            ", code_string, input.iter().map(|i| format!("{}", i)).collect::<Vec<_>>().join(", "));

                    match $crate::utils::compare(output, test.output) {
                        Err(e) => panic!("{}{}", context, e),
                        Ok(..) => {}
                    };
                }
            }
          )*
    };
}
