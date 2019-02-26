use std::path::PathBuf;
use zokrates_core::ir;
use zokrates_field::field::{Field, FieldPrime};

#[derive(Serialize, Deserialize)]
pub struct Tests {
    pub entry_point: PathBuf,
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

macro_rules! zokrates_test {
    ($($name:ident,)*) => {
          $(
            #[test]
            fn $name() {

                use zokrates_field::field::{Field, FieldPrime};
                use std::path::PathBuf;
                use zokrates_fs_resolver::resolve;
                use zokrates_core::compile::compile;
                use std::fs::File;
                use std::io::{BufReader, Read};

                let t: $crate::utils::Tests = serde_json::from_reader(
                    BufReader::new(
                        File::open(
                            &PathBuf::from("./tests/bench/").join(stringify!($name)).with_extension("json")
                        ).unwrap()
                    )
                ).unwrap();

                let mut code_reader = BufReader::new(File::open(&t.entry_point).unwrap());

                let bin = compile(
                    &mut code_reader,
                    Some(t.entry_point.parent().unwrap().to_str().unwrap().to_string()),
                    Some(resolve)
                ).unwrap();

                for test in t.tests.into_iter() {
                    let input = &test.input.values;
                    let output = bin.execute(&input.iter().map(|v| FieldPrime::from_dec_string(v.clone())).collect());

                    match $crate::utils::compare(output, test.output) {
                        Err(e) => {
                            let mut code = File::open(&t.entry_point).unwrap();
                            let mut s = String::new();
                            code.read_to_string(&mut s).unwrap();
                            let context = format!("\n{}\nCalled with input ({})\n", s, input.iter().map(|i| format!("{}", i)).collect::<Vec<_>>().join(", "));
                            panic!("{}{}", context, e)
                        },
                        Ok(..) => {}
                    };
                }
            }
          )*
    };
}
