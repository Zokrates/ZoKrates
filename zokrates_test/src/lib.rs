#[macro_use]
extern crate serde_derive;

use std::path::PathBuf;
use zokrates_core::ir;
use zokrates_field::field::{Field, FieldPrime};

#[derive(Serialize, Deserialize)]
struct Tests {
    pub entry_point: PathBuf,
    pub tests: Vec<Test>,
}

#[derive(Serialize, Deserialize)]
struct Input {
    pub values: Vec<Val>,
}

#[derive(Serialize, Deserialize)]
struct Test {
    pub input: Input,
    pub output: TestResult,
}

type TestResult = Result<Output, ir::Error>;

#[derive(PartialEq, Debug)]
struct ComparableResult(Result<Vec<FieldPrime>, ir::Error>);

#[derive(Serialize, Deserialize)]
struct Output {
    values: Vec<Val>,
}

type Val = String;

impl From<ir::ExecutionResult<FieldPrime>> for ComparableResult {
    fn from(r: ir::ExecutionResult<FieldPrime>) -> ComparableResult {
        ComparableResult(r.map(|v| v.return_values()))
    }
}

impl From<TestResult> for ComparableResult {
    fn from(r: TestResult) -> ComparableResult {
        ComparableResult(r.map(|v| {
            v.values
                .iter()
                .map(|v| FieldPrime::try_from_dec_str(v).unwrap())
                .collect()
        }))
    }
}

fn compare(result: ir::ExecutionResult<FieldPrime>, expected: TestResult) -> Result<(), String> {
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

use std::io::{BufReader, Read};
use zokrates_core::compile::compile;
use zokrates_fs_resolver::resolve;

pub fn test_inner(test_path: &str) {
    let t: Tests =
        serde_json::from_reader(BufReader::new(File::open(Path::new(test_path)).unwrap())).unwrap();

    let code = std::fs::read_to_string(&t.entry_point).unwrap();

    let artifacts = compile(code, t.entry_point.clone(), Some(&resolve)).unwrap();

    let bin = artifacts.prog();

    for test in t.tests.into_iter() {
        let input = &test.input.values;
        let output = bin.execute(
            &input
                .iter()
                .map(|v| FieldPrime::try_from_dec_str(&v.clone()).unwrap())
                .collect(),
        );

        match compare(output, test.output) {
            Err(e) => {
                let mut code = File::open(&t.entry_point).unwrap();
                let mut s = String::new();
                code.read_to_string(&mut s).unwrap();
                let context = format!(
                    "\n{}\nCalled with input ({})\n",
                    s,
                    input
                        .iter()
                        .map(|i| format!("{}", i))
                        .collect::<Vec<_>>()
                        .join(", ")
                );
                panic!("{}{}", context, e)
            }
            Ok(..) => {}
        };
    }
}

use std::env;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

pub fn write_tests(base: &str) {
    use glob::glob;

    let base = Path::new(&base);
    let out_dir = env::var("OUT_DIR").unwrap();
    let destination = Path::new(&out_dir).join("tests.rs");
    let test_file = File::create(&destination).unwrap();
    let mut writer = BufWriter::new(test_file);

    for p in glob(base.join("**/*.json").to_str().unwrap()).unwrap() {
        write_test(&mut writer, &p.unwrap(), &base);
    }
}

fn write_test<W: Write>(test_file: &mut W, test_path: &Path, base_path: &Path) {
    println!("{:?}", test_path);
    println!("{:?}", base_path);

    let test_name = format!(
        "test_{}",
        test_path
            .strip_prefix(base_path.strip_prefix("./").unwrap())
            .unwrap()
            .display()
            .to_string()
            .replace("/", "_")
            .replace(".json", "")
            .replace(".", "")
    );

    write!(
        test_file,
        include_str!("../test_template"),
        test_name = test_name,
        test_path = test_path.display()
    )
    .unwrap();
}
