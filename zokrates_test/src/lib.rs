#[macro_use]
extern crate serde_derive;

use std::path::PathBuf;
use zokrates_core::ir;
use zokrates_field::{Bls12Field, Bn128Field, Field};

#[derive(Serialize, Deserialize)]
enum Curve {
    Bn128,
    Bls12,
}

#[derive(Serialize, Deserialize)]
struct Tests {
    pub entry_point: PathBuf,
    pub curve: Curve,
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
struct ComparableResult<T>(Result<Vec<T>, ir::Error>);

#[derive(Serialize, Deserialize)]
struct Output {
    values: Vec<Val>,
}

type Val = String;

impl<T: Field> From<ir::ExecutionResult<T>> for ComparableResult<T> {
    fn from(r: ir::ExecutionResult<T>) -> ComparableResult<T> {
        ComparableResult(r.map(|v| v.return_values()))
    }
}

impl<T: Field> From<TestResult> for ComparableResult<T> {
    fn from(r: TestResult) -> ComparableResult<T> {
        ComparableResult(r.map(|v| {
            v.values
                .iter()
                .map(|v| T::try_from_dec_str(v).unwrap())
                .collect()
        }))
    }
}

fn compare<T: Field>(result: ir::ExecutionResult<T>, expected: TestResult) -> Result<(), String> {
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

    match t.curve {
        Curve::Bn128 => compile_and_run::<Bn128Field>(t),
        Curve::Bls12 => compile_and_run::<Bls12Field>(t),
    }
}

fn compile_and_run<T: Field>(t: Tests) {
    let mut code_reader = BufReader::new(File::open(&t.entry_point).unwrap());

    let bin = compile::<T, _, _, _>(
        &mut code_reader,
        Some(
            t.entry_point
                .parent()
                .unwrap()
                .to_str()
                .unwrap()
                .to_string(),
        ),
        Some(resolve),
    )
    .unwrap();

    for test in t.tests.into_iter() {
        let input = &test.input.values;
        let output = bin.execute(
            &input
                .iter()
                .map(|v| T::try_from_dec_str(&v.clone()).unwrap())
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
