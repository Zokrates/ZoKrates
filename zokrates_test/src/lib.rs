#[macro_use]
extern crate serde_derive;

use std::fs::File;
use std::path::{Path, PathBuf};
use zokrates_core::ir;
use zokrates_field::{Bls12_377Field, Bls12_381Field, Bn128Field, Bw6_761Field, Field};

#[derive(Serialize, Deserialize, Clone)]
enum Curve {
    Bn128,
    Bls12_381,
    Bls12_377,
    Bw6_761,
}

#[derive(Serialize, Deserialize, Clone)]
struct Tests {
    pub entry_point: PathBuf,
    pub curves: Option<Vec<Curve>>,
    pub max_constraint_count: Option<usize>,
    pub tests: Vec<Test>,
}

#[derive(Serialize, Deserialize, Clone)]
struct Input {
    pub values: Vec<Val>,
}

#[derive(Serialize, Deserialize, Clone)]
struct Test {
    pub input: Input,
    pub output: TestResult,
}

type TestResult = Result<Output, ir::Error>;

#[derive(PartialEq, Debug)]
struct ComparableResult<T>(Result<Vec<T>, ir::Error>);

#[derive(Serialize, Deserialize, Clone)]
struct Output {
    values: Vec<Val>,
}

type Val = String;

fn parse_val<T: Field>(s: String) -> T {
    let s = if s.starts_with("0x") {
        u32::from_str_radix(s.trim_start_matches("0x"), 16)
            .unwrap()
            .to_string()
    } else {
        s
    };

    T::try_from_dec_str(&s).unwrap()
}

impl<T: Field> From<ir::ExecutionResult<T>> for ComparableResult<T> {
    fn from(r: ir::ExecutionResult<T>) -> ComparableResult<T> {
        ComparableResult(r.map(|v| v.return_values()))
    }
}

impl<T: Field> From<TestResult> for ComparableResult<T> {
    fn from(r: TestResult) -> ComparableResult<T> {
        ComparableResult(r.map(|v| v.values.into_iter().map(parse_val).collect()))
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
use zokrates_fs_resolver::FileSystemResolver;

pub fn test_inner(test_path: &str) {
    let t: Tests =
        serde_json::from_reader(BufReader::new(File::open(Path::new(test_path)).unwrap())).unwrap();

    let curves = t.curves.clone().unwrap_or(vec![Curve::Bn128]);

    for c in &curves {
        match c {
            Curve::Bn128 => compile_and_run::<Bn128Field>(t.clone()),
            Curve::Bls12_381 => compile_and_run::<Bls12_381Field>(t.clone()),
            Curve::Bls12_377 => compile_and_run::<Bls12_377Field>(t.clone()),
            Curve::Bw6_761 => compile_and_run::<Bw6_761Field>(t.clone()),
        }
    }
}

fn compile_and_run<T: Field>(t: Tests) {
    let code = std::fs::read_to_string(&t.entry_point).unwrap();

    let stdlib = std::fs::canonicalize("../zokrates_stdlib/stdlib").unwrap();
    let resolver = FileSystemResolver::with_stdlib_root(stdlib.to_str().unwrap());
    let artifacts = compile::<T, _>(code, t.entry_point.clone(), Some(&resolver)).unwrap();

    let bin = artifacts.prog();

    match t.max_constraint_count {
        Some(target_count) => {
            let count = bin.constraint_count();

            println!(
                "{} at {}% of max",
                t.entry_point.display(),
                (count as f32) / (target_count as f32) * 100_f32
            );
        }
        _ => {}
    };

    let interpreter = zokrates_core::ir::Interpreter::default();

    for test in t.tests.into_iter() {
        let input = &test.input.values;

        let output = interpreter.execute(bin, &(input.iter().cloned().map(parse_val).collect()));

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
                        .map(|i| i.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                );
                panic!("{}{}", context, e)
            }
            Ok(..) => {}
        };
    }
}
