#[macro_use]
extern crate serde_derive;

use std::fs::File;
use std::io::BufReader;
use std::path::{Path, PathBuf};

use zokrates_ast::typed::types::GTupleType;
use zokrates_ast::typed::ConcreteSignature;
use zokrates_ast::typed::ConcreteType;
use zokrates_core::compile::{compile, CompileConfig};

use zokrates_field::{Bls12_377Field, Bls12_381Field, Bn128Field, Bw6_761Field, Field};
use zokrates_fs_resolver::FileSystemResolver;

#[derive(Serialize, Deserialize, Clone)]
enum Curve {
    Bn128,
    Bls12_381,
    Bls12_377,
    Bw6_761,
}

#[derive(Serialize, Deserialize, Clone)]
struct Tests {
    pub entry_point: Option<PathBuf>,
    pub curves: Option<Vec<Curve>>,
    pub max_constraint_count: Option<usize>,
    pub config: Option<CompileConfig>,
    pub abi: Option<bool>,
    pub tests: Vec<Test>,
}

#[derive(Serialize, Deserialize, Clone)]
struct Input {
    pub values: Vec<Val>,
}

#[derive(Serialize, Deserialize, Clone)]
struct Test {
    pub abi: Option<bool>,
    pub input: Input,
    pub output: TestResult,
}

type TestResult = Result<Output, zokrates_interpreter::Error>;

#[derive(Serialize, Deserialize, Clone, PartialEq, Debug)]
struct Output {
    value: Val,
}

type Val = serde_json::Value;

fn try_parse_raw_val<T: Field>(s: serde_json::Value) -> Result<T, ()> {
    match s {
        serde_json::Value::String(s) => T::try_from_dec_str(&s).map_err(|_| ()),
        _ => Err(()),
    }
}

fn try_parse_abi_val<T: Field>(
    s: Vec<Val>,
    types: Vec<ConcreteType>,
) -> Result<Vec<T>, zokrates_abi::Error> {
    use zokrates_abi::Encode;
    zokrates_abi::parse_strict_json(s, types).map(|v| v.encode())
}

fn compare(
    result: Result<Output, zokrates_interpreter::Error>,
    expected: TestResult,
) -> Result<(), String> {
    if result != expected {
        return Err(format!("Expected {:?} but found {:?}", expected, result));
    }
    Ok(())
}

pub fn test_inner(test_path: &str) {
    let t: Tests =
        serde_json::from_reader(BufReader::new(File::open(Path::new(test_path)).unwrap())).unwrap();

    let curves = t.curves.clone().unwrap_or_else(|| vec![Curve::Bn128]);

    let t = Tests {
        entry_point: Some(
            t.entry_point
                .unwrap_or_else(|| PathBuf::from(String::from(test_path)).with_extension("zok")),
        ),
        ..t
    };

    // this function typically runs in a spawn thread whose stack size is small, leading to stack overflows
    // to avoid that, run the stack-heavy bit in a thread with a larger stack (8M)
    let builder = std::thread::Builder::new().stack_size(8388608);

    builder
        .spawn(move || {
            for c in &curves {
                match c {
                    Curve::Bn128 => compile_and_run::<Bn128Field>(t.clone()),
                    Curve::Bls12_381 => compile_and_run::<Bls12_381Field>(t.clone()),
                    Curve::Bls12_377 => compile_and_run::<Bls12_377Field>(t.clone()),
                    Curve::Bw6_761 => compile_and_run::<Bw6_761Field>(t.clone()),
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

fn compile_and_run<T: Field>(t: Tests) {
    let entry_point = t.entry_point.unwrap();

    let config = t.config.unwrap_or_default();

    let code = std::fs::read_to_string(&entry_point).unwrap();

    let stdlib = std::fs::canonicalize("../zokrates_stdlib/stdlib").unwrap();
    let resolver = FileSystemResolver::with_stdlib_root(stdlib.to_str().unwrap());

    let arena = typed_arena::Arena::new();

    let artifacts = compile::<T, _>(
        code.clone(),
        entry_point.clone(),
        Some(&resolver),
        config,
        &arena,
    )
    .unwrap();

    let (bin, abi) = artifacts.into_inner();
    // here we do want the program in memory because we want to run many tests on it
    let bin = bin.collect();

    if let Some(target_count) = t.max_constraint_count {
        let count = bin.constraint_count();

        assert!(
            count <= target_count,
            "{} exceeded max constraint count (actual={}, max={}, p={:.2}% of max)",
            entry_point.display(),
            count,
            target_count,
            (count as f32) / (target_count as f32) * 100_f32
        );
    };

    let interpreter = zokrates_interpreter::Interpreter::default();
    let with_abi = t.abi.unwrap_or(true);

    for test in t.tests.into_iter() {
        let with_abi = test.abi.unwrap_or(with_abi);

        let signature = if with_abi {
            abi.signature()
        } else {
            ConcreteSignature::new()
                .inputs(vec![ConcreteType::FieldElement; bin.arguments.len()])
                .output(ConcreteType::Tuple(GTupleType::new(
                    vec![ConcreteType::FieldElement; bin.return_count],
                )))
        };

        let input = if with_abi {
            try_parse_abi_val(test.input.values, signature.inputs.clone()).unwrap()
        } else {
            test.input
                .values
                .iter()
                .cloned()
                .map(try_parse_raw_val)
                .collect::<Result<Vec<_>, _>>()
                .unwrap()
        };

        let output = interpreter.execute(bin.clone(), &input);

        use zokrates_abi::Decode;

        let output: Result<Output, zokrates_interpreter::Error> = output.map(|witness| Output {
            value: zokrates_abi::Value::decode(witness.return_values(), *signature.output.clone())
                .into_serde_json(),
        });

        if let Err(e) = compare(output, test.output) {
            let context = format!(
                "\n{}\nCalled on curve {} with input ({})\n",
                code,
                T::name(),
                input
                    .iter()
                    .map(|i| i.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            panic!("{}{}", context, e)
        }
    }
}
