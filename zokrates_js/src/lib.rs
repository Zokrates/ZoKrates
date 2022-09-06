mod util;

#[macro_use]
extern crate lazy_static;

use crate::util::normalize_path;
use serde::{Deserialize, Serialize};
use serde_json::to_string_pretty;
use std::convert::TryFrom;
use std::io::{Cursor, Write};
use std::path::{Component, PathBuf};
use typed_arena::Arena;
use wasm_bindgen::prelude::*;
use zokrates_abi::{parse_strict, Decode, Encode, Inputs};
use zokrates_ark::Ark;
use zokrates_ast::ir;
use zokrates_ast::ir::ProgEnum;
use zokrates_ast::typed::abi::Abi;
use zokrates_ast::typed::types::{ConcreteSignature, ConcreteType, GTupleType};
use zokrates_bellman::Bellman;
use zokrates_circom::{write_r1cs, write_witness};
use zokrates_common::helpers::{BackendParameter, CurveParameter, SchemeParameter};
use zokrates_common::Resolver;
use zokrates_core::compile::{
    compile as core_compile, CompilationArtifacts, CompileConfig, CompileError,
};
use zokrates_core::imports::Error;
use zokrates_field::{Bls12_377Field, Bls12_381Field, Bn128Field, Bw6_761Field, Field};
use zokrates_proof_systems::groth16::G16;
use zokrates_proof_systems::{
    Backend, Marlin, NonUniversalBackend, NonUniversalScheme, Proof, Scheme,
    SolidityCompatibleField, SolidityCompatibleScheme, TaggedKeypair, TaggedProof,
    UniversalBackend, UniversalScheme, GM17,
};

lazy_static! {
    static ref STDLIB: serde_json::Value =
        serde_json::from_str(include_str!(concat!(env!("OUT_DIR"), "/stdlib.json"))).unwrap();
}

#[wasm_bindgen]
pub struct CompilationResult {
    program: Vec<u8>,
    abi: Abi,
    snarkjs_program: Option<Vec<u8>>,
}

#[wasm_bindgen]
impl CompilationResult {
    pub fn program(&self) -> js_sys::Uint8Array {
        let arr = js_sys::Uint8Array::new_with_length(self.program.len() as u32);
        arr.copy_from(&self.program);
        arr
    }
    pub fn abi(&self) -> JsValue {
        JsValue::from_serde(&self.abi).unwrap()
    }

    pub fn snarkjs_program(&self) -> Option<js_sys::Uint8Array> {
        self.snarkjs_program.as_ref().map(|p| {
            let arr = js_sys::Uint8Array::new_with_length(p.len() as u32);
            arr.copy_from(p);
            arr
        })
    }
}

#[derive(Serialize, Deserialize)]
pub struct ResolverResult {
    source: String,
    location: String,
}

#[wasm_bindgen]
pub struct ComputationResult {
    witness: String,
    output: String,
    snarkjs_witness: Option<Vec<u8>>,
}

#[wasm_bindgen]
impl ComputationResult {
    pub fn witness(&self) -> JsValue {
        JsValue::from_str(&self.witness)
    }
    pub fn output(&self) -> JsValue {
        JsValue::from_str(&self.output)
    }
    pub fn snarkjs_witness(&self) -> Option<js_sys::Uint8Array> {
        self.snarkjs_witness.as_ref().map(|w| {
            let arr = js_sys::Uint8Array::new_with_length(w.len() as u32);
            arr.copy_from(w);
            arr
        })
    }
}

pub struct JsResolver<'a> {
    callback: &'a js_sys::Function,
}

impl<'a> JsResolver<'a> {
    pub fn new(callback: &'a js_sys::Function) -> Self {
        JsResolver { callback }
    }
}

impl<'a> Resolver<Error> for JsResolver<'a> {
    fn resolve(
        &self,
        current_location: PathBuf,
        import_location: PathBuf,
    ) -> Result<(String, PathBuf), Error> {
        let base: PathBuf = match import_location.components().next() {
            Some(Component::CurDir) | Some(Component::ParentDir) => {
                current_location.parent().unwrap().into()
            }
            _ => PathBuf::default(),
        };

        let path = base.join(import_location.clone()).with_extension("zok");

        match path.components().next() {
            Some(Component::Normal(_)) => {
                let path_normalized = normalize_path(path);
                let source = STDLIB
                    .get(&path_normalized.to_str().unwrap())
                    .ok_or_else(|| {
                        Error::new(format!(
                            "module `{}` not found in stdlib",
                            import_location.display()
                        ))
                    })?
                    .as_str()
                    .unwrap();

                Ok((source.to_owned(), path_normalized))
            }
            _ => {
                let value = self
                    .callback
                    .call2(
                        &JsValue::UNDEFINED,
                        &current_location.to_str().unwrap().into(),
                        &import_location.to_str().unwrap().into(),
                    )
                    .map_err(|_| {
                        Error::new(format!(
                            "could not resolve module `{}`",
                            import_location.display()
                        ))
                    })?;

                if value.is_null() || value.is_undefined() {
                    return Err(Error::new(format!(
                        "could not resolve module `{}`",
                        import_location.display()
                    )));
                }

                let result: serde_json::Value = value.into_serde().unwrap();
                let source = result
                    .get("source")
                    .ok_or_else(|| Error::new("missing field `source`"))?
                    .as_str()
                    .ok_or_else(|| {
                        Error::new("invalid type for field `source`, should be a string")
                    })?;

                let location = result
                    .get("location")
                    .ok_or_else(|| Error::new("missing field `location`"))?
                    .as_str()
                    .ok_or_else(|| {
                        Error::new("invalid type for field `location`, should be a string")
                    })?;

                Ok((source.to_owned(), PathBuf::from(location.to_owned())))
            }
        }
    }
}

pub struct LogWriter<'a> {
    buf: Vec<u8>,
    callback: &'a js_sys::Function,
}

impl<'a> LogWriter<'a> {
    pub fn new(callback: &'a js_sys::Function) -> Self {
        Self {
            buf: Vec::default(),
            callback,
        }
    }
}

impl<'a> Write for LogWriter<'a> {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.buf.write(buf)
    }
    fn flush(&mut self) -> std::io::Result<()> {
        self.callback
            .call1(
                &JsValue::UNDEFINED,
                &JsValue::from_str(
                    std::str::from_utf8(&self.buf.as_slice()[..self.buf.len() - 1]).unwrap(),
                ),
            )
            .map_err(|_| {
                std::io::Error::new(std::io::ErrorKind::Other, "unable to call log callback")
            })?;
        self.buf.clear();
        Ok(())
    }
}

mod internal {
    use super::*;

    pub fn compile<T: Field>(
        source: JsValue,
        location: JsValue,
        resolve_callback: &js_sys::Function,
        config: JsValue,
    ) -> Result<CompilationResult, JsValue> {
        let resolver = JsResolver::new(resolve_callback);
        let config: serde_json::Value = config.into_serde().unwrap();
        let with_snarkjs_program = config
            .get("snarkjs")
            .map(|v| *v == serde_json::Value::Bool(true))
            .unwrap_or(false);
        let config: CompileConfig = serde_json::from_value(config).unwrap_or_default();

        let fmt_error = |e: &CompileError| format!("{}:{}", e.file().display(), e.value());

        let arena = Arena::new();
        let artifacts: CompilationArtifacts<T, _> = core_compile(
            source.as_string().unwrap(),
            PathBuf::from(location.as_string().unwrap()),
            Some(&resolver),
            config,
            &arena,
        )
        .map_err(|ce| {
            JsValue::from_str(
                &ce.0
                    .iter()
                    .map(|e| fmt_error(e))
                    .collect::<Vec<_>>()
                    .join("\n"),
            )
        })?;

        let abi = artifacts.abi().clone();

        let program = artifacts.prog().collect();
        let snarkjs_program = with_snarkjs_program.then(|| {
            let mut buffer = Cursor::new(vec![]);
            write_r1cs(&mut buffer, program.clone()).unwrap();
            buffer.into_inner()
        });
        let mut buffer = Cursor::new(vec![]);
        let _ = program.serialize(&mut buffer);

        Ok(CompilationResult {
            abi,
            program: buffer.into_inner(),
            snarkjs_program,
        })
    }

    pub fn compute<T: Field>(
        program: ir::Prog<T>,
        abi: JsValue,
        args: JsValue,
        config: JsValue,
        log_callback: &js_sys::Function,
    ) -> Result<ComputationResult, JsValue> {
        let input = args.as_string().unwrap();

        let config: serde_json::Value = config.into_serde().unwrap();
        let with_snarkjs_witness = config
            .get("snarkjs")
            .map(|v| *v == serde_json::Value::Bool(true))
            .unwrap_or(false);

        let (inputs, signature) = if abi.is_object() {
            let abi: Abi = abi.into_serde().map_err(|err| {
                JsValue::from_str(&format!("Could not deserialize `abi`: {}", err))
            })?;

            let signature = abi.signature();
            let inputs = parse_strict(&input, signature.inputs.clone())
                .map(Inputs::Abi)
                .map_err(|err| JsValue::from_str(&err.to_string()))?;

            (inputs, signature)
        } else {
            let signature = ConcreteSignature::new()
                .inputs(vec![ConcreteType::FieldElement; program.arguments.len()])
                .output(ConcreteType::Tuple(GTupleType::new(
                    vec![ConcreteType::FieldElement; program.return_count],
                )));

            let inputs = parse_strict(&input, signature.inputs.clone())
                .map(Inputs::Abi)
                .map_err(|err| JsValue::from_str(&err.to_string()))?;

            (inputs, signature)
        };

        let interpreter = zokrates_interpreter::Interpreter::default();

        let public_inputs = program.public_inputs();

        let mut writer = LogWriter::new(log_callback);
        let witness = interpreter
            .execute_with_log_stream(program, &inputs.encode(), &mut writer)
            .map_err(|err| JsValue::from_str(&format!("Execution failed: {}", err)))?;

        let return_values: serde_json::Value =
            zokrates_abi::Value::decode(witness.return_values(), *signature.output)
                .into_serde_json();

        let snarkjs_witness = with_snarkjs_witness.then(|| {
            let mut buffer = Cursor::new(vec![]);
            write_witness(&mut buffer, witness.clone(), public_inputs).unwrap();
            buffer.into_inner()
        });

        Ok(ComputationResult {
            witness: format!("{}", witness),
            output: to_string_pretty(&return_values).unwrap(),
            snarkjs_witness,
        })
    }

    pub fn setup_non_universal<
        T: Field,
        S: NonUniversalScheme<T> + Serialize,
        B: NonUniversalBackend<T, S>,
    >(
        program: ir::Prog<T>,
    ) -> JsValue {
        let keypair = B::setup(program);
        let tagged_keypair = TaggedKeypair::<T, S>::new(keypair);
        JsValue::from_serde(&tagged_keypair).unwrap()
    }

    pub fn setup_universal<
        T: Field,
        I: IntoIterator<Item = ir::Statement<T>>,
        S: UniversalScheme<T> + Serialize,
        B: UniversalBackend<T, S>,
    >(
        srs: &[u8],
        program: ir::ProgIterator<T, I>,
    ) -> Result<JsValue, JsValue> {
        let keypair = B::setup(srs.to_vec(), program).map_err(|e| JsValue::from_str(&e))?;
        Ok(JsValue::from_serde(&TaggedKeypair::<T, S>::new(keypair)).unwrap())
    }

    pub fn universal_setup_of_size<T: Field, S: UniversalScheme<T>, B: UniversalBackend<T, S>>(
        size: u32,
    ) -> Vec<u8> {
        B::universal_setup(size)
    }

    pub fn generate_proof<T: Field, S: Scheme<T>, B: Backend<T, S>>(
        prog: ir::Prog<T>,
        witness: JsValue,
        pk: &[u8],
    ) -> Result<JsValue, JsValue> {
        let str_witness = witness.as_string().unwrap();
        let ir_witness: ir::Witness<T> = ir::Witness::read(str_witness.as_bytes())
            .map_err(|err| JsValue::from_str(&format!("Could not read witness: {}", err)))?;

        let proof = B::generate_proof(prog, ir_witness, pk.to_vec());
        Ok(JsValue::from_serde(&TaggedProof::<T, S>::new(proof.proof, proof.inputs)).unwrap())
    }

    pub fn verify<T: Field, S: Scheme<T>, B: Backend<T, S>>(
        vk: serde_json::Value,
        proof: serde_json::Value,
    ) -> Result<JsValue, JsValue> {
        let vk: S::VerificationKey =
            serde_json::from_value(vk).map_err(|e| JsValue::from_str(&e.to_string()))?;
        let proof: Proof<T, S> =
            serde_json::from_value(proof).map_err(|e| JsValue::from_str(&e.to_string()))?;

        let result = B::verify(vk, proof);
        Ok(JsValue::from_serde(&result).unwrap())
    }

    pub fn format_proof<T: SolidityCompatibleField, S: SolidityCompatibleScheme<T>>(
        proof: serde_json::Value,
    ) -> Result<JsValue, JsValue> {
        use serde_json::json;

        let proof: Proof<T, S> =
            serde_json::from_value(proof).map_err(|err| JsValue::from_str(&format!("{}", err)))?;

        let res = S::Proof::from(proof.proof);

        let proof_object = serde_json::to_value(&res).unwrap();
        let proof_vec = proof_object
            .as_object()
            .unwrap()
            .iter()
            .map(|(_, value)| value)
            .collect::<Vec<_>>();

        let result = if !proof.inputs.is_empty() {
            json!([proof_vec, proof.inputs])
        } else {
            json!([proof_vec])
        };

        Ok(JsValue::from_serde(&result).unwrap())
    }

    pub fn export_solidity_verifier<T: SolidityCompatibleField, S: SolidityCompatibleScheme<T>>(
        vk: serde_json::Value,
    ) -> Result<JsValue, JsValue> {
        let vk: S::VerificationKey =
            serde_json::from_value(vk).map_err(|err| JsValue::from_str(&format!("{}", err)))?;

        Ok(JsValue::from_str(&S::export_solidity_verifier(vk)))
    }
}

#[wasm_bindgen]
pub fn compile(
    source: JsValue,
    location: JsValue,
    resolve_callback: &js_sys::Function,
    config: JsValue,
    curve: JsValue,
) -> Result<CompilationResult, JsValue> {
    let curve = CurveParameter::try_from(curve.as_string().unwrap().as_str())
        .map_err(|e| JsValue::from_str(&e))?;

    match curve {
        CurveParameter::Bn128 => {
            internal::compile::<Bn128Field>(source, location, resolve_callback, config)
        }
        CurveParameter::Bls12_381 => {
            internal::compile::<Bls12_381Field>(source, location, resolve_callback, config)
        }
        CurveParameter::Bls12_377 => {
            internal::compile::<Bls12_377Field>(source, location, resolve_callback, config)
        }
        CurveParameter::Bw6_761 => {
            internal::compile::<Bw6_761Field>(source, location, resolve_callback, config)
        }
    }
}

#[wasm_bindgen]
pub fn compute_witness(
    program: &[u8],
    abi: JsValue,
    args: JsValue,
    config: JsValue,
    log_callback: &js_sys::Function,
) -> Result<ComputationResult, JsValue> {
    let prog = ir::ProgEnum::deserialize(program)
        .map_err(|err| JsValue::from_str(&err))?
        .collect();
    match prog {
        ProgEnum::Bn128Program(p) => internal::compute::<_>(p, abi, args, config, log_callback),
        ProgEnum::Bls12_381Program(p) => internal::compute::<_>(p, abi, args, config, log_callback),
        ProgEnum::Bls12_377Program(p) => internal::compute::<_>(p, abi, args, config, log_callback),
        ProgEnum::Bw6_761Program(p) => internal::compute::<_>(p, abi, args, config, log_callback),
    }
}

#[wasm_bindgen]
pub fn export_solidity_verifier(vk: JsValue) -> Result<JsValue, JsValue> {
    let vk: serde_json::Value = vk
        .into_serde()
        .map_err(|e| JsValue::from_str(&e.to_string()))?;

    let curve = CurveParameter::try_from(
        vk["curve"]
            .as_str()
            .ok_or_else(|| JsValue::from_str("Invalid verification key: missing field `curve`"))?,
    )
    .map_err(|e| JsValue::from_str(&e))?;

    let scheme =
        SchemeParameter::try_from(vk["scheme"].as_str().ok_or_else(|| {
            JsValue::from_str("Invalid verification key: missing field `scheme`")
        })?)
        .map_err(|e| JsValue::from_str(&e))?;

    match (curve, scheme) {
        (CurveParameter::Bn128, SchemeParameter::G16) => {
            internal::export_solidity_verifier::<Bn128Field, G16>(vk)
        }
        (CurveParameter::Bn128, SchemeParameter::GM17) => {
            internal::export_solidity_verifier::<Bn128Field, GM17>(vk)
        }
        (CurveParameter::Bn128, SchemeParameter::MARLIN) => {
            internal::export_solidity_verifier::<Bn128Field, Marlin>(vk)
        }
        _ => Err(JsValue::from_str("Not supported")),
    }
}

#[wasm_bindgen]
pub fn setup(program: &[u8], options: JsValue) -> Result<JsValue, JsValue> {
    let options: serde_json::Value = options.into_serde().unwrap();

    let backend = BackendParameter::try_from(
        options["backend"]
            .as_str()
            .ok_or_else(|| JsValue::from_str("Invalid options: missing field `backend`"))?,
    )
    .map_err(|e| JsValue::from_str(&e))?;

    let scheme = SchemeParameter::try_from(
        options["scheme"]
            .as_str()
            .ok_or_else(|| JsValue::from_str("Invalid options: missing field `scheme`"))?,
    )
    .map_err(|e| JsValue::from_str(&e))?;

    let prog = ir::ProgEnum::deserialize(program)
        .map_err(|err| JsValue::from_str(&err))?
        .collect();

    match (backend, scheme) {
        (BackendParameter::Bellman, SchemeParameter::G16) => match prog {
            ProgEnum::Bn128Program(p) => Ok(internal::setup_non_universal::<_, G16, Bellman>(p)),
            ProgEnum::Bls12_381Program(_) => Err(JsValue::from_str(
                "Not supported: https://github.com/Zokrates/ZoKrates/issues/1200",
            )),
            _ => Err(JsValue::from_str("Not supported")),
        },
        (BackendParameter::Ark, SchemeParameter::G16) => match prog {
            ProgEnum::Bn128Program(p) => Ok(internal::setup_non_universal::<_, G16, Ark>(p)),
            ProgEnum::Bls12_381Program(p) => Ok(internal::setup_non_universal::<_, G16, Ark>(p)),
            ProgEnum::Bls12_377Program(p) => Ok(internal::setup_non_universal::<_, G16, Ark>(p)),
            ProgEnum::Bw6_761Program(p) => Ok(internal::setup_non_universal::<_, G16, Ark>(p)),
        },
        (BackendParameter::Ark, SchemeParameter::GM17) => match prog {
            ProgEnum::Bn128Program(p) => Ok(internal::setup_non_universal::<_, GM17, Ark>(p)),
            ProgEnum::Bls12_381Program(p) => Ok(internal::setup_non_universal::<_, GM17, Ark>(p)),
            ProgEnum::Bls12_377Program(p) => Ok(internal::setup_non_universal::<_, GM17, Ark>(p)),
            ProgEnum::Bw6_761Program(p) => Ok(internal::setup_non_universal::<_, GM17, Ark>(p)),
        },
        _ => Err(JsValue::from_str("Unsupported options")),
    }
}

#[wasm_bindgen]
pub fn setup_with_srs(srs: &[u8], program: &[u8], options: JsValue) -> Result<JsValue, JsValue> {
    let options: serde_json::Value = options.into_serde().unwrap();

    let scheme = SchemeParameter::try_from(
        options["scheme"]
            .as_str()
            .ok_or_else(|| JsValue::from_str("Invalid options: missing field `scheme`"))?,
    )
    .map_err(|e| JsValue::from_str(&e))?;

    let prog = ir::ProgEnum::deserialize(program)
        .map_err(|err| JsValue::from_str(&err))?
        .collect();

    match scheme {
        SchemeParameter::MARLIN => match prog {
            ProgEnum::Bn128Program(p) => internal::setup_universal::<_, _, Marlin, Ark>(srs, p),
            ProgEnum::Bls12_381Program(p) => internal::setup_universal::<_, _, Marlin, Ark>(srs, p),
            ProgEnum::Bls12_377Program(p) => internal::setup_universal::<_, _, Marlin, Ark>(srs, p),
            ProgEnum::Bw6_761Program(p) => internal::setup_universal::<_, _, Marlin, Ark>(srs, p),
        },
        _ => Err(JsValue::from_str("Given scheme is not universal")),
    }
}

#[wasm_bindgen]
pub fn universal_setup(curve: JsValue, size: u32) -> Result<Vec<u8>, JsValue> {
    let curve = CurveParameter::try_from(curve.as_string().unwrap().as_str())
        .map_err(|e| JsValue::from_str(&e))?;

    match curve {
        CurveParameter::Bn128 => {
            Ok(internal::universal_setup_of_size::<Bn128Field, Marlin, Ark>(size))
        }
        CurveParameter::Bls12_381 => Ok(internal::universal_setup_of_size::<
            Bls12_381Field,
            Marlin,
            Ark,
        >(size)),
        CurveParameter::Bls12_377 => Ok(internal::universal_setup_of_size::<
            Bls12_377Field,
            Marlin,
            Ark,
        >(size)),
        CurveParameter::Bw6_761 => {
            Ok(internal::universal_setup_of_size::<Bw6_761Field, Marlin, Ark>(size))
        }
    }
}

#[wasm_bindgen]
pub fn generate_proof(
    program: &[u8],
    witness: JsValue,
    pk: &[u8],
    options: JsValue,
) -> Result<JsValue, JsValue> {
    let options: serde_json::Value = options.into_serde().unwrap();

    let backend = BackendParameter::try_from(
        options["backend"]
            .as_str()
            .ok_or_else(|| JsValue::from_str("Invalid options: missing field `backend`"))?,
    )
    .map_err(|e| JsValue::from_str(&e))?;

    let scheme = SchemeParameter::try_from(
        options["scheme"]
            .as_str()
            .ok_or_else(|| JsValue::from_str("Invalid options: missing field `scheme`"))?,
    )
    .map_err(|e| JsValue::from_str(&e))?;

    let prog = ir::ProgEnum::deserialize(program)
        .map_err(|err| JsValue::from_str(&err))?
        .collect();

    match (backend, scheme) {
        (BackendParameter::Bellman, SchemeParameter::G16) => match prog {
            ProgEnum::Bn128Program(p) => {
                internal::generate_proof::<_, G16, Bellman>(p, witness, pk)
            }
            ProgEnum::Bls12_381Program(_) => Err(JsValue::from_str(
                "Not supported: https://github.com/Zokrates/ZoKrates/issues/1200",
            )),
            _ => Err(JsValue::from_str("Not supported")),
        },
        (BackendParameter::Ark, SchemeParameter::G16) => match prog {
            ProgEnum::Bn128Program(p) => internal::generate_proof::<_, G16, Ark>(p, witness, pk),
            ProgEnum::Bls12_381Program(p) => {
                internal::generate_proof::<_, G16, Ark>(p, witness, pk)
            }
            ProgEnum::Bls12_377Program(p) => {
                internal::generate_proof::<_, G16, Ark>(p, witness, pk)
            }
            ProgEnum::Bw6_761Program(p) => internal::generate_proof::<_, G16, Ark>(p, witness, pk),
        },
        (BackendParameter::Ark, SchemeParameter::GM17) => match prog {
            ProgEnum::Bn128Program(p) => internal::generate_proof::<_, GM17, Ark>(p, witness, pk),
            ProgEnum::Bls12_381Program(p) => {
                internal::generate_proof::<_, GM17, Ark>(p, witness, pk)
            }
            ProgEnum::Bls12_377Program(p) => {
                internal::generate_proof::<_, GM17, Ark>(p, witness, pk)
            }
            ProgEnum::Bw6_761Program(p) => internal::generate_proof::<_, GM17, Ark>(p, witness, pk),
        },
        (BackendParameter::Ark, SchemeParameter::MARLIN) => match prog {
            ProgEnum::Bn128Program(p) => internal::generate_proof::<_, Marlin, Ark>(p, witness, pk),
            ProgEnum::Bls12_381Program(p) => {
                internal::generate_proof::<_, Marlin, Ark>(p, witness, pk)
            }
            ProgEnum::Bls12_377Program(p) => {
                internal::generate_proof::<_, Marlin, Ark>(p, witness, pk)
            }
            ProgEnum::Bw6_761Program(p) => {
                internal::generate_proof::<_, Marlin, Ark>(p, witness, pk)
            }
        },
        _ => Err(JsValue::from_str("Unsupported options")),
    }
}

#[wasm_bindgen]
pub fn verify(vk: JsValue, proof: JsValue, options: JsValue) -> Result<JsValue, JsValue> {
    let options: serde_json::Value = options.into_serde().unwrap();
    let backend = BackendParameter::try_from(
        options["backend"]
            .as_str()
            .ok_or_else(|| JsValue::from_str("Invalid options: missing field `backend`"))?,
    )
    .map_err(|e| JsValue::from_str(&e))?;

    let vk: serde_json::Value = vk.into_serde().unwrap();
    let proof: serde_json::Value = proof.into_serde().unwrap();
    let vk_curve = CurveParameter::try_from(
        vk["curve"]
            .as_str()
            .ok_or_else(|| JsValue::from_str("Invalid verification key: missing field `curve`"))?,
    )
    .map_err(|e| JsValue::from_str(&e))?;

    let vk_scheme =
        SchemeParameter::try_from(vk["scheme"].as_str().ok_or_else(|| {
            JsValue::from_str("Invalid verification key: missing field `scheme`")
        })?)
        .map_err(|e| JsValue::from_str(&e))?;

    let proof_curve = CurveParameter::try_from(
        proof["curve"]
            .as_str()
            .ok_or_else(|| JsValue::from_str("Invalid proof: missing field `curve`"))?,
    )
    .map_err(|e| JsValue::from_str(&e))?;

    let proof_scheme = SchemeParameter::try_from(
        proof["scheme"]
            .as_str()
            .ok_or_else(|| JsValue::from_str("Invalid proof: missing field `scheme`"))?,
    )
    .map_err(|e| JsValue::from_str(&e))?;

    if proof_curve != vk_curve {
        return Err(JsValue::from_str(
            "Proof and verification key should have the same curve",
        ));
    }

    if proof_scheme != vk_scheme {
        return Err(JsValue::from_str(
            "Proof and verification key should have the same scheme",
        ));
    }

    let scheme = vk_scheme;
    let curve = vk_curve;

    match (backend, scheme) {
        (BackendParameter::Bellman, SchemeParameter::G16) => match curve {
            CurveParameter::Bn128 => internal::verify::<Bn128Field, G16, Bellman>(vk, proof),
            CurveParameter::Bls12_381 => Err(JsValue::from_str(
                "Not supported: https://github.com/Zokrates/ZoKrates/issues/1200",
            )),
            _ => Err(JsValue::from_str("Not supported")),
        },
        (BackendParameter::Ark, SchemeParameter::G16) => match curve {
            CurveParameter::Bn128 => internal::verify::<Bn128Field, G16, Ark>(vk, proof),
            CurveParameter::Bls12_381 => internal::verify::<Bls12_381Field, G16, Ark>(vk, proof),
            CurveParameter::Bls12_377 => internal::verify::<Bls12_377Field, G16, Ark>(vk, proof),
            CurveParameter::Bw6_761 => internal::verify::<Bw6_761Field, G16, Ark>(vk, proof),
        },
        (BackendParameter::Ark, SchemeParameter::GM17) => match curve {
            CurveParameter::Bn128 => internal::verify::<Bn128Field, GM17, Ark>(vk, proof),
            CurveParameter::Bls12_381 => internal::verify::<Bls12_381Field, GM17, Ark>(vk, proof),
            CurveParameter::Bls12_377 => internal::verify::<Bls12_377Field, GM17, Ark>(vk, proof),
            CurveParameter::Bw6_761 => internal::verify::<Bw6_761Field, GM17, Ark>(vk, proof),
        },
        (BackendParameter::Ark, SchemeParameter::MARLIN) => match curve {
            CurveParameter::Bn128 => internal::verify::<Bn128Field, Marlin, Ark>(vk, proof),
            CurveParameter::Bls12_381 => internal::verify::<Bls12_381Field, Marlin, Ark>(vk, proof),
            CurveParameter::Bls12_377 => internal::verify::<Bls12_377Field, Marlin, Ark>(vk, proof),
            CurveParameter::Bw6_761 => internal::verify::<Bw6_761Field, Marlin, Ark>(vk, proof),
        },
        _ => Err(JsValue::from_str("Unsupported options")),
    }
}

#[wasm_bindgen]
pub fn format_proof(proof: JsValue) -> Result<JsValue, JsValue> {
    let proof: serde_json::Value = proof.into_serde().unwrap();

    let curve = CurveParameter::try_from(
        proof["curve"]
            .as_str()
            .ok_or_else(|| JsValue::from_str("Invalid proof: missing field `curve`"))?,
    )
    .map_err(|e| JsValue::from_str(&e))?;

    let scheme = SchemeParameter::try_from(
        proof["scheme"]
            .as_str()
            .ok_or_else(|| JsValue::from_str("Invalid proof: missing field `scheme`"))?,
    )
    .map_err(|e| JsValue::from_str(&e))?;

    match (curve, scheme) {
        (CurveParameter::Bn128, SchemeParameter::G16) => {
            internal::format_proof::<Bn128Field, G16>(proof)
        }
        (CurveParameter::Bn128, SchemeParameter::GM17) => {
            internal::format_proof::<Bn128Field, GM17>(proof)
        }
        (CurveParameter::Bn128, SchemeParameter::MARLIN) => {
            internal::format_proof::<Bn128Field, Marlin>(proof)
        }
        _ => Err(JsValue::from_str("Unsupported options")),
    }
}

#[wasm_bindgen(start)]
pub fn main_js() -> Result<(), JsValue> {
    std::panic::set_hook(Box::new(console_error_panic_hook::hook));
    Ok(())
}
