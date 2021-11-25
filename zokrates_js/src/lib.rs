use serde::{Deserialize, Serialize};
use serde_json::to_string_pretty;
use std::convert::TryFrom;
use std::io::Cursor;
use std::path::PathBuf;
use wasm_bindgen::prelude::*;
use zokrates_abi::{parse_strict, Decode, Encode, Inputs};
use zokrates_common::helpers::{BackendParameter, CurveParameter, Parameters, SchemeParameter};
use zokrates_common::Resolver;
use zokrates_core::compile::{
    compile as core_compile, CompilationArtifacts, CompileConfig, CompileError,
};
use zokrates_core::imports::Error;
use zokrates_core::ir;
use zokrates_core::ir::ProgEnum;
use zokrates_core::proof_system::ark::Ark;
use zokrates_core::proof_system::bellman::Bellman;
use zokrates_core::proof_system::groth16::G16;
use zokrates_core::proof_system::{
    Backend, Marlin, NonUniversalBackend, NonUniversalScheme, Proof, Scheme,
    SolidityCompatibleScheme, UniversalBackend, UniversalScheme, GM17,
};
use zokrates_core::typed_absy::abi::Abi;
use zokrates_core::typed_absy::types::ConcreteSignature as Signature;
use zokrates_field::{Bls12_377Field, Bls12_381Field, Bn128Field, Bw6_761Field, Field};

#[derive(Serialize, Deserialize)]
pub struct ResolverResult {
    source: String,
    location: String,
}

#[derive(Serialize, Deserialize)]
pub struct CompilationResult {
    program: Vec<u8>,
    abi: String,
}

#[derive(Serialize, Deserialize)]
pub struct ComputationResult {
    witness: String,
    output: String,
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
        let value = self
            .callback
            .call2(
                &JsValue::UNDEFINED,
                &current_location.to_str().unwrap().into(),
                &import_location.to_str().unwrap().into(),
            )
            .map_err(|_| {
                Error::new(format!(
                    "Error thrown in JS callback: could not resolve {}",
                    import_location.display()
                ))
            })?;

        if value.is_null() || value.is_undefined() {
            Err(Error::new(format!(
                "Could not resolve {}",
                import_location.display()
            )))
        } else {
            let result: ResolverResult = value.into_serde().unwrap();
            Ok((result.source, PathBuf::from(result.location)))
        }
    }
}

mod internal {
    use super::*;

    pub fn compile<T: Field>(
        source: JsValue,
        location: JsValue,
        resolve_callback: &js_sys::Function,
        config: JsValue,
    ) -> Result<JsValue, JsValue> {
        let resolver = JsResolver::new(resolve_callback);
        let fmt_error = |e: &CompileError| format!("{}:{}", e.file().display(), e.value());

        let config: CompileConfig = config.into_serde().unwrap_or_default();
        let artifacts: CompilationArtifacts<T> = core_compile(
            source.as_string().unwrap(),
            PathBuf::from(location.as_string().unwrap()),
            Some(&resolver),
            &config,
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

        let program = artifacts.prog();
        let mut buffer = Cursor::new(vec![]);
        program.serialize(&mut buffer);

        let result = CompilationResult {
            program: buffer.into_inner(),
            abi: to_string_pretty(artifacts.abi()).unwrap(),
        };

        Ok(JsValue::from_serde(&result).unwrap())
    }

    pub fn compute<T: Field>(
        program: ir::Prog<T>,
        abi: JsValue,
        args: JsValue,
    ) -> Result<JsValue, JsValue> {
        let abi: Abi = serde_json::from_str(abi.as_string().unwrap().as_str())
            .map_err(|err| JsValue::from_str(&format!("Could not deserialize abi: {}", err)))?;

        let signature: Signature = abi.signature();
        let input = args.as_string().unwrap();

        let inputs = parse_strict(&input, signature.inputs)
            .map(Inputs::Abi)
            .map_err(|why| JsValue::from_str(&why.to_string()))?;

        let interpreter = ir::Interpreter::default();

        let witness = interpreter
            .execute(&program, &inputs.encode())
            .map_err(|err| JsValue::from_str(&format!("Execution failed: {}", err)))?;

        let return_values: serde_json::Value =
            zokrates_abi::Values::decode(witness.return_values(), signature.outputs)
                .into_serde_json();

        let result = ComputationResult {
            witness: format!("{}", witness),
            output: to_string_pretty(&return_values).unwrap(),
        };

        Ok(JsValue::from_serde(&result).unwrap())
    }

    pub fn setup_non_universal<T: Field, S: NonUniversalScheme<T>, B: NonUniversalBackend<T, S>>(
        program: ir::Prog<T>,
    ) -> JsValue {
        let keypair = B::setup(program);
        JsValue::from_serde(&keypair).unwrap()
    }

    pub fn setup_universal<T: Field, S: UniversalScheme<T>, B: UniversalBackend<T, S>>(
        srs: &[u8],
        program: ir::Prog<T>,
    ) -> Result<JsValue, JsValue> {
        let keypair = B::setup(srs.to_vec(), program).map_err(|e| JsValue::from_str(&e))?;
        Ok(JsValue::from_serde(&keypair).unwrap())
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
        Ok(JsValue::from_serde(&proof).unwrap())
    }

    pub fn verify<T: Field, S: Scheme<T>, B: Backend<T, S>>(
        vk: JsValue,
        proof: JsValue,
    ) -> Result<JsValue, JsValue> {
        let vk: S::VerificationKey = vk.into_serde().unwrap();
        let proof: Proof<S::ProofPoints> = proof.into_serde().unwrap();

        let result = B::verify(vk, proof);
        Ok(JsValue::from_serde(&result).unwrap())
    }
}

#[wasm_bindgen]
pub fn compile(
    source: JsValue,
    location: JsValue,
    resolve_callback: &js_sys::Function,
    config: JsValue,
    options: JsValue,
) -> Result<JsValue, JsValue> {
    let options: serde_json::Value = options.into_serde().unwrap();
    let curve = CurveParameter::try_from(
        options["curve"]
            .as_str()
            .ok_or_else(|| JsValue::from_str("missing field `curve` in `options` object"))?,
    )
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
pub fn compute_witness(program: &[u8], abi: JsValue, args: JsValue) -> Result<JsValue, JsValue> {
    let p = ir::ProgEnum::deserialize(program).map_err(|err| JsValue::from_str(&err))?;
    match p {
        ProgEnum::Bn128Program(p) => internal::compute::<_>(p, abi, args),
        ProgEnum::Bls12_381Program(p) => internal::compute::<_>(p, abi, args),
        ProgEnum::Bls12_377Program(p) => internal::compute::<_>(p, abi, args),
        ProgEnum::Bw6_761Program(p) => internal::compute::<_>(p, abi, args),
    }
}

#[wasm_bindgen]
pub fn export_solidity_verifier(vk: JsValue, options: JsValue) -> Result<JsValue, JsValue> {
    let options: serde_json::Value = options.into_serde().unwrap();
    let curve = CurveParameter::try_from(
        options["curve"]
            .as_str()
            .ok_or_else(|| JsValue::from_str("missing field `curve` in `options` object"))?,
    )
    .map_err(|e| JsValue::from_str(&e))?;

    let scheme = SchemeParameter::try_from(
        options["scheme"]
            .as_str()
            .ok_or_else(|| JsValue::from_str("missing field `scheme` in `options` object"))?,
    )
    .map_err(|e| JsValue::from_str(&e))?;

    let verifier = match (curve, scheme) {
        (CurveParameter::Bn128, SchemeParameter::G16) => Ok(<G16 as SolidityCompatibleScheme<
            Bn128Field,
        >>::export_solidity_verifier(
            vk.into_serde().unwrap()
        )),
        (CurveParameter::Bn128, SchemeParameter::GM17) => Ok(<GM17 as SolidityCompatibleScheme<
            Bn128Field,
        >>::export_solidity_verifier(
            vk.into_serde().unwrap()
        )),
        _ => Err(JsValue::from_str("Could not export solidity verifier")),
    }?;

    Ok(JsValue::from_str(verifier.as_str()))
}

#[wasm_bindgen]
pub fn setup(program: &[u8], options: JsValue) -> Result<JsValue, JsValue> {
    let options: serde_json::Value = options.into_serde().unwrap();
    let backend = options["backend"]
        .as_str()
        .ok_or_else(|| JsValue::from_str("missing field `backend` in `options` object"))?;

    let scheme = options["scheme"]
        .as_str()
        .ok_or_else(|| JsValue::from_str("missing field `scheme` in `options` object"))?;

    let prog = ir::ProgEnum::deserialize(program).map_err(|err| JsValue::from_str(&err))?;
    let parameters =
        Parameters::try_from((backend, prog.curve(), scheme)).map_err(|e| JsValue::from_str(&e))?;

    match parameters {
        Parameters(BackendParameter::Bellman, _, SchemeParameter::G16) => match prog {
            ProgEnum::Bn128Program(p) => Ok(internal::setup_non_universal::<_, G16, Bellman>(p)),
            ProgEnum::Bls12_381Program(p) => {
                Ok(internal::setup_non_universal::<_, G16, Bellman>(p))
            }
            _ => unreachable!(),
        },
        Parameters(BackendParameter::Ark, _, SchemeParameter::GM17) => match prog {
            ProgEnum::Bn128Program(p) => Ok(internal::setup_non_universal::<_, GM17, Ark>(p)),
            ProgEnum::Bls12_377Program(p) => Ok(internal::setup_non_universal::<_, GM17, Ark>(p)),
            ProgEnum::Bw6_761Program(p) => Ok(internal::setup_non_universal::<_, GM17, Ark>(p)),
            _ => unreachable!(),
        },
        _ => Err(JsValue::from_str("Unsupported combination of parameters")),
    }
}

#[wasm_bindgen]
pub fn setup_with_srs(srs: &[u8], program: &[u8], options: JsValue) -> Result<JsValue, JsValue> {
    let options: serde_json::Value = options.into_serde().unwrap();
    let backend = options["backend"]
        .as_str()
        .ok_or_else(|| JsValue::from_str("missing field `backend` in `options` object"))?;

    let scheme = options["scheme"]
        .as_str()
        .ok_or_else(|| JsValue::from_str("missing field `scheme` in `options` object"))?;

    let prog = ir::ProgEnum::deserialize(program).map_err(|err| JsValue::from_str(&err))?;
    let parameters =
        Parameters::try_from((backend, prog.curve(), scheme)).map_err(|e| JsValue::from_str(&e))?;

    match parameters {
        Parameters(BackendParameter::Ark, _, SchemeParameter::MARLIN) => match prog {
            ProgEnum::Bn128Program(p) => internal::setup_universal::<_, Marlin, Ark>(srs, p),
            ProgEnum::Bls12_377Program(p) => internal::setup_universal::<_, Marlin, Ark>(srs, p),
            ProgEnum::Bw6_761Program(p) => internal::setup_universal::<_, Marlin, Ark>(srs, p),
            _ => unreachable!(),
        },
        _ => Err(JsValue::from_str("Unsupported combination of parameters")),
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
        CurveParameter::Bls12_377 => Ok(internal::universal_setup_of_size::<
            Bls12_377Field,
            Marlin,
            Ark,
        >(size)),
        CurveParameter::Bw6_761 => {
            Ok(internal::universal_setup_of_size::<Bw6_761Field, Marlin, Ark>(size))
        }
        c => Err(JsValue::from_str(&format!(
            "Unsupported curve `{:?}` provided in universal setup",
            c
        ))),
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
    let backend = options["backend"]
        .as_str()
        .ok_or_else(|| JsValue::from_str("missing field `backend` in `options` object"))?;

    let scheme = options["scheme"]
        .as_str()
        .ok_or_else(|| JsValue::from_str("missing field `scheme` in `options` object"))?;

    let prog = ir::ProgEnum::deserialize(program).map_err(|err| JsValue::from_str(&err))?;
    let parameters =
        Parameters::try_from((backend, prog.curve(), scheme)).map_err(|e| JsValue::from_str(&e))?;

    match parameters {
        Parameters(BackendParameter::Bellman, _, SchemeParameter::G16) => match prog {
            ProgEnum::Bn128Program(p) => {
                internal::generate_proof::<_, G16, Bellman>(p, witness, pk)
            }
            ProgEnum::Bls12_381Program(p) => {
                internal::generate_proof::<_, G16, Bellman>(p, witness, pk)
            }
            _ => unreachable!(),
        },
        Parameters(BackendParameter::Ark, _, SchemeParameter::GM17) => match prog {
            ProgEnum::Bn128Program(p) => internal::generate_proof::<_, GM17, Ark>(p, witness, pk),
            ProgEnum::Bls12_377Program(p) => {
                internal::generate_proof::<_, GM17, Ark>(p, witness, pk)
            }
            ProgEnum::Bw6_761Program(p) => internal::generate_proof::<_, GM17, Ark>(p, witness, pk),
            _ => unreachable!(),
        },
        Parameters(BackendParameter::Ark, _, SchemeParameter::MARLIN) => match prog {
            ProgEnum::Bn128Program(p) => internal::generate_proof::<_, Marlin, Ark>(p, witness, pk),
            ProgEnum::Bls12_377Program(p) => {
                internal::generate_proof::<_, Marlin, Ark>(p, witness, pk)
            }
            ProgEnum::Bw6_761Program(p) => {
                internal::generate_proof::<_, Marlin, Ark>(p, witness, pk)
            }
            _ => unreachable!(),
        },
        _ => unreachable!(),
    }
}

#[wasm_bindgen]
pub fn verify(vk: JsValue, proof: JsValue, options: JsValue) -> Result<JsValue, JsValue> {
    let options: serde_json::Value = options.into_serde().unwrap();
    let backend = options["backend"]
        .as_str()
        .ok_or_else(|| JsValue::from_str("missing field `backend` in `options` object"))?;

    let curve = options["curve"]
        .as_str()
        .ok_or_else(|| JsValue::from_str("missing field `curve` in `options` object"))?;

    let scheme = options["scheme"]
        .as_str()
        .ok_or_else(|| JsValue::from_str("missing field `scheme` in `options` object"))?;

    let parameters = Parameters::try_from((backend, curve, scheme))?;

    match parameters {
        Parameters(BackendParameter::Bellman, CurveParameter::Bn128, SchemeParameter::G16) => {
            internal::verify::<Bn128Field, G16, Bellman>(vk, proof)
        }
        Parameters(BackendParameter::Bellman, CurveParameter::Bls12_381, SchemeParameter::G16) => {
            internal::verify::<Bls12_381Field, G16, Bellman>(vk, proof)
        }
        Parameters(BackendParameter::Ark, CurveParameter::Bls12_377, SchemeParameter::GM17) => {
            internal::verify::<Bls12_377Field, GM17, Ark>(vk, proof)
        }
        Parameters(BackendParameter::Ark, CurveParameter::Bw6_761, SchemeParameter::GM17) => {
            internal::verify::<Bw6_761Field, GM17, Ark>(vk, proof)
        }
        Parameters(BackendParameter::Ark, CurveParameter::Bn128, SchemeParameter::GM17) => {
            internal::verify::<Bn128Field, GM17, Ark>(vk, proof)
        }
        Parameters(BackendParameter::Ark, CurveParameter::Bls12_377, SchemeParameter::MARLIN) => {
            internal::verify::<Bls12_377Field, Marlin, Ark>(vk, proof)
        }
        Parameters(BackendParameter::Ark, CurveParameter::Bw6_761, SchemeParameter::MARLIN) => {
            internal::verify::<Bw6_761Field, Marlin, Ark>(vk, proof)
        }
        Parameters(BackendParameter::Ark, CurveParameter::Bn128, SchemeParameter::MARLIN) => {
            internal::verify::<Bn128Field, Marlin, Ark>(vk, proof)
        }
        _ => unreachable!(),
    }
}

#[wasm_bindgen(start)]
pub fn main_js() -> Result<(), JsValue> {
    std::panic::set_hook(Box::new(console_error_panic_hook::hook));
    Ok(())
}
