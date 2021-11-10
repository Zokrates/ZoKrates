use serde::{Deserialize, Serialize};
use serde_json::to_string_pretty;
use std::io::Cursor;
use std::path::PathBuf;
use wasm_bindgen::prelude::*;
use zokrates_abi::{parse_strict, Decode, Encode, Inputs};
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

pub fn setup<T: Field, S: NonUniversalScheme<T>, B: NonUniversalBackend<T, S>>(
    program: ir::Prog<T>,
) -> JsValue {
    let keypair = B::setup(program);
    JsValue::from_serde(&keypair).unwrap()
}

pub fn setup_with_srs<T: Field, S: UniversalScheme<T>, B: UniversalBackend<T, S>>(
    srs: &[u8],
    program: ir::Prog<T>,
) -> Result<JsValue, JsValue> {
    let keypair = B::setup(srs.to_vec(), program).map_err(|e| JsValue::from_str(&e))?;
    Ok(JsValue::from_serde(&keypair).unwrap())
}

pub fn universal_setup<T: Field, S: UniversalScheme<T>, B: UniversalBackend<T, S>>(
    size: u32,
) -> JsValue {
    let keypair = B::universal_setup(size);
    JsValue::from_serde(&keypair).unwrap()
}

fn generate_proof<T: Field, S: Scheme<T>, B: Backend<T, S>>(
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

fn verify<T: Field, S: Scheme<T>, B: Backend<T, S>>(
    vk: JsValue,
    proof: JsValue,
) -> Result<JsValue, JsValue> {
    let vk: S::VerificationKey = vk.into_serde().unwrap();
    let proof: Proof<S::ProofPoints> = proof.into_serde().unwrap();

    let result = B::verify(vk, proof);
    Ok(JsValue::from_serde(&result).unwrap())
}

pub fn compile_source<T: Field>(
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

fn compute<T: Field>(
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
        zokrates_abi::Values::decode(witness.return_values(), signature.outputs).into_serde_json();

    let result = ComputationResult {
        witness: format!("{}", witness),
        output: to_string_pretty(&return_values).unwrap(),
    };

    Ok(JsValue::from_serde(&result).unwrap())
}

#[wasm_bindgen]
pub fn compile(
    curve: JsValue,
    source: JsValue,
    location: JsValue,
    resolve_callback: &js_sys::Function,
    config: JsValue,
) -> Result<JsValue, JsValue> {
    match curve.as_string().unwrap().as_str() {
        "bn128" => compile_source::<Bn128Field>(source, location, resolve_callback, config),
        "bls12_381" => compile_source::<Bls12_381Field>(source, location, resolve_callback, config),
        "bls12_377" => compile_source::<Bls12_377Field>(source, location, resolve_callback, config),
        "bw6_761" => compile_source::<Bw6_761Field>(source, location, resolve_callback, config),
        _ => unreachable!(),
    }
}

#[wasm_bindgen]
pub fn compute_witness(program: &[u8], abi: JsValue, args: JsValue) -> Result<JsValue, JsValue> {
    let p = ir::ProgEnum::deserialize(program).map_err(|err| JsValue::from_str(&err))?;
    match p {
        ProgEnum::Bn128Program(p) => compute::<_>(p, abi, args),
        ProgEnum::Bls12_381Program(p) => compute::<_>(p, abi, args),
        ProgEnum::Bls12_377Program(p) => compute::<_>(p, abi, args),
        ProgEnum::Bw6_761Program(p) => compute::<_>(p, abi, args),
    }
}

#[wasm_bindgen]
pub fn bellman_groth16_export_solidity_verifier(vk: JsValue) -> Result<JsValue, JsValue> {
    let verifier = <G16 as SolidityCompatibleScheme<Bn128Field>>::export_solidity_verifier(
        vk.into_serde().unwrap(),
    );
    Ok(JsValue::from_str(verifier.as_str()))
}

#[wasm_bindgen]
pub fn bellman_groth16_setup(program: &[u8]) -> Result<JsValue, JsValue> {
    let p = ir::ProgEnum::deserialize(program).map_err(|err| JsValue::from_str(&err))?;
    match p {
        ProgEnum::Bn128Program(p) => Ok(setup::<_, G16, Bellman>(p)),
        ProgEnum::Bls12_381Program(p) => Ok(setup::<_, G16, Bellman>(p)),
        _ => unreachable!(), // TODO: reachable
    }
}

#[wasm_bindgen]
pub fn ark_gm17_setup(program: &[u8]) -> Result<JsValue, JsValue> {
    let p = ir::ProgEnum::deserialize(program).map_err(|err| JsValue::from_str(&err))?;
    match p {
        ProgEnum::Bn128Program(p) => Ok(setup::<_, GM17, Ark>(p)),
        ProgEnum::Bls12_377Program(p) => Ok(setup::<_, GM17, Ark>(p)),
        ProgEnum::Bw6_761Program(p) => Ok(setup::<_, GM17, Ark>(p)),
        _ => unreachable!(), // TODO: reachable
    }
}

#[wasm_bindgen]
pub fn ark_marlin_setup(srs: &[u8], program: &[u8]) -> Result<JsValue, JsValue> {
    let p = ir::ProgEnum::deserialize(program).map_err(|err| JsValue::from_str(&err))?;
    match p {
        ProgEnum::Bn128Program(p) => setup_with_srs::<_, Marlin, Ark>(srs, p),
        ProgEnum::Bls12_377Program(p) => setup_with_srs::<_, Marlin, Ark>(srs, p),
        ProgEnum::Bw6_761Program(p) => setup_with_srs::<_, Marlin, Ark>(srs, p),
        _ => unreachable!(), // TODO: reachable
    }
}

#[wasm_bindgen]
pub fn ark_marlin_universal_setup(curve: JsValue, size: u32) -> Result<JsValue, JsValue> {
    match curve.as_string().unwrap().as_str() {
        "bn128" => Ok(universal_setup::<Bn128Field, Marlin, Ark>(size)),
        "bls12_377" => Ok(universal_setup::<Bls12_377Field, Marlin, Ark>(size)),
        "bw6_761" => Ok(universal_setup::<Bw6_761Field, Marlin, Ark>(size)),
        _ => unreachable!(),
    }
}

#[wasm_bindgen]
pub fn bellman_groth16_generate_proof(
    program: &[u8],
    witness: JsValue,
    pk: &[u8],
) -> Result<JsValue, JsValue> {
    let p = ir::ProgEnum::deserialize(program).map_err(|err| JsValue::from_str(&err))?;
    match p {
        ProgEnum::Bn128Program(p) => generate_proof::<_, G16, Bellman>(p, witness, pk),
        ProgEnum::Bls12_381Program(p) => generate_proof::<_, G16, Bellman>(p, witness, pk),
        _ => unreachable!(), // TODO: reachable
    }
}

#[wasm_bindgen]
pub fn ark_gm17_generate_proof(
    program: &[u8],
    witness: JsValue,
    pk: &[u8],
) -> Result<JsValue, JsValue> {
    let p = ir::ProgEnum::deserialize(program).map_err(|err| JsValue::from_str(&err))?;
    match p {
        ProgEnum::Bn128Program(p) => generate_proof::<_, GM17, Ark>(p, witness, pk),
        ProgEnum::Bls12_377Program(p) => generate_proof::<_, GM17, Ark>(p, witness, pk),
        ProgEnum::Bw6_761Program(p) => generate_proof::<_, GM17, Ark>(p, witness, pk),
        _ => unreachable!(), // TODO: reachable
    }
}

#[wasm_bindgen]
pub fn ark_marlin_generate_proof(
    program: &[u8],
    witness: JsValue,
    pk: &[u8],
) -> Result<JsValue, JsValue> {
    let p = ir::ProgEnum::deserialize(program).map_err(|err| JsValue::from_str(&err))?;
    match p {
        ProgEnum::Bn128Program(p) => generate_proof::<_, Marlin, Ark>(p, witness, pk),
        ProgEnum::Bls12_377Program(p) => generate_proof::<_, Marlin, Ark>(p, witness, pk),
        ProgEnum::Bw6_761Program(p) => generate_proof::<_, Marlin, Ark>(p, witness, pk),
        _ => unreachable!(), // TODO: reachable
    }
}

#[wasm_bindgen]
pub fn bellman_groth16_verify(
    vk: JsValue,
    proof: JsValue,
    curve: JsValue,
) -> Result<JsValue, JsValue> {
    match curve.as_string().unwrap().as_str() {
        "bn128" => verify::<Bn128Field, G16, Bellman>(vk, proof),
        "bls12_381" => verify::<Bls12_381Field, G16, Bellman>(vk, proof),
        _ => unreachable!(), // TODO: reachable
    }
}

#[wasm_bindgen]
pub fn ark_gm17_verify(vk: JsValue, proof: JsValue, curve: JsValue) -> Result<JsValue, JsValue> {
    match curve.as_string().unwrap().as_str() {
        "bn128" => verify::<Bn128Field, GM17, Ark>(vk, proof),
        "bls12_377" => verify::<Bls12_377Field, GM17, Ark>(vk, proof),
        "bw6_761" => verify::<Bw6_761Field, GM17, Ark>(vk, proof),
        _ => unreachable!(), // TODO: reachable
    }
}

#[wasm_bindgen]
pub fn ark_marlin_verify(vk: JsValue, proof: JsValue, curve: JsValue) -> Result<JsValue, JsValue> {
    match curve.as_string().unwrap().as_str() {
        "bn128" => verify::<Bn128Field, Marlin, Ark>(vk, proof),
        "bls12_377" => verify::<Bls12_377Field, Marlin, Ark>(vk, proof),
        "bw6_761" => verify::<Bw6_761Field, Marlin, Ark>(vk, proof),
        _ => unreachable!(), // TODO: reachable
    }
}

#[wasm_bindgen(start)]
pub fn main_js() -> Result<(), JsValue> {
    std::panic::set_hook(Box::new(console_error_panic_hook::hook));
    Ok(())
}
