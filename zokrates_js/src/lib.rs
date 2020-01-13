use bincode::{deserialize, serialize};
use serde::{Deserialize, Serialize};
use serde_json::to_string_pretty;
use wasm_bindgen::prelude::*;
use zokrates_abi::{parse_strict, Encode, Inputs};
use zokrates_core::compile::{compile as core_compile, CompilationArtifacts};
use zokrates_core::imports::Error;
use zokrates_core::ir;
use zokrates_core::proof_system::{self, ProofSystem};
use zokrates_core::typed_absy::abi::Abi;
use zokrates_core::typed_absy::Type;
use zokrates_field::field::FieldPrime;

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

impl ResolverResult {
    fn to_tuple(&self) -> (String, String) {
        (self.source.clone(), self.location.clone())
    }
}

#[inline]
fn deserialize_program(value: &Vec<u8>) -> Result<ir::Prog<FieldPrime>, JsValue> {
    deserialize(&value)
        .map_err(|err| JsValue::from_str(&format!("Could not deserialize program: {}", err)))
}

#[inline]
fn serialize_program(program: &ir::Prog<FieldPrime>) -> Result<Vec<u8>, JsValue> {
    serialize(program)
        .map_err(|err| JsValue::from_str(&format!("Could not serialize program: {}", err)))
}

#[wasm_bindgen]
pub fn compile(
    source: JsValue,
    location: JsValue,
    resolve: &js_sys::Function,
) -> Result<JsValue, JsValue> {
    let closure = |l: String, p: String| {
        let value = resolve
            .call2(&JsValue::UNDEFINED, &l.into(), &p.clone().into())
            .map_err(|_| {
                Error::new(format!(
                    "Error thrown in callback: Could not resolve `{}`",
                    p
                ))
            })?;

        if value.is_null() || value.is_undefined() {
            Err(Error::new(format!("Could not resolve `{}`", p)))
        } else {
            let result: ResolverResult = value.into_serde().unwrap();
            Ok(result.to_tuple())
        }
    };

    let artifacts: CompilationArtifacts<FieldPrime> = core_compile(
        source.as_string().unwrap(),
        location.as_string().unwrap(),
        Some(&closure),
    )
    .map_err(|ce| JsValue::from_str(&format!("{}", ce)))?;

    let result = CompilationResult {
        program: serialize_program(artifacts.prog())?,
        abi: to_string_pretty(artifacts.abi()).unwrap(),
    };

    Ok(JsValue::from_serde(&result).unwrap())
}

#[wasm_bindgen]
pub fn compute_witness(artifacts: JsValue, args: JsValue) -> Result<JsValue, JsValue> {
    let result: CompilationResult = artifacts.into_serde().unwrap();
    let program_flattened = deserialize_program(&result.program)?;

    let abi: Abi = serde_json::from_str(result.abi.as_str())
        .map_err(|err| JsValue::from_str(&format!("Could not deserialize abi: {}", err)))?;

    let input = args.as_string().unwrap();
    let input_types: Vec<Type> = abi.inputs.iter().map(|i| i.ty.clone()).collect();

    let inputs = parse_strict(&input, input_types)
        .map(|parsed| Inputs::Abi(parsed))
        .map_err(|why| JsValue::from_str(&format!("{}", why.to_string())))?;

    program_flattened
        .execute(&inputs.encode())
        .map(|witness| JsValue::from_str(&format!("{}", witness)))
        .map_err(|err| JsValue::from_str(&format!("Execution failed: {}", err)))
}

#[wasm_bindgen]
pub fn setup(program: JsValue) -> Result<JsValue, JsValue> {
    let input: Vec<u8> = program.into_serde().unwrap();
    let program_flattened = deserialize_program(&input)?;
    let keypair = proof_system::G16 {}.setup(program_flattened);
    Ok(JsValue::from_serde(&keypair).unwrap())
}

#[wasm_bindgen]
pub fn export_solidity_verifier(vk: JsValue, is_abiv2: JsValue) -> JsValue {
    let verifier = proof_system::G16 {}
        .export_solidity_verifier(vk.as_string().unwrap(), is_abiv2.as_bool().unwrap());
    JsValue::from_str(verifier.as_str())
}

#[wasm_bindgen]
pub fn generate_proof(program: JsValue, witness: JsValue, pk: JsValue) -> Result<JsValue, JsValue> {
    let input: Vec<u8> = program.into_serde().unwrap();
    let program_flattened = deserialize_program(&input)?;

    let str_witness = witness.as_string().unwrap();
    let ir_witness: ir::Witness<FieldPrime> = ir::Witness::read(str_witness.as_bytes())
        .map_err(|err| JsValue::from_str(&format!("Could not read witness: {}", err)))?;

    let proving_key: Vec<u8> = pk.into_serde().unwrap();
    let proof = proof_system::G16 {}.generate_proof(program_flattened, ir_witness, proving_key);

    Ok(JsValue::from_str(proof.as_str()))
}

#[wasm_bindgen(start)]
pub fn main_js() -> Result<(), JsValue> {
    #[cfg(debug_assertions)]
    console_error_panic_hook::set_once();

    Ok(())
}
