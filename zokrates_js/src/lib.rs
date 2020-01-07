use serde::{Deserialize, Serialize};
use wasm_bindgen::prelude::*;
use zokrates_abi::{parse_strict, Encode, Inputs};
use zokrates_core::compile::{compile as compile_core, CompileErrors, CompilationArtifacts};
use zokrates_core::imports::Error;
use zokrates_core::ir;
use zokrates_core::typed_absy::abi::Abi;
use zokrates_core::typed_absy::Type;
use zokrates_core::proof_system::{self, ProofSystem};
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

fn deserialize_program(value: &Vec<u8>) -> Result<ir::Prog<FieldPrime>, JsValue> {
    bincode::deserialize(&value)
        .map_err(|err| JsValue::from_str(&format!("Could not deserialize program: {}", err)))
}

#[wasm_bindgen]
pub fn compile(
    source: JsValue,
    location: JsValue,
    resolve: &js_sys::Function) -> Result<JsValue, JsValue> {

    let closure = |l: String, p: String| match resolve.call2(
        &JsValue::UNDEFINED,
        &l.into(),
        &p.clone().into(),
    ) {
        Ok(value) => {
            if value.is_null() || value.is_undefined() {
                Err(Error::new(format!("Could not resolve `{}`", p)))
            } else {
                let result: ResolverResult = value
                    .into_serde()
                    .map_err(|_| Error::new(format!("Invalid resolve object format")))?;
                Ok((result.source, result.location))
            }
        }
        Err(_) => Err(Error::new(format!(
            "Error thrown in resolve callback; could not resolve `{}`",
            p
        ))),
    };

    let result: Result<CompilationArtifacts<FieldPrime>, CompileErrors> = compile_core(
        source.as_string().unwrap(),
        location.as_string().unwrap(),
        Some(&closure),
    );

    match result {
        Ok(artifacts) => {
            let program: Vec<u8> = bincode::serialize(artifacts.prog()).unwrap();
            let abi: String = serde_json::to_string_pretty(artifacts.abi()).unwrap();

            let output: CompilationResult = CompilationResult { program, abi };
            Ok(JsValue::from_serde(&output).unwrap())
        }
        Err(ce) => Err(JsValue::from_str(&format!("{}", ce))),
    }
}

#[wasm_bindgen]
pub fn compute_witness(artifacts: JsValue, args: JsValue) -> Result<JsValue, JsValue> {
    let result: CompilationResult = artifacts.into_serde().unwrap();
    let program_flattened: ir::Prog<FieldPrime> = deserialize_program(&result.program)?;

    let abi: Abi = serde_json::from_str(result.abi.as_str())
        .map_err(|err| JsValue::from_str(&format!("Could not deserialize abi: {}", err)))?;

    let input: String = args.as_string().unwrap();
    let input_types: Vec<Type> = abi.inputs.iter().map(|i| i.ty.clone()).collect();

    let inputs = parse_strict(&input, input_types)
        .map(|parsed| Inputs::Abi(parsed))
        .map_err(|why| JsValue::from_str(&format!("{}", why.to_string())))?;

    let witness = program_flattened.execute(&inputs.encode());
    match witness {
        Ok(witness) => Ok(JsValue::from_str(&format!("{}", witness))),
        Err(error) => Err(JsValue::from_str(&format!("Execution failed: {}", error))),
    }
}

#[wasm_bindgen]
pub fn setup(program: JsValue) -> Result<JsValue, JsValue> {
    let input: Vec<u8> = program.into_serde().unwrap();
    let program_flattened: ir::Prog<FieldPrime> = deserialize_program(&input)?;
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
    let program_flattened: ir::Prog<FieldPrime> = deserialize_program(&input)?;

    let str_witness: String = witness.as_string().unwrap();
    let ir_witness: ir::Witness<FieldPrime> = ir::Witness::read(str_witness.as_bytes())
        .map_err(|err| JsValue::from_str(&format!("Could not read witness: {}", err)))?;

    let proving_key: Vec<u8> = pk.into_serde().unwrap();
    let proof: String =
        proof_system::G16 {}.generate_proof(program_flattened, ir_witness, proving_key);

    Ok(JsValue::from_str(proof.as_str()))
}

#[wasm_bindgen(start)]
pub fn main_js() -> Result<(), JsValue> {
    #[cfg(debug_assertions)]
    console_error_panic_hook::set_once();

    Ok(())
}
