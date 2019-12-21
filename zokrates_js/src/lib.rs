use serde::{Deserialize, Serialize};
use wasm_bindgen::prelude::*;
use zokrates_abi::{parse_strict, Encode, Inputs};
use zokrates_core::compile::{compile as compile_core, CompileErrors};
use zokrates_core::imports::Error;
use zokrates_core::ir;
use zokrates_core::proof_system::{self, ProofSystem};
use zokrates_field::field::FieldPrime;

#[derive(Serialize, Deserialize)]
pub struct ResolverResult {
    source: String,
    location: String,
}

fn deserialize_program(input: &JsValue) -> ir::Prog<FieldPrime> {
    let vec: Vec<u8> = input.into_serde().unwrap();
    bincode::deserialize(&vec).unwrap()
}

#[wasm_bindgen]
pub fn compile(
    source: JsValue,
    location: JsValue,
    resolve: &js_sys::Function,
) -> Result<JsValue, JsValue> {
    let closure = |l: String, p: String| match resolve.call2(
        &JsValue::UNDEFINED,
        &l.into(),
        &p.clone().into(),
    ) {
        Ok(value) => {
            let result: ResolverResult = value
                .into_serde()
                .map_err(|_| Error::new(format!("Could not resolve `{}`", p)))?;
            Ok((result.source, result.location))
        }
        Err(_) => Err(Error::new(format!(
            "Error thrown in resolve callback; could not resolve `{}`",
            p
        ))),
    };

    let program_flattened: Result<ir::Prog<FieldPrime>, CompileErrors> = compile_core(
        source.as_string().unwrap(),
        location.as_string().unwrap(),
        Some(&closure),
    );

    match program_flattened {
        Ok(p) => {
            let data: Vec<u8> = bincode::serialize(&p).unwrap();
            Ok(JsValue::from_serde(&data).unwrap())
        }
        Err(ce) => Err(JsValue::from_str(&format!("{}", ce))),
    }
}

#[wasm_bindgen]
pub fn compute_witness(program: JsValue, args: JsValue) -> Result<JsValue, JsValue> {
    let program_flattened = deserialize_program(&program);

    let input: String = args.as_string().unwrap();
    let signature = program_flattened.signature.clone();

    let arguments = parse_strict(&input, signature.inputs)
        .map(|parsed| Inputs::Abi(parsed))
        .map_err(|why| why.to_string());

    match arguments {
        Ok(inputs) => {
            let witness = program_flattened.execute(&inputs.encode());
            match witness {
                Ok(witness) => Ok(JsValue::from_str(&format!("{}", witness))),
                Err(error) => Err(JsValue::from_str(&format!("Execution failed: {}", error))),
            }
        }
        Err(err) => Err(JsValue::from_str(&format!("{}", err))),
    }
}

#[wasm_bindgen]
pub fn setup(program: JsValue) -> JsValue {
    let program_flattened = deserialize_program(&program);
    let keypair = proof_system::G16 {}.setup(program_flattened);
    JsValue::from_serde(&keypair).unwrap()
}

#[wasm_bindgen]
pub fn export_solidity_verifier(vk: JsValue, is_abiv2: JsValue) -> JsValue {
    let verifier = proof_system::G16 {}
        .export_solidity_verifier(vk.as_string().unwrap(), is_abiv2.as_bool().unwrap());
    JsValue::from_str(verifier.as_str())
}

#[wasm_bindgen]
pub fn generate_proof(program: JsValue, witness: JsValue, pk: JsValue) -> JsValue {
    let program_flattened = deserialize_program(&program);
    let str_witness: String = witness.as_string().unwrap();
    let witness_out: ir::Witness<FieldPrime> = ir::Witness::read(str_witness.as_bytes()).unwrap();
    let proving_key: Vec<u8> = pk.into_serde().unwrap();

    let proof: String =
        proof_system::G16 {}.generate_proof(program_flattened, witness_out, proving_key);
    JsValue::from_str(proof.as_str())
}

#[wasm_bindgen(start)]
pub fn main_js() -> Result<(), JsValue> {
    #[cfg(debug_assertions)]
    console_error_panic_hook::set_once();

    Ok(())
}
