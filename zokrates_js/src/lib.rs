use serde::{Deserialize, Serialize};
use serde_json::to_string_pretty;
use std::io::Cursor;
use std::path::PathBuf;
use typed_arena::Arena;
use wasm_bindgen::prelude::*;
use zokrates_abi::{parse_strict, Decode, Encode, Inputs};
use zokrates_common::Resolver;
use zokrates_core::compile::{
    compile as core_compile, CompilationArtifacts, CompileConfig, CompileError,
};
use zokrates_core::imports::Error;
use zokrates_core::ir;
use zokrates_core::proof_system::bellman::Bellman;
use zokrates_core::proof_system::groth16::G16;
use zokrates_core::proof_system::{
    Backend, NonUniversalBackend, Proof, Scheme, SolidityCompatibleScheme,
};
use zokrates_core::typed_absy::abi::Abi;
use zokrates_core::typed_absy::types::ConcreteSignature as Signature;
use zokrates_field::Bn128Field;

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

#[inline]
fn deserialize_program(value: &[u8]) -> Result<ir::Prog<Bn128Field>, JsValue> {
    let prog = ir::ProgEnum::deserialize(value).map_err(|err| JsValue::from_str(&err))?;
    match prog {
        ir::ProgEnum::Bn128Program(p) => p.collect().map_err(|e| e.to_string().into()),
        _ => Err(JsValue::from_str("Unsupported binary")),
    }
}

#[inline]
fn serialize_program<I: ir::IntoStatements<Field = Bn128Field>>(
    program: ir::ProgIterator<I>,
) -> Vec<u8> {
    let mut buffer = Cursor::new(vec![]);
    program.serialize(&mut buffer).unwrap();
    buffer.into_inner()
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

#[wasm_bindgen]
pub fn compile(
    source: JsValue,
    location: JsValue,
    resolve_callback: &js_sys::Function,
    config: JsValue,
) -> Result<JsValue, JsValue> {
    let resolver = JsResolver::new(resolve_callback);
    let config: CompileConfig = config.into_serde().unwrap_or_default();

    let fmt_error = |e: &CompileError| format!("{}:{}", e.file().display(), e.value());

    let arena = Arena::new();

    let artifacts: CompilationArtifacts<_> = core_compile(
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

    let result = CompilationResult {
        abi: to_string_pretty(artifacts.abi()).unwrap(),
        program: serialize_program(artifacts.prog()),
    };

    Ok(JsValue::from_serde(&result).unwrap())
}

#[wasm_bindgen]
pub fn compute_witness(program: &[u8], abi: JsValue, args: JsValue) -> Result<JsValue, JsValue> {
    let program_flattened = deserialize_program(program)?;
    let abi: Abi = serde_json::from_str(abi.as_string().unwrap().as_str())
        .map_err(|err| JsValue::from_str(&format!("Could not deserialize abi: {}", err)))?;

    let signature: Signature = abi.signature();
    let input = args.as_string().unwrap();

    let inputs = parse_strict(&input, signature.inputs)
        .map(Inputs::Abi)
        .map_err(|why| JsValue::from_str(&why.to_string()))?;

    let interpreter = ir::Interpreter::default();

    let witness = interpreter
        .execute(program_flattened, &inputs.encode())
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
pub fn setup(program: &[u8]) -> Result<JsValue, JsValue> {
    let program_flattened = deserialize_program(program)?;
    let keypair = <Bellman as NonUniversalBackend<Bn128Field, G16>>::setup(program_flattened);
    Ok(JsValue::from_serde(&keypair).unwrap())
}

#[wasm_bindgen]
pub fn export_solidity_verifier(vk: JsValue) -> Result<JsValue, JsValue> {
    let verifier = <G16 as SolidityCompatibleScheme<Bn128Field>>::export_solidity_verifier(
        vk.into_serde().unwrap(),
    );

    Ok(JsValue::from_str(verifier.as_str()))
}

#[wasm_bindgen]
pub fn generate_proof(program: &[u8], witness: JsValue, pk: &[u8]) -> Result<JsValue, JsValue> {
    let program_flattened = deserialize_program(program)?;
    let str_witness = witness.as_string().unwrap();

    let ir_witness: ir::Witness<Bn128Field> = ir::Witness::read(str_witness.as_bytes())
        .map_err(|err| JsValue::from_str(&format!("Could not read witness: {}", err)))?;

    let proof = <Bellman as Backend<Bn128Field, G16>>::generate_proof(
        program_flattened,
        ir_witness,
        pk.to_vec(),
    );

    Ok(JsValue::from_serde(&proof).unwrap())
}

#[wasm_bindgen]
pub fn verify(vk: JsValue, proof: JsValue) -> Result<JsValue, JsValue> {
    let vk: <G16 as Scheme<Bn128Field>>::VerificationKey = vk.into_serde().unwrap();
    let proof: Proof<<G16 as Scheme<Bn128Field>>::ProofPoints> = proof.into_serde().unwrap();

    let ans = <Bellman as Backend<Bn128Field, G16>>::verify(vk, proof);
    Ok(JsValue::from_serde(&ans).unwrap())
}

#[wasm_bindgen(start)]
pub fn main_js() -> Result<(), JsValue> {
    std::panic::set_hook(Box::new(console_error_panic_hook::hook));
    Ok(())
}
