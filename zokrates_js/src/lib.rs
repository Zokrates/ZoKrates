use serde::{Deserialize, Serialize};
use serde_json::to_string_pretty;
use std::convert::TryFrom;
use std::io::Cursor;
use std::path::PathBuf;
use typed_arena::Arena;
use wasm_bindgen::prelude::*;
use zokrates_abi::{parse_strict, Decode, Encode, Inputs};
use zokrates_common::helpers::{CurveParameter, SchemeParameter};
use zokrates_common::Resolver;
use zokrates_core::compile::{
    compile as core_compile, CompilationArtifacts, CompileConfig, CompileError,
};
use zokrates_core::imports::Error;
use zokrates_core::ir;
use zokrates_core::ir::ProgEnum;
use zokrates_core::proof_system::ark::Ark;
use zokrates_core::proof_system::groth16::G16;
use zokrates_core::proof_system::{
    Backend, Marlin, NonUniversalBackend, NonUniversalScheme, Proof, Scheme,
    SolidityCompatibleField, SolidityCompatibleScheme, UniversalBackend, UniversalScheme, GM17, TaggedProof, TaggedKeypair,
};
use zokrates_core::typed_absy::abi::Abi;
use zokrates_core::typed_absy::types::{ConcreteSignature, ConcreteType};
use zokrates_field::{Bls12_377Field, Bls12_381Field, Bn128Field, Bw6_761Field, Field};

#[wasm_bindgen]
pub struct CompilationResult {
    program: Vec<u8>,
    abi: Abi,
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
}

#[derive(Serialize, Deserialize)]
pub struct ResolverResult {
    source: String,
    location: String,
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
                    "Could not resolve `{}`: error thrown in resolve callback",
                    import_location.display()
                ))
            })?;

        if value.is_null() || value.is_undefined() {
            Err(Error::new(format!(
                "Could not resolve `{}`",
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
    ) -> Result<CompilationResult, JsValue> {
        let resolver = JsResolver::new(resolve_callback);
        let config: CompileConfig = config.into_serde().unwrap_or_default();

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

        let program = artifacts.prog();
        let mut buffer = Cursor::new(vec![]);
        let _ = program.serialize(&mut buffer);

        Ok(CompilationResult {
            abi,
            program: buffer.into_inner(),
        })
    }

    pub fn compute<T: Field>(
        program: ir::Prog<T>,
        abi: JsValue,
        args: JsValue,
    ) -> Result<JsValue, JsValue> {
        let input = args.as_string().unwrap();

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
                .outputs(vec![ConcreteType::FieldElement; program.return_count]);

            let inputs = parse_strict(&input, signature.inputs.clone())
                .map(Inputs::Abi)
                .map_err(|err| JsValue::from_str(&err.to_string()))?;

            (inputs, signature)
        };

        let interpreter = ir::Interpreter::default();

        let witness = interpreter
            .execute(program, &inputs.encode())
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

    pub fn setup_non_universal<T: Field, S: NonUniversalScheme<T> + Serialize, B: NonUniversalBackend<T, S>>(
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
        let vk: S::VerificationKey = serde_json::from_value(vk).map_err(|e| JsValue::from_str(&e.to_string()))?;
        let proof: Proof<T, S> = serde_json::from_value(proof).map_err(|e| JsValue::from_str(&e.to_string()))?;

        let result = B::verify(vk, proof);
        Ok(JsValue::from_serde(&result).unwrap())
    }

    pub fn format_proof<T: SolidityCompatibleField, S: SolidityCompatibleScheme<T>>(
        proof: serde_json::Value,
    ) -> Result<JsValue, JsValue> {
        use serde_json::json;

        let proof: Proof<T, S> = serde_json::from_value(proof)
            .map_err(|err| JsValue::from_str(&format!("{}", err)))?;

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
        let vk: S::VerificationKey = serde_json::from_value(vk)
            .map_err(|err| JsValue::from_str(&format!("{}", err)))?;

        Ok(JsValue::from_str(&S::export_solidity_verifier(
            vk
        )))
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
pub fn compute_witness(program: &[u8], abi: JsValue, args: JsValue) -> Result<JsValue, JsValue> {
    let prog = ir::ProgEnum::deserialize(program)
        .map_err(|err| JsValue::from_str(&err))?
        .collect();
    match prog {
        ProgEnum::Bn128Program(p) => internal::compute::<_>(p, abi, args),
        ProgEnum::Bls12_381Program(p) => internal::compute::<_>(p, abi, args),
        ProgEnum::Bls12_377Program(p) => internal::compute::<_>(p, abi, args),
        ProgEnum::Bw6_761Program(p) => internal::compute::<_>(p, abi, args),
    }
}

#[wasm_bindgen]
pub fn export_solidity_verifier(vk: JsValue) -> Result<JsValue, JsValue> {
    let vk: serde_json::Value = vk.into_serde().map_err(|e| JsValue::from_str(&e.to_string()))?;
    let curve = CurveParameter::try_from(
        vk["curve"]
            .as_str()
            .ok_or_else(|| JsValue::from_str("Invalid verification key: missing field `curve`"))?,
    )
    .map_err(|e| JsValue::from_str(&e))?;

    let scheme = SchemeParameter::try_from(
        vk["scheme"]
            .as_str()
            .ok_or_else(|| JsValue::from_str("Invalid verification key: missing field `scheme`"))?,
    )
    .map_err(|e| JsValue::from_str(&e))?;

    match (curve, scheme) {
        (CurveParameter::Bn128, SchemeParameter::G16) => internal::export_solidity_verifier::<Bn128Field, G16>(vk),
        (CurveParameter::Bn128, SchemeParameter::GM17) => internal::export_solidity_verifier::<Bn128Field, GM17>(vk),
        (CurveParameter::Bn128, SchemeParameter::MARLIN) => internal::export_solidity_verifier::<Bn128Field, Marlin>(vk),
        _ => Err(JsValue::from_str("Not supported")),
    }
}

#[wasm_bindgen]
pub fn setup(program: &[u8], options: JsValue) -> Result<JsValue, JsValue> {
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
        SchemeParameter::G16 => match prog {
            ProgEnum::Bn128Program(p) => Ok(internal::setup_non_universal::<_, G16, Ark>(p)),
            ProgEnum::Bls12_381Program(p) => Ok(internal::setup_non_universal::<_, G16, Ark>(p)),
            ProgEnum::Bls12_377Program(p) => Ok(internal::setup_non_universal::<_, G16, Ark>(p)),
            ProgEnum::Bw6_761Program(p) => Ok(internal::setup_non_universal::<_, G16, Ark>(p)),
        },
        SchemeParameter::GM17 => match prog {
            ProgEnum::Bn128Program(p) => Ok(internal::setup_non_universal::<_, GM17, Ark>(p)),
            ProgEnum::Bls12_381Program(p) => Ok(internal::setup_non_universal::<_, GM17, Ark>(p)),
            ProgEnum::Bls12_377Program(p) => Ok(internal::setup_non_universal::<_, GM17, Ark>(p)),
            ProgEnum::Bw6_761Program(p) => Ok(internal::setup_non_universal::<_, GM17, Ark>(p)),
        },
        _ => Err(JsValue::from_str("Unsupported scheme")),
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
        SchemeParameter::G16 => match prog {
            ProgEnum::Bn128Program(p) => internal::generate_proof::<_, G16, Ark>(p, witness, pk),
            ProgEnum::Bls12_381Program(p) => {
                internal::generate_proof::<_, G16, Ark>(p, witness, pk)
            }
            ProgEnum::Bls12_377Program(p) => {
                internal::generate_proof::<_, G16, Ark>(p, witness, pk)
            }
            ProgEnum::Bw6_761Program(p) => internal::generate_proof::<_, G16, Ark>(p, witness, pk),
        },
        SchemeParameter::GM17 => match prog {
            ProgEnum::Bn128Program(p) => internal::generate_proof::<_, GM17, Ark>(p, witness, pk),
            ProgEnum::Bls12_381Program(p) => {
                internal::generate_proof::<_, GM17, Ark>(p, witness, pk)
            }
            ProgEnum::Bls12_377Program(p) => {
                internal::generate_proof::<_, GM17, Ark>(p, witness, pk)
            }
            ProgEnum::Bw6_761Program(p) => internal::generate_proof::<_, GM17, Ark>(p, witness, pk),
        },
        SchemeParameter::MARLIN => match prog {
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
        _ => Err(JsValue::from_str("Unsupported scheme")),
    }
}

#[wasm_bindgen]
pub fn verify(vk: JsValue, proof: JsValue) -> Result<JsValue, JsValue> {
    let vk: serde_json::Value = vk.into_serde().unwrap();
    let proof: serde_json::Value = proof.into_serde().unwrap();
    let vk_curve = CurveParameter::try_from(
        vk["curve"]
            .as_str()
            .ok_or_else(|| JsValue::from_str("Invalid verification key: missing field `curve`"))?,
    )
    .map_err(|e| JsValue::from_str(&e))?;

    let vk_scheme = SchemeParameter::try_from(
        vk["scheme"]
            .as_str()
            .ok_or_else(|| JsValue::from_str("Invalid verification key: missing field `scheme`"))?,
    )
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
        return Err(JsValue::from_str(&format!("Proof and verification should have the same curve")));
    }

    if proof_scheme != vk_scheme {
        return Err(JsValue::from_str(&format!("Proof and verification should have the same scheme")));
    }

    let scheme = vk_scheme;
    let curve = vk_curve;

    match scheme {
        SchemeParameter::G16 => match curve {
            CurveParameter::Bn128 => internal::verify::<Bn128Field, G16, Ark>(vk, proof),
            CurveParameter::Bls12_381 => internal::verify::<Bls12_381Field, G16, Ark>(vk, proof),
            CurveParameter::Bls12_377 => internal::verify::<Bls12_377Field, G16, Ark>(vk, proof),
            CurveParameter::Bw6_761 => internal::verify::<Bw6_761Field, G16, Ark>(vk, proof),
        },
        SchemeParameter::GM17 => match curve {
            CurveParameter::Bn128 => internal::verify::<Bn128Field, GM17, Ark>(vk, proof),
            CurveParameter::Bls12_381 => internal::verify::<Bls12_381Field, GM17, Ark>(vk, proof),
            CurveParameter::Bls12_377 => internal::verify::<Bls12_377Field, GM17, Ark>(vk, proof),
            CurveParameter::Bw6_761 => internal::verify::<Bw6_761Field, GM17, Ark>(vk, proof),
        },
        SchemeParameter::MARLIN => match curve {
            CurveParameter::Bn128 => internal::verify::<Bn128Field, Marlin, Ark>(vk, proof),
            CurveParameter::Bls12_381 => internal::verify::<Bls12_381Field, Marlin, Ark>(vk, proof),
            CurveParameter::Bls12_377 => internal::verify::<Bls12_377Field, Marlin, Ark>(vk, proof),
            CurveParameter::Bw6_761 => internal::verify::<Bw6_761Field, Marlin, Ark>(vk, proof),
        },
        _ => Err(JsValue::from_str("Unsupported scheme")),
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
