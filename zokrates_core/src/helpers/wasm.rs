use helpers::{Executable, Signed};
use std::fmt;

use rustc_hex::FromHex;
use serde::{Deserialize, Deserializer};
use std::rc::Rc;
use wasmi::{ImportsBuilder, ModuleInstance, ModuleRef, NopExternals};
use zokrates_field::field::Field;

#[derive(Clone, Debug, Serialize)]
pub struct WasmHelper(
    #[serde(skip)] std::rc::Rc<ModuleRef>,
    #[serde(serialize_with = "serde_bytes::serialize")] Vec<u8>,
);

impl WasmHelper {
    // Hand-coded assembly for identity.
    // Source available at https://gist.github.com/gballet/f14d11053d8f846bfbb3687581b0eecb#file-identity-wast
    pub const IDENTITY_WASM: &'static str = "0061736d010000000105016000017f030302000005030100010615047f0041010b7f0041010b7f0041200b7f0141000b074b06066d656d6f727902000e6765745f696e707574735f6f6666000105736f6c766500000a6d696e5f696e7075747303000b6d696e5f6f75747075747303010a6669656c645f73697a6503020a2c0225000340412023036a410023036a280200360200230341016a240323032302470d000b41200b040041000b0b4b020041000b20ffffffff000000000000000000000000ffffffff0000000000000000000000000041200b20deadbeef000000000000000000000000deadbeef000000000000000000000000";
    // Generated from C code, normalized and cleaned up by hand.
    // Source available at https://gist.github.com/gballet/f14d11053d8f846bfbb3687581b0eecb#file-bits_v2-c
    pub const BITS_WASM: &'static [u8] = &[
        0, 97, 115, 109, 1, 0, 0, 0, 1, 8, 2, 96, 0, 0, 96, 0, 1, 127, 3, 5, 4, 0, 1, 1, 1, 4, 5,
        1, 112, 1, 1, 1, 5, 3, 1, 0, 2, 6, 38, 6, 127, 1, 65, 240, 199, 4, 11, 127, 0, 65, 240,
        199, 4, 11, 127, 0, 65, 240, 199, 0, 11, 127, 0, 65, 32, 11, 127, 0, 65, 1, 11, 127, 0, 65,
        254, 1, 11, 7, 109, 9, 6, 109, 101, 109, 111, 114, 121, 2, 0, 11, 95, 95, 104, 101, 97,
        112, 95, 98, 97, 115, 101, 3, 1, 10, 95, 95, 100, 97, 116, 97, 95, 101, 110, 100, 3, 2, 14,
        103, 101, 116, 95, 105, 110, 112, 117, 116, 115, 95, 111, 102, 102, 0, 1, 5, 115, 111, 108,
        118, 101, 0, 2, 4, 109, 97, 105, 110, 0, 3, 10, 102, 105, 101, 108, 100, 95, 115, 105, 122,
        101, 3, 3, 10, 109, 105, 110, 95, 105, 110, 112, 117, 116, 115, 3, 4, 11, 109, 105, 110,
        95, 111, 117, 116, 112, 117, 116, 115, 3, 5, 9, 1, 0, 10, 85, 4, 3, 0, 1, 11, 5, 0, 65,
        144, 8, 11, 68, 1, 2, 127, 65, 253, 1, 33, 0, 65, 176, 8, 33, 1, 3, 64, 32, 1, 65, 1, 32,
        0, 65, 7, 113, 116, 32, 0, 65, 3, 118, 65, 144, 8, 106, 45, 0, 0, 113, 65, 0, 71, 58, 0, 0,
        32, 1, 65, 32, 106, 33, 1, 32, 0, 65, 127, 106, 34, 0, 65, 127, 71, 13, 0, 11, 65, 176, 8,
        11, 4, 0, 65, 0, 11, 11, 19, 1, 0, 65, 128, 8, 11, 12, 32, 0, 0, 0, 1, 0, 0, 0, 254, 0, 0,
        0,
    ];

    pub fn from_hex<U: Into<String>>(u: U) -> Self {
        let code_hex = u.into();
        let code = FromHex::from_hex(&code_hex[..])
            .expect(format!("invalid bytecode: {}", code_hex).as_str());
        WasmHelper::from(code)
    }
}

impl<U: Into<Vec<u8>>> From<U> for WasmHelper {
    fn from(code: U) -> Self {
        let code_vec = code.into();
        let module = wasmi::Module::from_buffer(code_vec.clone()).expect("Error decoding buffer");
        let modinst = ModuleInstance::new(&module, &ImportsBuilder::default())
            .expect("Failed to instantiate module")
            .assert_no_start();
        WasmHelper(Rc::new(modinst), code_vec)
    }
}

impl<'de> Deserialize<'de> for WasmHelper {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let hex: Vec<u8> = serde_bytes::deserialize(deserializer)?;
        Ok(WasmHelper::from(hex))
    }
}

impl PartialEq for WasmHelper {
    fn eq(&self, other: &WasmHelper) -> bool {
        self.1 == other.1
    }
}

impl fmt::Display for WasmHelper {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Hex(\"{:?}\")", &self.1[..])
    }
}

fn get_export<T: wasmi::FromRuntimeValue>(varname: &str, modref: &ModuleRef) -> Result<T, String> {
    modref
        .export_by_name(varname)
        .ok_or(&format!("Could not find exported symbol `{}` in module", varname)[..])?
        .as_global()
        .ok_or(format!(
            "Error getting {} from the list of globals",
            varname
        ))?
        .get()
        .try_into::<T>()
        .ok_or(format!("Error converting `{}` to i32", varname))
}

impl Signed for WasmHelper {
    fn get_signature(&self) -> (usize, usize) {
        // Check that the module has the following exports:
        //  * min_inputs = the (minimum) number of inputs
        //  * min_outputs = the (minimum) number of outputs
        let ni = get_export::<i32>("min_inputs", self.0.as_ref()).unwrap();
        let no = get_export::<i32>("min_outputs", self.0.as_ref()).unwrap();

        (ni as usize, no as usize)
    }
}

impl<T: Field> Executable<T> for WasmHelper {
    fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, String> {
        let field_size = get_export::<i32>("field_size", self.0.as_ref())? as usize;
        let ninputs = get_export::<i32>("min_inputs", self.0.as_ref())? as usize;

        if ninputs != inputs.len() {
            return Err(format!(
                "`solve` expected {} inputs, received {}",
                ninputs,
                inputs.len()
            ));
        }

        /* Prepare the inputs */
        let input_offset = self
            .0
            .invoke_export("get_inputs_off", &[], &mut NopExternals)
            .map_err(|e| format!("Error getting the input offset: {}", e.to_string()))?
            .ok_or("`get_inputs_off` did not return any value")?
            .try_into::<i32>()
            .ok_or("`get_inputs_off` returned the wrong type")?;

        let mem = self
            .0
            .as_ref()
            .export_by_name("memory")
            .ok_or("Module didn't export its memory section")?
            .as_memory()
            .unwrap()
            .clone();

        for (index, input) in inputs.iter().enumerate() {
            // Get the field's bytes and check they correspond to
            // the value that the module expects.
            let mut bv = input.into_byte_vector();
            if bv.len() > field_size {
                return Err(format!(
                    "Input #{} is stored on {} bytes which is greater than the field size of {}",
                    index,
                    bv.len(),
                    field_size
                ));
            } else {
                bv.resize(field_size, 0);
            }

            let addr = (input_offset as u32) + (index as u32) * (field_size as u32);
            mem.set(addr, &bv[..])
                .map_err(|_e| format!("Could not write at memory address {}", addr))?;
        }

        let output_offset = self
            .0
            .as_ref()
            .invoke_export("solve", &[], &mut NopExternals)
            .map_err(|e| format!("Error solving the problem: {}", e.to_string()))?
            .ok_or("`solve` did not return any value")?
            .try_into::<i32>()
            .ok_or("`solve returned the wrong type`")?;

        // NOTE: The question regarding the way that an error code is
        // returned is still open.
        //
        // The current model considers that 2GB is more than enough
        // to store the output data.
        //
        // This being said this approach is tacky and I am considering
        // others at this point:
        //
        //   1. Use a 64 bit return code, values greater than 32-bits
        //      are considered error codes.
        //   2. Export an extra global called `errno` which contains
        //      the error code.
        //   3. 32-bit alignment gives a 2-bit error field
        //   4. Return a pointer to a structure that contains
        //      the error code just before the output data.
        //
        // Experimenting with other languages will help decide what
        // is the better approach.
        if output_offset > 0 {
            let mut outputs = Vec::new();
            let noutputs = get_export::<i32>("min_outputs", self.0.as_ref())?;
            for i in 0..noutputs {
                let index = i as u32;
                let fs = field_size as u32;
                let value = mem
                    .get(output_offset as u32 + fs * index, field_size)
                    .map_err(|e| format!("Could not retrieve the output offset: {}", e))?;

                outputs.push(T::from_byte_vector(value));
            }

            Ok(outputs)
        } else {
            Err(format!("`solve` returned error code {}", output_offset))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use parity_wasm::builder::*;
    use parity_wasm::elements::{Instruction, Instructions, ValueType};
    use std::panic;
    use zokrates_field::field::FieldPrime;

    fn remove_export(code: &str, symbol: &str) -> Vec<u8> {
        let code = FromHex::from_hex(code).unwrap();
        let mut idmod: parity_wasm::elements::Module = parity_wasm::deserialize_buffer(&code[..])
            .expect("Could not deserialize Identity module");
        idmod
            .export_section_mut()
            .expect("Could not get export section")
            .entries_mut()
            .retain(|ref export| export.field() != symbol);
        parity_wasm::serialize(idmod).expect("Could not serialize buffer")
    }

    fn replace_function(
        code: &str,
        symbol: &str,
        params: Vec<ValueType>,
        ret: Option<ValueType>,
        instr: Vec<Instruction>,
    ) -> Vec<u8> {
        /* Deserialize to parity_wasm format */
        let code = FromHex::from_hex(code).unwrap();
        let mut pwmod: parity_wasm::elements::Module = parity_wasm::deserialize_buffer(&code[..])
            .expect("Could not deserialize Identity module");

        /* Remove export, if it exists */
        pwmod
            .export_section_mut()
            .expect("Could not get export section")
            .entries_mut()
            .retain(|ref export| export.field() != symbol);

        /* Add a new function and give it the export name */
        let wmod: parity_wasm::elements::Module = from_module(pwmod)
            .function()
            .signature()
            .with_params(params)
            .with_return_type(ret)
            .build()
            .body()
            .with_instructions(Instructions::new(instr))
            .build()
            .build()
            .export()
            .field(symbol)
            .internal()
            .func(2)
            .build()
            .build();
        parity_wasm::serialize(wmod).expect("Could not serialize buffer")
    }

    fn replace_global(code: &str, symbol: &str, value: i32) -> Vec<u8> {
        /* Deserialize to parity_wasm format */
        let code = FromHex::from_hex(code).unwrap();
        let mut pwmod: parity_wasm::elements::Module = parity_wasm::deserialize_buffer(&code[..])
            .expect("Could not deserialize Identity module");

        /* Remove export, if it exists */
        pwmod
            .export_section_mut()
            .expect("Could not get export section")
            .entries_mut()
            .retain(|ref export| export.field() != symbol);

        /* Add a new function and give it the export name */
        let wmod: parity_wasm::elements::Module = from_module(pwmod)
            .global()
            .value_type()
            .i32()
            .init_expr(Instruction::I32Const(value))
            .build()
            .export()
            .field(symbol)
            .internal()
            .global(4)
            .build()
            .build();
        parity_wasm::serialize(wmod).expect("Could not serialize buffer")
    }

    fn replace_global_type(code: &str, symbol: &str) -> Vec<u8> {
        /* Deserialize to parity_wasm format */
        let code = FromHex::from_hex(code).unwrap();
        let mut pwmod: parity_wasm::elements::Module = parity_wasm::deserialize_buffer(&code[..])
            .expect("Could not deserialize Identity module");

        /* Remove export, if it exists */
        pwmod
            .export_section_mut()
            .expect("Could not get export section")
            .entries_mut()
            .retain(|ref export| export.field() != symbol);

        /* Add a new function and give it the export name */
        let wmod: parity_wasm::elements::Module = from_module(pwmod)
            .global()
            .value_type()
            .f32()
            .init_expr(Instruction::F32Const(0))
            .build()
            .export()
            .field(symbol)
            .internal()
            .global(4)
            .build()
            .build();
        parity_wasm::serialize(wmod).expect("Could not serialize buffer")
    }

    #[test]
    fn check_signatures() {
        let h1 = WasmHelper::from_hex(WasmHelper::IDENTITY_WASM);
        assert_eq!(h1.get_signature(), (1, 1));
    }

    #[test]
    #[should_panic(
        expected = "invalid bytecode: invalid bytecode: Invalid character 'i' at position 0"
    )]
    fn check_invalid_bytecode_fails() {
        WasmHelper::from_hex("invalid bytecode");
    }

    #[test]
    #[should_panic(expected = "Error decoding buffer: Validation(\"I/O Error: UnexpectedEof\")")]
    fn check_truncated_bytecode_fails() {
        WasmHelper::from_hex(&WasmHelper::IDENTITY_WASM[..20]);
    }

    #[test]
    fn validate_exports() {
        /* Test identity without the `solve` export */
        let id = WasmHelper::from(remove_export(WasmHelper::IDENTITY_WASM, "solve"));
        let input = vec![FieldPrime::from(1)];
        let outputs = id.execute(&input);
        assert_eq!(
            outputs,
            Err(String::from(
                "Error solving the problem: Function: Module doesn\'t have export solve",
            ))
        );

        /* Test identity, without the `get_inputs_off` export */
        let id = WasmHelper::from(remove_export(WasmHelper::IDENTITY_WASM, "get_inputs_off"));
        let input = vec![FieldPrime::from(1)];
        let outputs = id.execute(&input);
        assert_eq!(
            outputs,
            Err(String::from(
                "Error getting the input offset: Function: Module doesn\'t have export get_inputs_off",
            ))
        );

        /* Test identity, without the `min_inputs` export */
        let id = WasmHelper::from(remove_export(WasmHelper::IDENTITY_WASM, "min_inputs"));
        let input = vec![FieldPrime::from(1)];
        let outputs = id.execute(&input);
        assert_eq!(
            outputs,
            Err(String::from(
                "Could not find exported symbol `min_inputs` in module",
            ))
        );

        /* Test identity, without the `min_outputs` export */
        let id = WasmHelper::from(remove_export(WasmHelper::IDENTITY_WASM, "min_outputs"));
        let input = vec![FieldPrime::from(1)];
        let outputs = id.execute(&input);
        assert_eq!(
            outputs,
            Err(String::from(
                "Could not find exported symbol `min_outputs` in module",
            ))
        );

        /* Test identity, without the `field_size` export */
        let id = WasmHelper::from(remove_export(WasmHelper::IDENTITY_WASM, "field_size"));
        let input = vec![FieldPrime::from(1)];
        let outputs = id.execute(&input);
        assert_eq!(
            outputs,
            Err(String::from(
                "Could not find exported symbol `field_size` in module",
            ))
        );

        /* Test identity, without the `memory` export */
        let id = WasmHelper::from(remove_export(WasmHelper::IDENTITY_WASM, "memory"));
        let input = vec![FieldPrime::from(1)];
        let outputs = id.execute(&input);
        assert_eq!(
            outputs,
            Err(String::from("Module didn\'t export its memory section"))
        );
    }

    #[test]
    fn check_invalid_function_type() {
        /* Test identity, with a different function return type */
        let id = WasmHelper::from(replace_function(
            WasmHelper::IDENTITY_WASM,
            "get_inputs_off",
            Vec::new(),
            Some(ValueType::I64),
            vec![Instruction::I64Const(0), Instruction::End],
        ));
        let input = vec![FieldPrime::from(1)];
        let outputs = id.execute(&input);
        assert_eq!(
            outputs,
            Err(String::from("`get_inputs_off` returned the wrong type"))
        );

        /* Test identity, with no return type for function */
        let id = WasmHelper::from(replace_function(
            WasmHelper::IDENTITY_WASM,
            "get_inputs_off",
            Vec::new(),
            None,
            vec![Instruction::Nop, Instruction::End],
        ));
        let input = vec![FieldPrime::from(1)];
        let outputs = id.execute(&input);
        assert_eq!(
            outputs,
            Err(String::from("`get_inputs_off` did not return any value"))
        );

        /* Test identity, with extra parameter for function */
        let id = WasmHelper::from(replace_function(
            WasmHelper::IDENTITY_WASM,
            "get_inputs_off",
            vec![ValueType::I64],
            Some(ValueType::I32),
            vec![Instruction::I32Const(0), Instruction::End],
        ));
        let input = vec![FieldPrime::from(1)];
        let outputs = id.execute(&input);
        assert_eq!(
            outputs,
            Err(String::from(
                "Error getting the input offset: Trap: Trap { kind: UnexpectedSignature }",
            ))
        );
    }

    #[test]
    fn check_invalid_field_size() {
        /* Test identity, with 1-byte filed size */
        let id = WasmHelper::from(replace_global(WasmHelper::IDENTITY_WASM, "field_size", 1));
        let input = vec![FieldPrime::from(65536)];
        let outputs = id.execute(&input);
        assert_eq!(
            outputs,
            Err(String::from(
                "Input #0 is stored on 3 bytes which is greater than the field size of 1",
            ))
        );

        /* Test identity, tweaked so that field_size is a f32 */
        let id = WasmHelper::from(replace_global_type(WasmHelper::IDENTITY_WASM, "field_size"));
        let input = vec![FieldPrime::from(65536)];
        let outputs = id.execute(&input);
        assert_eq!(
            outputs,
            Err(String::from("Error converting `field_size` to i32"))
        );
    }

    #[test]
    fn check_identity() {
        let id = WasmHelper::from_hex(WasmHelper::IDENTITY_WASM);
        let input = vec![FieldPrime::from(1)];
        let outputs = id.execute(&input).expect("Identity call failed");
        assert_eq!(outputs, input);

        let id = WasmHelper::from_hex(WasmHelper::IDENTITY_WASM);
        let input = vec![FieldPrime::from(0)];
        let outputs = id.execute(&input).expect("Identity call failed");
        assert_eq!(outputs, input);
    }

    #[test]
    fn check_identity_3_bytes() {
        let id = WasmHelper::from_hex(WasmHelper::IDENTITY_WASM);
        let input = vec![FieldPrime::from(16777216)];
        let outputs = id.execute(&input).expect("Identity call failed");
        assert_eq!(outputs, input);
    }

    #[test]
    fn check_invalid_arg_number() {
        let id = WasmHelper::from_hex(WasmHelper::IDENTITY_WASM);
        let input = vec![FieldPrime::from(1)];
        let outputs = id.execute(&input).expect("Identity call failed");
        assert_eq!(outputs, input);
    }

    #[test]
    fn check_memory_boundaries() {
        // Check that input writes are boundary-checked: same as identity, but
        // get_inputs_off returns an OOB offset.
        let id = WasmHelper::from(replace_function(
            WasmHelper::IDENTITY_WASM,
            "get_inputs_off",
            Vec::new(),
            Some(ValueType::I32),
            vec![Instruction::I32Const(65536), Instruction::End],
        ));
        let input = vec![FieldPrime::from(65536)];
        let outputs = id.execute(&input);
        assert_eq!(
            outputs,
            Err(String::from("Could not write at memory address 65536"))
        );

        /* Check that output writes are boundary-checked */
        // Check that input writes are boundary-checked: same as identity, but
        // solve returns an OOB offset.
        let id = WasmHelper::from(replace_function(
            WasmHelper::IDENTITY_WASM,
            "solve",
            Vec::new(),
            Some(ValueType::I32),
            vec![Instruction::I32Const(65536), Instruction::End],
        ));
        let input = vec![FieldPrime::from(65536)];
        let outputs = id.execute(&input);
        assert_eq!(
            outputs,
            Err(String::from(
                "Could not retrieve the output offset: Memory: trying to access region [65536..65568] in memory [0..64]",
            ))
        );
    }

    #[test]
    fn check_negative_output_value() {
        /* Same as identity, but `solve` returns -1 */
        let id = WasmHelper::from(replace_function(
            WasmHelper::IDENTITY_WASM,
            "solve",
            Vec::new(),
            Some(ValueType::I32),
            vec![Instruction::I32Const(-1), Instruction::End],
        ));
        let input = vec![FieldPrime::from(1)];
        let outputs = id.execute(&input);
        assert_eq!(outputs, Err(String::from("`solve` returned error code -1")));
    }

    #[test]
    fn check_bits() {
        let bits = WasmHelper::from(WasmHelper::BITS_WASM);
        let input = vec![FieldPrime::from(0xdeadbeef as u32)];
        let outputs = bits.execute(&input).unwrap();

        assert_eq!(254, outputs.len());

        for i in 0..32 {
            let bitval = (0xdeadbeef as i64 >> i) & 1;
            assert_eq!(outputs[(253 - i) as usize], FieldPrime::from(bitval as i32));
        }

        for i in 32..254 {
            assert_eq!(outputs[(253 - i) as usize], FieldPrime::from(0));
        }
    }
}
