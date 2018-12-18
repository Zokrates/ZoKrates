use std::fmt;
use std::fs::File;
use helpers::{Signed, Executable};
use field::Field;

use wasmi::{ModuleInstance, ImportsBuilder, NopExternals, ModuleRef};
use rustc_hex::FromHex;
use std::rc::Rc;
use serde::{Deserialize, Deserializer};

#[derive(Clone, Debug, Serialize)]
pub struct WasmHelper(#[serde(skip)] std::rc::Rc<ModuleRef>, #[serde(serialize_with="serde_bytes::serialize")] Vec<u8>);

impl WasmHelper {
	/* Hand-coded assembly for identity */
	pub const IDENTITY_WASM : &'static str = "0061736d010000000105016000017f030302000005030100010615047f0041010b7f0041010b7f0041200b7f0141000b074b06066d656d6f727902000e6765745f696e707574735f6f6666000105736f6c766500000a6d696e5f696e7075747303000b6d696e5f6f75747075747303010a6669656c645f73697a6503020a2c0225000340412023036a410023036a280200360200230341016a240323032302470d000b41200b040041000b0b4b020041000b20ffffffff000000000000000000000000ffffffff0000000000000000000000000041200b20deadbeef000000000000000000000000deadbeef000000000000000000000000";
	/* Generated from C code, normalized and cleaned up by hand */
	pub const BITS_WASM : &'static str = "0061736d01000000010c026000017f60037f7f7f017f0304030000010405017001010105030100020626067f0141f0c7040b7f0041f0c7040b7f0041f0c7000b7f0041200b7f0041010b7f0041fe010b074b06066d656d6f727902000e6765745f696e707574735f6f6666000005736f6c766500010a6669656c645f73697a6503030a6d696e5f696e7075747303040b6d696e5f6f75747075747303050901000ad5030305004190080b4f01027f41b008210041b008410041c03f10021a4100210103402000410120014107717420014103764190086a2d0000714100473a0000200041206a2100200141016a220141fe01470d000b41b0080bfc0202037f017e02402002450d00200020013a0000200020026a2203417f6a20013a000020024103490d00200020013a0002200020013a00012003417d6a20013a00002003417e6a20013a000020024107490d00200020013a00032003417c6a20013a000020024109490d002000410020006b41037122046a2203200141ff017141818284086c22013602002003200220046b417c7122046a2202417c6a200136020020044109490d002003200136020820032001360204200241786a2001360200200241746a200136020020044119490d00200320013602102003200136020c2003200136021420032001360218200241686a2001360200200241646a20013602002002416c6a2001360200200241706a20013602002004200341047141187222056b22024120490d002001ad22064220862006842106200320056a2101034020012006370300200141086a2006370300200141106a2006370300200141186a2006370300200141206a2101200241606a2202411f4b0d000b0b20000b";

	pub fn from_file<U: Into<String>>(u: U) -> Self {
		use std::io::prelude::*;
		let fname = u.into();
		let mut file = File::open(fname).unwrap();
		let mut buf = Vec::new();
		file.read_to_end(&mut buf).unwrap();
		WasmHelper::from(buf)
	}

	pub fn from_hex<U: Into<String>>(u: U) -> Self {
		let code_hex = u.into();
		let code = FromHex::from_hex(&code_hex[..])
			.expect(format!("invalid bytecode: {}", code_hex).as_str());
		WasmHelper::from(code)
	}
}

impl From<Vec<u8>> for WasmHelper {
	fn from(code: Vec<u8>) -> Self {
		let module = wasmi::Module::from_buffer(code.clone())
			.expect("Error decoding buffer");
		let modinst = ModuleInstance::new(&module, &ImportsBuilder::default())
	        .expect("Failed to instantiate module")
			.assert_no_start();
		WasmHelper(Rc::new(modinst), code)
	}
}

impl<'de> Deserialize<'de> for WasmHelper {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
		let hex : Vec<u8> = serde_bytes::deserialize(deserializer)?;
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

fn get_export<T : wasmi::FromRuntimeValue>(varname: &str, modref : &ModuleRef) -> Result<T, String> {
	let no = modref
		.export_by_name(varname)
		.ok_or(&format!("Could not find exported symbol `{}` in module", varname)[..])?
		.as_global()
		.ok_or(format!("Error getting {} from the list of globals", varname))?
		.get()
		.try_into::<T>()
		.ok_or(format!("Error converting `{}` to i32", varname))?; // XXX i32 -> T ?
	return Ok(no);
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
			return Err(format!("`solve` expected {} inputs, received {}", ninputs, inputs.len()));
		}

		/* Prepare the inputs */
		let input_offset = self.0
			.invoke_export("get_inputs_off", &[], &mut NopExternals)
			.map_err(|e| format!("Error getting the input offset: {}", e.to_string()))?
			.ok_or("`get_inputs_off` did not return any value")?
			.try_into::<i32>()
			.ok_or("`get_inputs_off` returned the wrong type")?;

		let mem = self.0
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
				return Err(format!("Input #{} is stored on {} bytes which is greater than the field size of {}", index, bv.len(), field_size));
			} else {
				bv.resize(field_size, 0);
			}

			let addr = (input_offset as u32)+(index as u32)*(field_size as u32);
			mem.set(addr, &bv[..])
				.map_err(|_e| format!("Could not write at memory address {}", addr))?;
		}

		let output_offset = self.0
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
				let value = mem.get(output_offset as u32 + fs * index, field_size)
					.map_err(|e| format!("Could not retreive the output offset: {}", e))?;

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
	use field::FieldPrime;
	use super::*;

	#[test]
	fn check_signatures() {
		let h1 = WasmHelper::from_hex(WasmHelper::IDENTITY_WASM);
		assert_eq!(h1.get_signature(), (1, 1));
	}

	#[test]
	fn check_signature_bytecode() {
		let result = panic::catch_unwind(|| { 
			let x = WasmHelper::from_hex("invalid bytecode");
			x.get_signature();
		});
		assert!(result.is_err());
	}

	#[test]
	fn check_signature_exports() {
		/* Code is the same as identity, without the `min_inputs` export */
		let result = panic::catch_unwind(|| { 
			let id = WasmHelper::from_hex("0061736d010000000105016000017f030302000005030100010615047f0041010b7f0041010b7f0041200b7f0141000b073e05066d656d6f727902000e6765745f696e707574735f6f6666000105736f6c766500000b6d696e5f6f75747075747303010a6669656c645f73697a6503020a2c0225000340412023036a410023036a280200360200230341016a240323032302470d000b41200b040041000b0b4b020041000b20ffffffff000000000000000000000000ffffffff0000000000000000000000000041200b20deadbeef000000000000000000000000deadbeef000000000000000000000000");
			id.get_signature();
		});
		assert!(result.is_err());
		
		/* Code is the same as identity, without the `min_outputs` export */
		let result = panic::catch_unwind(|| { 
			let id = WasmHelper::from_hex("0061736d010000000105016000017f030302000005030100010615047f0041010b7f0041010b7f0041200b7f0141000b073d05066d656d6f727902000e6765745f696e707574735f6f6666000105736f6c766500000a6d696e5f696e7075747303000a6669656c645f73697a6503020a2c0225000340412023036a410023036a280200360200230341016a240323032302470d000b41200b040041000b0b4b020041000b20ffffffff000000000000000000000000ffffffff0000000000000000000000000041200b20deadbeef000000000000000000000000deadbeef000000000000000000000000");
			id.get_signature();
		});
		assert!(result.is_err());
	}

	#[test]
	fn check_invalid_bytecode_fails() {
		let id = WasmHelper::from_hex("invalid bytecode");
		let input = vec![FieldPrime::from(1)];
		let outputs = id.execute(&input);
		assert_eq!(outputs, Err(String::from("Invalid character \'i\' at position 0")));

		let id = WasmHelper::from_hex(&WasmHelper::IDENTITY_WASM[..20]);
		let input = vec![FieldPrime::from(1)];
		let outputs = id.execute(&input);
		assert_eq!(outputs, Err(String::from("Validation: I/O Error: UnexpectedEof")));
	}

	#[test]
	fn validate_exports() {
		/* Code is the same as identity, without the `solve` export */
		let id = WasmHelper::new_code("0061736d010000000105016000017f030302000005030100010615047f0041010b7f0041010b7f0041200b7f0141000b074305066d656d6f727902000e6765745f696e707574735f6f666600010a6d696e5f696e7075747303000b6d696e5f6f75747075747303010a6669656c645f73697a6503020a2c0225000340412023036a410023036a280200360200230341016a240323032302470d000b41200b040041000b0b4b020041000b20ffffffff000000000000000000000000ffffffff0000000000000000000000000041200b20deadbeef000000000000000000000000deadbeef000000000000000000000000");
		let input = vec![FieldPrime::from(1)];
		let outputs = id.execute(&input);
		assert_eq!(outputs, Err(String::from("Error solving the problem: Function: Module doesn\'t have export solve")));

		/* Code is the same as identity, without the `get_inputs_off` export */
		let id = WasmHelper::from_hex("0061736d010000000105016000017f030302000005030100010615047f0041010b7f0041010b7f0041200b7f0141000b073a05066d656d6f7279020005736f6c766500000a6d696e5f696e7075747303000b6d696e5f6f75747075747303010a6669656c645f73697a6503020a2c0225000340412023036a410023036a280200360200230341016a240323032302470d000b41200b040041000b0b4b020041000b20ffffffff000000000000000000000000ffffffff0000000000000000000000000041200b20deadbeef000000000000000000000000deadbeef000000000000000000000000");
		let input = vec![FieldPrime::from(1)];
		let outputs = id.execute(&input);
		assert_eq!(outputs, Err(String::from("Error getting the input offset: Function: Module doesn\'t have export get_inputs_off")));

		/* Code is the same as identity, without the `min_inputs` export */
		let id = WasmHelper::from_hex("0061736d010000000105016000017f030302000005030100010615047f0041010b7f0041010b7f0041200b7f0141000b073e05066d656d6f727902000e6765745f696e707574735f6f6666000105736f6c766500000b6d696e5f6f75747075747303010a6669656c645f73697a6503020a2c0225000340412023036a410023036a280200360200230341016a240323032302470d000b41200b040041000b0b4b020041000b20ffffffff000000000000000000000000ffffffff0000000000000000000000000041200b20deadbeef000000000000000000000000deadbeef000000000000000000000000");
		let input = vec![FieldPrime::from(1)];
		let outputs = id.execute(&input);
		assert_eq!(outputs, Err(String::from("Could not find exported symbol `min_inputs` in module")));

		/* Code is the same as identity, without the `min_outputs` export */
		let id = WasmHelper::from_hex("0061736d010000000105016000017f030302000005030100010615047f0041010b7f0041010b7f0041200b7f0141000b073d05066d656d6f727902000e6765745f696e707574735f6f6666000105736f6c766500000a6d696e5f696e7075747303000a6669656c645f73697a6503020a2c0225000340412023036a410023036a280200360200230341016a240323032302470d000b41200b040041000b0b4b020041000b20ffffffff000000000000000000000000ffffffff0000000000000000000000000041200b20deadbeef000000000000000000000000deadbeef000000000000000000000000");
		let input = vec![FieldPrime::from(1)];
		let outputs = id.execute(&input);
		assert_eq!(outputs, Err(String::from("Could not find exported symbol `min_outputs` in module")));

		/* Code is the same as identity, without the `field_size` export */
		let id = WasmHelper::from_hex("0061736d010000000105016000017f030302000005030100010615047f0041010b7f0041010b7f0041200b7f0141000b073e05066d656d6f727902000e6765745f696e707574735f6f6666000105736f6c766500000a6d696e5f696e7075747303000b6d696e5f6f75747075747303010a2c0225000340412023036a410023036a280200360200230341016a240323032302470d000b41200b040041000b0b4b020041000b20ffffffff000000000000000000000000ffffffff0000000000000000000000000041200b20deadbeef000000000000000000000000deadbeef000000000000000000000000");
		let input = vec![FieldPrime::from(1)];
		let outputs = id.execute(&input);
		assert_eq!(outputs, Err(String::from("Could not find exported symbol `field_size` in module")));

		/* Code is the same as identity, without the `memory` export */
		let id = WasmHelper::from_hex("0061736d010000000105016000017f030302000005030100010615047f0041010b7f0041010b7f0041200b7f0141000b0742050e6765745f696e707574735f6f6666000105736f6c766500000a6d696e5f696e7075747303000b6d696e5f6f75747075747303010a6669656c645f73697a6503020a2c0225000340412023036a410023036a280200360200230341016a240323032302470d000b41200b040041000b0b4b020041000b20ffffffff000000000000000000000000ffffffff0000000000000000000000000041200b20deadbeef000000000000000000000000deadbeef000000000000000000000000");
		let input = vec![FieldPrime::from(1)];
		let outputs = id.execute(&input);
		assert_eq!(outputs, Err(String::from("Module didn\'t export its memory section")));
	}

	#[test]
	fn check_invalid_function_type() {
		/* Code is the same as indentity, with a different function return type */
		let id = WasmHelper::from_hex("0061736d010000000105016000017e030302000005030100010615047f0041010b7f0041010b7f0041200b7f0141000b074b06066d656d6f727902000e6765745f696e707574735f6f6666000105736f6c766500000a6d696e5f696e7075747303000b6d696e5f6f75747075747303010a6669656c645f73697a6503020a2c0225000340412023036a410023036a280200360200230341016a240323032302470d000b42200b040042000b0b4b020041000b20ffffffff000000000000000000000000ffffffff0000000000000000000000000041200b20deadbeef000000000000000000000000deadbeef000000000000000000000000");
		let input = vec![FieldPrime::from(1)];
		let outputs = id.execute(&input);
		assert_eq!(outputs, Err(String::from("`get_inputs_off` returned the wrong type")));

		/* Code is the same as indentity, with no return type for function */
		let id = WasmHelper::from_hex("0061736d010000000108026000017f600000030302000105030100010615047f0041010b7f0041010b7f0041200b7f0141000b074b06066d656d6f727902000e6765745f696e707574735f6f6666000105736f6c766500000a6d696e5f696e7075747303000b6d696e5f6f75747075747303010a6669656c645f73697a6503020a2b0225000340412023036a410023036a280200360200230341016a240323032302470d000b41200b0300010b0b4b020041000b20ffffffff000000000000000000000000ffffffff0000000000000000000000000041200b20deadbeef000000000000000000000000deadbeef000000000000000000000000");
		let input = vec![FieldPrime::from(1)];
		let outputs = id.execute(&input);
		assert_eq!(outputs, Err(String::from("`get_inputs_off` did not return any value")));

		/* Code is the same as indentity, with extra parameter for function */
		let id = WasmHelper::from_hex("0061736d010000000109026000017f60017f00030302000105030100010615047f0041010b7f0041010b7f0041200b7f0141000b074b06066d656d6f727902000e6765745f696e707574735f6f6666000105736f6c766500000a6d696e5f696e7075747303000b6d696e5f6f75747075747303010a6669656c645f73697a6503020a2b0225000340412023036a410023036a280200360200230341016a240323032302470d000b41200b0300010b0b4b020041000b20ffffffff000000000000000000000000ffffffff0000000000000000000000000041200b20deadbeef000000000000000000000000deadbeef000000000000000000000000");
		let input = vec![FieldPrime::from(1)];
		let outputs = id.execute(&input);
		assert_eq!(outputs, Err(String::from("Error getting the input offset: Function: not enough arguments, given 0 but expected: 1")));
	}

	#[test]
	fn check_invalid_field_size() {
		/* Code is the same as indentity, with 1-byte filed size */
		let id = WasmHelper::from_hex("0061736d010000000105016000017f030302000005030100010615047f0041010b7f0041010b7f0041010b7f0141000b074b06066d656d6f727902000e6765745f696e707574735f6f6666000105736f6c766500000a6d696e5f696e7075747303000b6d696e5f6f75747075747303010a6669656c645f73697a6503020a2c0225000340412023036a410023036a280200360200230341016a240323032302470d000b41200b040041000b0b4b020041000b20ffffffff000000000000000000000000ffffffff0000000000000000000000000041200b20deadbeef000000000000000000000000deadbeef000000000000000000000000");
		let input = vec![FieldPrime::from(65536)];
		let outputs = id.execute(&input);
		assert_eq!(outputs, Err(String::from("Input #0 is stored on 3 bytes which is greater than the field size of 1")));

		/* Code is the same as identity, tweaked so that field_size is a f32 */
		let id = WasmHelper::from_hex("0061736d010000000105016000017f030302000005030100010618047f0041010b7f0041010b7d0043000000000b7f0141000b074b06066d656d6f727902000e6765745f696e707574735f6f6666000105736f6c766500000a6d696e5f696e7075747303000b6d696e5f6f75747075747303010a6669656c645f73697a6503020a2f0228000340412023036a410023036a280200360200230341016a2403430000000023025c0d000b41200b040041000b0b4b020041000b20ffffffff000000000000000000000000ffffffff0000000000000000000000000041200b20deadbeef000000000000000000000000deadbeef000000000000000000000000");
		let input = vec![FieldPrime::from(65536)];
		let outputs = id.execute(&input);
		assert_eq!(outputs, Err(String::from("Error converting `field_size` to i32")));
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
		/* Check that input writes are boundary-checked */
		let id = WasmHelper::from_hex("0061736d010000000105016000017f030302000005030100010615047f0041010b7f0041010b7f0041200b7f0141000b074b06066d656d6f727902000e6765745f696e707574735f6f6666000105736f6c766500000a6d696e5f696e7075747303000b6d696e5f6f75747075747303010a6669656c645f73697a6503020a2e0225000340412023036a410023036a280200360200230341016a240323032302470d000b41200b0600418080040b0b4b020041000b20ffffffff000000000000000000000000ffffffff0000000000000000000000000041200b20deadbeef000000000000000000000000deadbeef000000000000000000000000");
		let input = vec![FieldPrime::from(65536)];
		let outputs = id.execute(&input);
		assert_eq!(outputs, Err(String::from("Could not write at memory address 65536")));

		/* Check that output writes are boundary-checked */
		let id = WasmHelper::from_hex("0061736d010000000105016000017f030302000005030100010615047f0041010b7f0041010b7f0041200b7f0141000b074b06066d656d6f727902000e6765745f696e707574735f6f6666000105736f6c766500000a6d696e5f696e7075747303000b6d696e5f6f75747075747303010a6669656c645f73697a6503020a2e0227000340412023036a410023036a280200360200230341016a240323032302470d000b418080040b040041000b0b4b020041000b20ffffffff000000000000000000000000ffffffff0000000000000000000000000041200b20deadbeef000000000000000000000000deadbeef000000000000000000000000");
		let input = vec![FieldPrime::from(65536)];
		let outputs = id.execute(&input);
		assert_eq!(outputs, Err(String::from("Could not retreive the output offset: Memory: trying to access region [65536..65568] in memory [0..65536]")));
	}

	#[test]
	fn check_negative_output_value() {
		let id = WasmHelper::from_hex("0061736d010000000105016000017f030302000005030100010615047f0041010b7f0041010b7f0041200b7f0141000b074b06066d656d6f727902000e6765745f696e707574735f6f6666000105736f6c766500000a6d696e5f696e7075747303000b6d696e5f6f75747075747303010a6669656c645f73697a6503020a2c0225000340412023036a410023036a280200360200230341016a240323032302470d000b417f0b040041000b0b4b020041000b20ffffffff000000000000000000000000ffffffff0000000000000000000000000041200b20deadbeef000000000000000000000000deadbeef000000000000000000000000");
		let input = vec![FieldPrime::from(1)];
		let outputs = id.execute(&input);
		assert_eq!(outputs, Err(String::from("`solve` returned error code -1")));
	}

	#[test]
	fn check_file_exists() {
		let result = panic::catch_unwind(|| { 
			let noname = WasmHelper::new_file("noname.wasm");
			let input = vec![FieldPrime::from(7 /* Lucky number, maybe it'll work? ;) */)];
			let _outputs = noname.execute(&input).unwrap();
		});
		/* Nope :( */
		assert!(result.is_err());
	}

	#[test]
	fn check_bits() {
		let bits = WasmHelper::from_hex(WasmHelper::BITS_WASM);
		let input = vec![FieldPrime::from(0xdeadbeef as u32)];
		let outputs = bits.execute(&input).unwrap();

		assert_eq!(254, outputs.len());

		for i in 0..32 {
			let bitval = (0xdeadbeef as i64 >> i) & 1;
			assert_eq!(outputs[i as usize], FieldPrime::from(bitval as i32));
		}

		for i in 32..254 {
			assert_eq!(outputs[i as usize], FieldPrime::from(0));
		}
	}
}