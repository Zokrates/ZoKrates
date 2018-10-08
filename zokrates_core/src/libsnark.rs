//
// @file libsnark.rs
// @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de
// @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
// @date 2017

extern crate libc;

use self::libc::{c_int, c_char, uint8_t};
use std::ffi::{CString};
use std::cmp::max;
use std::string::String;
use flat_absy::flat_variable::FlatVariable;

use field::Field;

extern "C" {

    fn _setup(
        A: *const uint8_t,
        B: *const uint8_t,
        C: *const uint8_t,
        A_len: c_int,
        B_len: c_int,
        C_len: c_int,
        constraints: c_int,
        variables: c_int,
        inputs: c_int,
        pk_path: *const c_char,
        vk_path: *const c_char,
    ) -> bool;

    fn _generate_proof(pk_path: *const c_char,
                public_inputs: *const uint8_t,
                public_inputs_length: c_int,
                private_inputs: *const uint8_t,
                private_inputs_length: c_int,
            ) -> bool;

    fn _sha256Constraints() -> *mut c_char;
    fn _sha256Witness(inputs: *const uint8_t, inputs_length: c_int) -> *mut c_char;
    
    fn _shaEth256Constraints() -> *mut c_char;
    fn _shaEth256Witness(inputs: *const uint8_t, inputs_length: c_int) -> *mut c_char;
}

pub fn setup<T: Field> (
    variables: Vec<FlatVariable>,
    a: Vec<Vec<(usize, T)>>,
    b: Vec<Vec<(usize, T)>>,
    c: Vec<Vec<(usize, T)>>,
    num_inputs: usize,
    pk_path: &str,
    vk_path: &str,
    ) -> bool {

    let num_constraints = a.len();
    let num_variables = variables.len();

    // Create single A,B,C vectors of tuples (constraint_number, variable_id, variable_value)
    let mut a_vec = vec![];
    let mut b_vec = vec![];
    let mut c_vec = vec![];
    for row in 0..num_constraints {
      for &(idx, ref val) in &a[row] {
          a_vec.push((row as i32, idx as i32, vec_as_u8_32_array(&val.into_byte_vector())));
      }
      for &(idx, ref val) in &b[row] {
          b_vec.push((row as i32, idx as i32, vec_as_u8_32_array(&val.into_byte_vector())));
      }
      for &(idx, ref val) in &c[row] {
          c_vec.push((row as i32, idx as i32, vec_as_u8_32_array(&val.into_byte_vector())));
      }
    }

    // Sizes and offsets in bytes for our struct {row, id, value}
    // We're building { i32, i32, i8[32] }
    const STRUCT_SIZE: usize = 40;

    const ROW_SIZE: usize = 4;

    const IDX_SIZE: usize = 4;
    const IDX_OFFSET: usize = 4;

    const VALUE_SIZE: usize = 32;
    const VALUE_OFFSET: usize = 8;

    // Convert above A,B,C vectors to byte arrays for cpp
    let mut a_arr: Vec<u8> = vec![0u8; STRUCT_SIZE * a_vec.len()];
    let mut b_arr: Vec<u8> = vec![0u8; STRUCT_SIZE * b_vec.len()];
    let mut c_arr: Vec<u8> = vec![0u8; STRUCT_SIZE * c_vec.len()];
    use std::mem::transmute;
    for (id, (row, idx, val)) in a_vec.iter().enumerate() {
      let row_bytes: [u8; ROW_SIZE] = unsafe { transmute(row.to_le()) };
      let idx_bytes: [u8; IDX_SIZE] = unsafe { transmute(idx.to_le()) };

      for x in 0..ROW_SIZE {
        a_arr[id * STRUCT_SIZE + x] = row_bytes[x];
      }
      for x in 0..IDX_SIZE {
        a_arr[id * STRUCT_SIZE + x + IDX_OFFSET] = idx_bytes[x];
      }
      for x in 0..VALUE_SIZE {
        a_arr[id * STRUCT_SIZE + x + VALUE_OFFSET] = val[x];
      }
    }
    for (id, (row, idx, val)) in b_vec.iter().enumerate() {
      let row_bytes: [u8; ROW_SIZE] = unsafe { transmute(row.to_le()) };
      let idx_bytes: [u8; IDX_SIZE] = unsafe { transmute(idx.to_le()) };

      for x in 0..ROW_SIZE {
        b_arr[id * STRUCT_SIZE + x] = row_bytes[x];
      }
      for x in 0..IDX_SIZE {
        b_arr[id * STRUCT_SIZE + x + IDX_OFFSET] = idx_bytes[x];
      }
      for x in 0..VALUE_SIZE {
        b_arr[id * STRUCT_SIZE + x + VALUE_OFFSET] = val[x];
      }
    }
    for (id, (row, idx, val)) in c_vec.iter().enumerate() {
      let row_bytes: [u8; ROW_SIZE] = unsafe { transmute(row.to_le()) };
      let idx_bytes: [u8; IDX_SIZE] = unsafe { transmute(idx.to_le()) };

      for x in 0..ROW_SIZE {
        c_arr[id * STRUCT_SIZE + x] = row_bytes[x];
      }
      for x in 0..IDX_SIZE {
        c_arr[id * STRUCT_SIZE + x + IDX_OFFSET] = idx_bytes[x];
      }
      for x in 0..VALUE_SIZE {
        c_arr[id * STRUCT_SIZE + x + VALUE_OFFSET] = val[x];
      }
    }

    // convert String slices to 'CString's
    let pk_path_cstring = CString::new(pk_path).unwrap();
    let vk_path_cstring = CString::new(vk_path).unwrap();

    unsafe {
        _setup(
            a_arr.as_ptr(),
            b_arr.as_ptr(),
            c_arr.as_ptr(),
            a_vec.len() as i32,
            b_vec.len() as i32,
            c_vec.len() as i32,
            num_constraints as i32,
            num_variables as i32,
            num_inputs as i32,
            pk_path_cstring.as_ptr(),
            vk_path_cstring.as_ptr()
        )
    }
}

pub fn generate_proof<T: Field>(
    pk_path: &str,
    public_inputs: Vec<T>,
    private_inputs: Vec<T>,
) -> bool {

    let pk_path_cstring = CString::new(pk_path).unwrap();

    let public_inputs_length = public_inputs.len();
    let private_inputs_length = private_inputs.len();

    let mut public_inputs_arr: Vec<[u8; 32]> = vec![[0u8; 32]; public_inputs_length];
    // length must not be zero here, so we apply the max function
    let mut private_inputs_arr: Vec<[u8; 32]> = vec![[0u8; 32]; max(private_inputs_length,1)];

    //convert inputs
    for (index, value) in public_inputs.into_iter().enumerate() {
        public_inputs_arr[index] = vec_as_u8_32_array(&value.into_byte_vector());
    }
    for (index, value) in private_inputs.into_iter().enumerate() {
        private_inputs_arr[index] = vec_as_u8_32_array(&value.into_byte_vector());
    }

    unsafe {
        _generate_proof(
            pk_path_cstring.as_ptr(),
            public_inputs_arr[0].as_ptr(),
            public_inputs_length as i32,
            private_inputs_arr[0].as_ptr(),
            private_inputs_length as i32
        )
    }
}

pub fn get_sha256_constraints() -> String {
    let a = unsafe { CString::from_raw(_sha256Constraints()) };
    a.into_string().unwrap()
}

pub fn get_sha256_witness<T:Field>(inputs: &Vec<T>) -> String {
    let mut inputs_arr: Vec<[u8; 32]> = vec![[0u8; 32]; inputs.len()];

    for (index, value) in inputs.into_iter().enumerate() {
        inputs_arr[index] = vec_as_u8_32_array(&value.into_byte_vector());
    }

    let a = unsafe { CString::from_raw(_sha256Witness(inputs_arr[0].as_ptr(), inputs.len() as i32)) };
    a.into_string().unwrap()
}

pub fn get_ethsha256_constraints() -> String {
    let a = unsafe { CString::from_raw(_shaEth256Constraints()) };
    a.into_string().unwrap()
}

pub fn get_ethsha256_witness<T:Field>(inputs: &Vec<T>) -> String {
    let mut inputs_arr: Vec<[u8; 32]> = vec![[0u8; 32]; inputs.len()];

    for (index, value) in inputs.into_iter().enumerate() {
        inputs_arr[index] = vec_as_u8_32_array(&value.into_byte_vector());
    }

    let a = unsafe { CString::from_raw(_shaEth256Witness(inputs_arr[0].as_ptr(), inputs.len() as i32)) };
    a.into_string().unwrap()
}


// utility function. Converts a Fields vector-based byte representation to fixed size array.
fn vec_as_u8_32_array(vec: &Vec<u8>) -> [u8; 32] {
    assert!(vec.len() <= 32);
    let mut array = [0u8; 32];
    for (index, byte) in vec.iter().enumerate() {
        array[31 - index] = *byte;
    }
    array
}

#[cfg(test)]
mod tests {
    use super::*;
    use field::FieldPrime;
    use num_bigint::BigUint;
    use serde_json;
    use flat_absy::*;
    use standard;

    #[cfg(test)]
    mod sha256_gadget {
        use super::*;

        #[test]
        fn can_get_sha256_constraints() {
            let _a = get_sha256_constraints();
        }

        #[test]
        fn can_generate_sha_256_witness_null() {
            let inputs = vec![FieldPrime::from(0); 512];
            let _b = get_sha256_witness(&inputs);
        }

        #[test]
        fn can_generate_flattened_code() {
            let constraints = get_sha256_constraints();
            let r1cs: standard::R1CS = serde_json::from_str(&constraints).unwrap();
            let _prog: FlatProg<FieldPrime> = FlatProg::from(standard::DirectiveR1CS{r1cs, directive: None});
        }
    }

    #[cfg(test)]
    mod libsnark_integration {
        use super::*;

        #[test]
        fn serialization_dec() {
            assert_eq!(
                BigUint::parse_bytes(
                    b"5472060717959818805561601436314318772174077789324455915672259473661306552146",
                    10
                ).unwrap()
                    .to_bytes_le(),
                FieldPrime::from(
                    "5472060717959818805561601436314318772174077789324455915672259473661306552146"
                ).into_byte_vector()
            );
        }

        #[test]
        fn serialization_bin() {
            assert_eq!(
                BigUint::parse_bytes(b"110000011001000100111001110010111000010011000110100000001010011011100001010000010001011011011010000001100000010101100001011101100101111000000101101010100100010110100001110001110010101000110100111100001000001000110000010110110110000111110011111101010010",2).unwrap().to_bytes_le(),
                FieldPrime::from("5472060717959818805561601436314318772174077789324455915672259473661306552146").into_byte_vector()
            );
        }

        #[test]
        fn vec_to_array() {
            let byte_vector: Vec<u8> = FieldPrime::from(
                "5472060717959818805561601436314318772174077789324455915672259473661306552146",
            ).into_byte_vector();
            let array: [u8; 32] = vec_as_u8_32_array(&byte_vector);
            for (index, value) in byte_vector.iter().enumerate() {
                assert_eq!(*value, array[31 - index]);
            }
        }
    }
}
