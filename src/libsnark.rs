//
// @file libsnark.rs
// @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de
// @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
// @date 2017

extern crate libc;

use self::libc::c_int;
use self::libc::c_char;
use self::libc::uint8_t;
use std::ffi::{CStr, CString};
use std::cmp::max;

use field::Field;

extern "C" {

    fn _setup(
        A: *const uint8_t,
        B: *const uint8_t,
        C: *const uint8_t,
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
    
    fn _sha256Constraints() -> *const c_char;
}

pub fn setup<T: Field> (
    variables: Vec<String>,
    a: Vec<Vec<(usize, T)>>,
    b: Vec<Vec<(usize, T)>>,
    c: Vec<Vec<(usize, T)>>,
    num_inputs: usize,
    pk_path: &str,
    vk_path: &str,
    ) -> bool {

    let num_constraints = a.len();
    let num_variables = variables.len();

    //initialize matrix entries with 0s.
    let mut a_arr: Vec<[u8; 32]> = vec![[0u8; 32]; num_constraints * num_variables];
    let mut b_arr: Vec<[u8; 32]> = vec![[0u8; 32]; num_constraints * num_variables];
    let mut c_arr: Vec<[u8; 32]> = vec![[0u8; 32]; num_constraints * num_variables];

    for row in 0..num_constraints {
        for &(idx, ref val) in &a[row] {
            a_arr[row * num_variables + idx] = vec_as_u8_32_array(&val.into_byte_vector());
        }
        for &(idx, ref val) in &b[row] {
            b_arr[row * num_variables + idx] = vec_as_u8_32_array(&val.into_byte_vector());
        }
        for &(idx, ref val) in &c[row] {
            c_arr[row * num_variables + idx] = vec_as_u8_32_array(&val.into_byte_vector());
        }
    }

    // convert String slices to 'CString's
    let pk_path_cstring = CString::new(pk_path).unwrap();
    let vk_path_cstring = CString::new(vk_path).unwrap();

    unsafe {
        _setup(
            a_arr[0].as_ptr(),
            b_arr[0].as_ptr(),
            c_arr[0].as_ptr(),
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

pub fn get_sha256_constraints() -> () {
    let c_buf: *const c_char = unsafe { _sha256Constraints() };
    let c_str: &CStr = unsafe { CStr::from_ptr(c_buf) };
    let str_slice: &str = c_str.to_str().unwrap();
    println!("{}", str_slice);
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
    use num::bigint::BigUint;

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

        #[test]
        fn sha_256() { 
            //let out: String = unsafe { _sha256Constraints() };
             //let out: String = unsafe { _sha256Witness() };
            //assert_eq!(0,12);
        }
    }
}
