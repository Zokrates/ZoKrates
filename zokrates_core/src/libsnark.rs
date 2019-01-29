//
// @file libsnark.rs
// @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de
// @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
// @date 2017

extern crate libc;

use self::libc::{c_char, c_int, uint8_t};
use std::ffi::CString;
use std::string::String;

use zokrates_field::field::Field;

extern "C" {
    fn _sha256Constraints() -> *mut c_char;
    fn _sha256Witness(inputs: *const uint8_t, inputs_length: c_int) -> *mut c_char;

    fn _shaEth256Constraints() -> *mut c_char;
    fn _shaEth256Witness(inputs: *const uint8_t, inputs_length: c_int) -> *mut c_char;
}

pub fn get_sha256_constraints() -> String {
    let a = unsafe { CString::from_raw(_sha256Constraints()) };
    a.into_string().unwrap()
}

pub fn get_sha256_witness<T: Field>(inputs: &Vec<T>) -> String {
    let mut inputs_arr: Vec<[u8; 32]> = vec![[0u8; 32]; inputs.len()];

    for (index, value) in inputs.into_iter().enumerate() {
        inputs_arr[index] = vec_as_u8_32_array(&value.into_byte_vector());
    }

    let a =
        unsafe { CString::from_raw(_sha256Witness(inputs_arr[0].as_ptr(), inputs.len() as i32)) };
    a.into_string().unwrap()
}

pub fn get_ethsha256_constraints() -> String {
    let a = unsafe { CString::from_raw(_shaEth256Constraints()) };
    a.into_string().unwrap()
}

pub fn get_ethsha256_witness<T: Field>(inputs: &Vec<T>) -> String {
    let mut inputs_arr: Vec<[u8; 32]> = vec![[0u8; 32]; inputs.len()];

    for (index, value) in inputs.into_iter().enumerate() {
        inputs_arr[index] = vec_as_u8_32_array(&value.into_byte_vector());
    }

    let a = unsafe {
        CString::from_raw(_shaEth256Witness(
            inputs_arr[0].as_ptr(),
            inputs.len() as i32,
        ))
    };
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
    use flat_absy::*;
    use helpers;
    use num_bigint::BigUint;
    use serde_json;
    use standard;
    use zokrates_field::field::FieldPrime;

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
            let _prog: FlatProg<FieldPrime> = FlatProg::from(standard::DirectiveR1CS {
                r1cs,
                directive: helpers::LibsnarkGadgetHelper::Sha256Compress,
            });
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
                )
                .unwrap()
                .to_bytes_le(),
                FieldPrime::try_from_str(
                    "5472060717959818805561601436314318772174077789324455915672259473661306552146"
                )
                .unwrap()
                .into_byte_vector()
            );
        }

        #[test]
        fn serialization_bin() {
            assert_eq!(
                BigUint::parse_bytes(b"110000011001000100111001110010111000010011000110100000001010011011100001010000010001011011011010000001100000010101100001011101100101111000000101101010100100010110100001110001110010101000110100111100001000001000110000010110110110000111110011111101010010",2).unwrap().to_bytes_le(),
                FieldPrime::try_from_str("5472060717959818805561601436314318772174077789324455915672259473661306552146").unwrap().into_byte_vector()
            );
        }

        #[test]
        fn vec_to_array() {
            let byte_vector: Vec<u8> = FieldPrime::try_from_str(
                "5472060717959818805561601436314318772174077789324455915672259473661306552146",
            )
            .unwrap()
            .into_byte_vector();
            let array: [u8; 32] = vec_as_u8_32_array(&byte_vector);
            for (index, value) in byte_vector.iter().enumerate() {
                assert_eq!(*value, array[31 - index]);
            }
        }
    }
}
