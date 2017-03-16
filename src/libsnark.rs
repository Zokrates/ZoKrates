//
// @file libsnark.rs
// @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
// @date 2017

extern crate libc;

use self::libc::c_int;
use self::libc::uint8_t;
use field::Field;

#[link(name = "snark")]
#[link(name = "supercop")]
#[link(name = "gmp")]
#[link(name = "gmpxx")]
extern {
    fn _run_libsnark(A: *const uint8_t, B: *const uint8_t, C: *const uint8_t, witness: *const uint8_t, constraints: c_int, variables: c_int) -> bool;
}

// assumes that field elements can be represented with 32 bytes
pub fn run_libsnark<T: Field>(variables: Vec<String>, a: Vec<Vec<(usize, T)>>, b: Vec<Vec<(usize, T)>>, c: Vec<Vec<(usize, T)>>, witness: Vec<T>) -> bool {
    let num_constraints = a.len();
    let num_variables = variables.len();
    // let size_variables = T::get_required_bits;

    //initialize matrix entries with 0s.
    let mut a_arr: Vec<[u8;32]> = vec![[0u8;32]; num_constraints * num_variables];
    let mut b_arr: Vec<[u8;32]> = vec![[0u8;32]; num_constraints * num_variables];
    let mut c_arr: Vec<[u8;32]> = vec![[0u8;32]; num_constraints * num_variables];
    let mut w_arr: Vec<[u8;32]> = vec![[0u8;32]; num_variables];
    //before:
    //let mut c_arr: Vec<i32> = vec![0; num_constraints * num_variables];

    for row in 0..num_constraints {
        for &(idx, ref val) in &a[row] {
            a_arr[row * num_variables + idx] = vec_as_u8_32_array(val.into_byte_vector());
        }
        for &(idx, ref val) in &b[row] {
            b_arr[row * num_variables + idx] = vec_as_u8_32_array(val.into_byte_vector());
        }
        for &(idx, ref val) in &c[row] {
            c_arr[row * num_variables + idx] = vec_as_u8_32_array(val.into_byte_vector());
        }
    }

    //convert witness
    for (index,value) in witness.into_iter().enumerate() {
        w_arr[index] = vec_as_u8_32_array(value.into_byte_vector());
    }

    //debugging output
    println!("debugging output:");
    println!("a_arr {:?}", a_arr);
    println!("b_arr {:?}", b_arr);
    println!("c_arr {:?}", c_arr);
    println!("w_arr {:?}", w_arr);

    unsafe {
        _run_libsnark(a_arr[0].as_ptr(),b_arr[0].as_ptr(), c_arr[0].as_ptr(), w_arr[0].as_ptr(), num_constraints as i32, num_variables as i32)
    }
}

// utility function. Converts a Fields vector-based byte representation to fixed size array.
fn vec_as_u8_32_array(vec: Vec<u8>) -> [u8;32]{
    assert!(vec.len()<=32);
    let mut array = [0u8;32];
    for (index,byte) in vec.into_iter().enumerate() {
        array[31-index] = byte;
    }
    array
}
