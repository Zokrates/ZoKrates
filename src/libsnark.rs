/**
 * @file libsnark.rs
 * @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
 * @date 2017
 */

extern crate libc;

use self::libc::c_int;

#[link(name = "snark")]
#[link(name = "supercop")]
#[link(name = "gmp")]
#[link(name = "gmpxx")]
extern {
    fn _run_libsnark(A: *const c_int, B: *const c_int, C: *const c_int, witness: *const c_int, constraints: c_int, variables: c_int) -> bool;
}

pub fn run_libsnark(variables: Vec<String>, a: Vec<Vec<(usize, i32)>>, b: Vec<Vec<(usize, i32)>>, c: Vec<Vec<(usize, i32)>>, witness: Vec<i32>) -> bool {
    let num_constraints = a.len();
    let num_variables = variables.len();
    let mut a_arr: Vec<i32> = vec![0; num_constraints * num_variables];
    let mut b_arr: Vec<i32> = vec![0; num_constraints * num_variables];
    let mut c_arr: Vec<i32> = vec![0; num_constraints * num_variables];
    for row in 0..num_constraints {
        for &(idx, val) in &a[row] {
            a_arr[row * num_variables + idx] = val;
        }
        for &(idx, val) in &b[row] {
            b_arr[row * num_variables + idx] = val;
        }
        for &(idx, val) in &c[row] {
            c_arr[row * num_variables + idx] = val;
        }
    }
    unsafe {
        _run_libsnark(a_arr.as_ptr(), b_arr.as_ptr(), c_arr.as_ptr(), witness.as_ptr(), num_constraints as i32, num_variables as i32)
    }
}
