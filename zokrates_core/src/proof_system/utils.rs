use field::Field;
use flat_absy::flat_variable::FlatVariable;
use std::cmp::max;
use std::ffi::CString;

// utility function. Converts a Fields vector-based byte representation to fixed size array.
fn vec_as_u8_32_array(vec: &Vec<u8>) -> [u8; 32] {
    assert!(vec.len() <= 32);
    let mut array = [0u8; 32];
    for (index, byte) in vec.iter().enumerate() {
        array[31 - index] = *byte;
    }
    array
}

// proof-system-independent preparation for the setup phase
pub fn prepare_setup<T: Field>(
    variables: Vec<FlatVariable>,
    a: Vec<Vec<(usize, T)>>,
    b: Vec<Vec<(usize, T)>>,
    c: Vec<Vec<(usize, T)>>,
    num_inputs: usize,
    pk_path: &str,
    vk_path: &str,
) -> (
    Vec<u8>,
    Vec<u8>,
    Vec<u8>,
    Vec<(i32, i32, [u8; 32])>,
    Vec<(i32, i32, [u8; 32])>,
    Vec<(i32, i32, [u8; 32])>,
    usize,
    usize,
    usize,
    CString,
    CString,
) {
    let num_constraints = a.len();
    let num_variables = variables.len();

    // Create single A,B,C vectors of tuples (constraint_number, variable_id, variable_value)
    let mut a_vec = vec![];
    let mut b_vec = vec![];
    let mut c_vec = vec![];
    for row in 0..num_constraints {
        for &(idx, ref val) in &a[row] {
            a_vec.push((
                row as i32,
                idx as i32,
                vec_as_u8_32_array(&val.into_byte_vector()),
            ));
        }
        for &(idx, ref val) in &b[row] {
            b_vec.push((
                row as i32,
                idx as i32,
                vec_as_u8_32_array(&val.into_byte_vector()),
            ));
        }
        for &(idx, ref val) in &c[row] {
            c_vec.push((
                row as i32,
                idx as i32,
                vec_as_u8_32_array(&val.into_byte_vector()),
            ));
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

    (
        a_arr,
        b_arr,
        c_arr,
        a_vec,
        b_vec,
        c_vec,
        num_constraints,
        num_variables,
        num_inputs,
        pk_path_cstring,
        vk_path_cstring,
    )
}

// proof-system-independent preparation for proof generation
pub fn prepare_generate_proof<T: Field>(
    pk_path: &str,
    proof_path: &str,
    public_inputs: Vec<T>,
    private_inputs: Vec<T>,
) -> (CString, CString, Vec<[u8; 32]>, usize, Vec<[u8; 32]>, usize) {
    let pk_path_cstring = CString::new(pk_path).unwrap();
    let proof_path_cstring = CString::new(proof_path).unwrap();

    let public_inputs_length = public_inputs.len();
    let private_inputs_length = private_inputs.len();

    let mut public_inputs_arr: Vec<[u8; 32]> = vec![[0u8; 32]; public_inputs_length];
    // length must not be zero here, so we apply the max function
    let mut private_inputs_arr: Vec<[u8; 32]> = vec![[0u8; 32]; max(private_inputs_length, 1)];

    //convert inputs
    for (index, value) in public_inputs.into_iter().enumerate() {
        public_inputs_arr[index] = vec_as_u8_32_array(&value.into_byte_vector());
    }
    for (index, value) in private_inputs.into_iter().enumerate() {
        private_inputs_arr[index] = vec_as_u8_32_array(&value.into_byte_vector());
    }

    (
        pk_path_cstring,
        proof_path_cstring,
        public_inputs_arr,
        public_inputs_length,
        private_inputs_arr,
        private_inputs_length,
    )
}
