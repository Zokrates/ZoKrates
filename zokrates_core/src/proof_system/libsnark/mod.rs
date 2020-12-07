mod ffi;
pub mod gm17;
pub mod pghr13;

use crate::flat_absy::FlatVariable;
use crate::ir::{self, Statement};
use std::cmp::max;
use std::collections::HashMap;
use zokrates_field::Field;

pub struct Libsnark;

// utility function. Converts a Field's vector-based byte representation to fixed size array.
fn vec_as_u8_32_array(vec: &Vec<u8>) -> [u8; 32] {
    assert!(vec.len() <= 32);
    let mut array = [0u8; 32];
    for (index, byte) in vec.iter().enumerate() {
        array[31 - index] = *byte;
    }
    array
}

pub fn prepare_public_inputs<T: Field>(public_inputs: Vec<T>) -> (Vec<[u8; 32]>, usize) {
    let public_inputs_length = public_inputs.len();
    let mut public_inputs_arr: Vec<[u8; 32]> = vec![[0u8; 32]; public_inputs_length];

    for (index, value) in public_inputs.into_iter().enumerate() {
        public_inputs_arr[index] = vec_as_u8_32_array(&value.into_byte_vector());
    }

    (public_inputs_arr, public_inputs_length)
}

// proof-system-independent preparation for the setup phase
pub fn prepare_setup<T: Field>(
    program: ir::Prog<T>,
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
) {
    // transform to R1CS
    let (variables, public_variables_count, a, b, c) = r1cs_program(program);

    let num_inputs = public_variables_count - 1;

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
    )
}

// proof-system-independent preparation for proof generation
pub fn prepare_generate_proof<T: Field>(
    program: ir::Prog<T>,
    witness: ir::Witness<T>,
) -> (Vec<[u8; 32]>, usize, Vec<[u8; 32]>, usize) {
    // recover variable order from the program
    let (variables, public_variables_count, _, _, _) = r1cs_program(program);

    let witness: Vec<_> = variables.iter().map(|x| witness.0[x].clone()).collect();

    // split witness into public and private inputs at offset
    let mut public_inputs: Vec<_> = witness.clone();
    let private_inputs: Vec<_> = public_inputs.split_off(public_variables_count);

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
        public_inputs_arr,
        public_inputs_length,
        private_inputs_arr,
        private_inputs_length,
    )
}

/// Returns the index of `var` in `variables`, adding `var` with incremented index if it does not yet exists.
///
/// # Arguments
///
/// * `variables` - A mutual map that maps all existing variables to their index.
/// * `var` - Variable to be searched for.
pub fn provide_variable_idx(
    variables: &mut HashMap<FlatVariable, usize>,
    var: &FlatVariable,
) -> usize {
    let index = variables.len();
    *variables.entry(*var).or_insert(index)
}

/// Calculates one R1CS row representation of a program and returns (V, A, B, C) so that:
/// * `V` contains all used variables and the index in the vector represents the used number in `A`, `B`, `C`
/// * `<A,x>*<B,x> = <C,x>` for a witness `x`
///
/// # Arguments
///
/// * `prog` - The program the representation is calculated for.
pub fn r1cs_program<T: Field>(
    prog: ir::Prog<T>,
) -> (
    Vec<FlatVariable>,
    usize,
    Vec<Vec<(usize, T)>>,
    Vec<Vec<(usize, T)>>,
    Vec<Vec<(usize, T)>>,
) {
    let mut variables: HashMap<FlatVariable, usize> = HashMap::new();
    provide_variable_idx(&mut variables, &FlatVariable::one());

    for x in prog
        .main
        .arguments
        .iter()
        .enumerate()
        .filter(|(index, _)| !prog.private[*index])
    {
        provide_variable_idx(&mut variables, &x.1);
    }

    //Only the main function is relevant in this step, since all calls to other functions were resolved during flattening
    let main = prog.main;

    //~out are added after main's arguments, since we want variables (columns)
    //in the r1cs to be aligned like "public inputs | private inputs"
    let main_return_count = main.returns.len();

    for i in 0..main_return_count {
        provide_variable_idx(&mut variables, &FlatVariable::public(i));
    }

    // position where private part of witness starts
    let private_inputs_offset = variables.len();

    // first pass through statements to populate `variables`
    for (quad, lin) in main.statements.iter().filter_map(|s| match s {
        Statement::Constraint(quad, lin) => Some((quad, lin)),
        Statement::Directive(..) => None,
    }) {
        for (k, _) in &quad.left.0 {
            provide_variable_idx(&mut variables, &k);
        }
        for (k, _) in &quad.right.0 {
            provide_variable_idx(&mut variables, &k);
        }
        for (k, _) in &lin.0 {
            provide_variable_idx(&mut variables, &k);
        }
    }

    let mut a = vec![];
    let mut b = vec![];
    let mut c = vec![];

    // second pass to convert program to raw sparse vectors
    for (quad, lin) in main.statements.into_iter().filter_map(|s| match s {
        Statement::Constraint(quad, lin) => Some((quad, lin)),
        Statement::Directive(..) => None,
    }) {
        a.push(
            quad.left
                .0
                .into_iter()
                .map(|(k, v)| (variables.get(&k).unwrap().clone(), v))
                .collect(),
        );
        b.push(
            quad.right
                .0
                .into_iter()
                .map(|(k, v)| (variables.get(&k).unwrap().clone(), v))
                .collect(),
        );
        c.push(
            lin.0
                .into_iter()
                .map(|(k, v)| (variables.get(&k).unwrap().clone(), v))
                .collect(),
        );
    }

    // Convert map back into list ordered by index
    let mut variables_list = vec![FlatVariable::new(0); variables.len()];
    for (k, v) in variables.drain() {
        assert_eq!(variables_list[v], FlatVariable::new(0));
        variables_list[v] = k;
    }
    (variables_list, private_inputs_offset, a, b, c)
}

pub mod serialization {
    use crate::proof_system::{G1Affine, G2Affine};
    use std::io::Read;
    use std::io::Write;

    #[inline]
    fn decode_hex(value: &String) -> Vec<u8> {
        hex::decode(value.strip_prefix("0x").unwrap()).unwrap()
    }

    #[inline]
    fn encode_hex<T: AsRef<[u8]>>(data: T) -> String {
        format!("0x{}", hex::encode(data))
    }

    pub fn read_g1<R: Read>(reader: &mut R) -> Result<G1Affine, ()> {
        let mut buffer = [0; 64];
        reader.read_exact(&mut buffer).map_err(|_| ())?;

        Ok(G1Affine(
            encode_hex(&buffer[0..32].to_vec()),
            encode_hex(&buffer[32..64].to_vec()),
        ))
    }

    pub fn read_g2<R: Read>(reader: &mut R) -> Result<G2Affine, ()> {
        let mut buffer = [0; 128];
        reader.read_exact(&mut buffer).map_err(|_| ())?;

        Ok(G2Affine(
            (
                encode_hex(&buffer[0..32].to_vec()),
                encode_hex(&buffer[32..64].to_vec()),
            ),
            (
                encode_hex(&buffer[64..96].to_vec()),
                encode_hex(&buffer[96..128].to_vec()),
            ),
        ))
    }

    pub fn write_g1<W: Write>(writer: &mut W, g1: &G1Affine) {
        writer.write(decode_hex(&g1.0).as_ref()).unwrap();
        writer.write(decode_hex(&g1.1).as_ref()).unwrap();
    }

    pub fn write_g2<W: Write>(writer: &mut W, g2: &G2Affine) {
        writer.write(decode_hex(&(g2.0).0).as_ref()).unwrap();
        writer.write(decode_hex(&(g2.0).1).as_ref()).unwrap();
        writer.write(decode_hex(&(g2.1).0).as_ref()).unwrap();
        writer.write(decode_hex(&(g2.1).1).as_ref()).unwrap();
    }
}
