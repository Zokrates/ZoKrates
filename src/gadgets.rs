//
// @file gadgets.rs
// @author Aurélien Nicolas <info@nau.re> for QED-it.com
// @date 2018

extern crate libc;
use self::libc::c_char;
use std::ffi::{CStr, CString};
use std::path::{PathBuf};
extern crate libloading as lib;

use std::slice;

use flat_absy::*;
use parameter::*;
use field::{Field, FieldPrime};
use std::cmp::max;
use libsnark::vec_as_u8_32_array;


// Gadget interface

const INIT_GADGETS_SYMBOL: &[u8] = b"zokrates_init_gadgets";

type InitGadgetsFn = extern "C" fn(
    register_gadget: extern fn(ctx: *mut RegisterGadgetContext<FieldPrime>, gadget_name: *const c_char, n_inputs: u64, n_outputs: u64),
    context: *mut RegisterGadgetContext<FieldPrime>,
) -> bool;


const MAKE_WITNESS_SYMBOL: &[u8] = b"zokrates_make_witness";

type MakeWitnessFn = extern "C" fn(
    gadget_name: *const c_char,
    inputs_bytes: *const [u8; 32],
    inputs_size: u64,
    // Callback and its context
    map_variables: extern fn(ctx: *mut AddWitnessContext<FieldPrime>, first_input: u64, first_output: u64, first_local: u64),
    add_witness: extern fn(ctx: *mut AddWitnessContext<FieldPrime>, gadget_index: u64, val: &[u8; 32]),
    context: *mut AddWitnessContext<FieldPrime>,
) -> bool;


const MAKE_CONSTRAINTS_SYMBOL: &[u8] = b"zokrates_make_constraints";

type MakeConstraintsFn = extern "C" fn(
    gadget_name: *const c_char,
    inputs_size: u64,
    // Callback and its context
    map_variables: extern fn(ctx: *mut AddConstraintContext<FieldPrime>, first_input: u64, first_output: u64, first_local: u64),
    add_constraint: extern fn(ctx: *mut AddConstraintContext<FieldPrime>, is_abc: u8, n_constraints: u64, indices: &u64, coeffs: &[u8; 32]),
    context: *mut AddConstraintContext<FieldPrime>,
) -> bool;



fn bytes_to_field<T: Field>(bytes: &[u8; 32]) -> T {
    let mut v = bytes.to_vec();
    v.reverse();
    return T::from_byte_vector(v);
}

fn field_to_bytes<T: Field>(elem: &T) -> [u8; 32] {
    return vec_as_u8_32_array(&elem.into_byte_vector());
}


#[repr(C)]
pub struct IndicesMap {
    pub first_input: u64,
    pub first_output: u64,
    pub first_local: u64,
}

impl IndicesMap {
    fn map_index(&self, gadget_index :u64) -> (/*is_inp_out_local*/ u8, /*var_index*/ u64) {

        if self.first_input <= gadget_index && gadget_index < self.first_output {
            return (0, gadget_index - self.first_input);

        } else if self.first_output <= gadget_index && gadget_index < self.first_local {
            return (1, gadget_index - self.first_output);

        } else {
            return (2, gadget_index); // Does not need to be contiguous
        }
    }

    fn set(&mut self, first_input: u64, first_output: u64, first_local: u64) {
        println!("map_variables {} {} {}", first_input, first_output, first_local);
        assert!(first_input <= first_output && first_output <= first_local);
        self.first_input = first_input;
        self.first_output = first_output;
        self.first_local = first_local;
    }
}


// Call gadget witness generator

#[repr(C)]
pub struct AddWitnessContext<T: Field> {
    indices_map: IndicesMap,

    call_count: i32,
    pub witness: Vec<(/*is_inp_out_local*/ u8, /*var_index*/ u64, /*val*/ T)>,
}


extern "C" fn add_witness<T: Field>(context_ptr: *mut AddWitnessContext<T>, gadget_index: u64, val: &[u8; 32]) {
    let context = unsafe { &mut *context_ptr };
    context.call_count += 1;

    let p: T = bytes_to_field(val);

    // Interpret variable
    let (is_inp_out_local, var_index) = context.indices_map.map_index(gadget_index);

    context.witness.push((is_inp_out_local, var_index, p));

}


pub fn make_witness<T: Field>(plugin_path: &PathBuf, gadget_name: &GadgetName, inputs: &Vec<T>) -> AddWitnessContext<T> {

    // Prepare inputs
    let inputs_len = inputs.len();
    let mut inputs_c: Vec<[u8; 32]> = vec![[0u8; 32]; max(inputs_len, 1)];

    for (index, value) in inputs.into_iter().enumerate() {
        inputs_c[index] = field_to_bytes(value);
    }

    // Prepare outputs to be populated by add_witness()
    let mut context = AddWitnessContext::<T> {
        indices_map: IndicesMap{first_input: 0, first_output: 0, first_local: 0},
        call_count: 0,
        witness: Vec::new(),
    };

    // Receive the indices map
    extern "C" fn map_variables(context_ptr: *mut AddWitnessContext<FieldPrime>, first_input: u64, first_output: u64, first_local: u64) {
        unsafe { &mut *context_ptr }.indices_map.set(first_input, first_output, first_local);
    }

    let lib = lib::Library::new(plugin_path).unwrap();

    unsafe {
        let make_witness_c: lib::Symbol<MakeWitnessFn> = lib.get(MAKE_WITNESS_SYMBOL).unwrap();

        assert!( make_witness_c(
            gadget_name.as_ptr(),
            inputs_c.as_ptr(),
            inputs_len as u64,
            map_variables,
            add_witness::<FieldPrime>,
            &mut context as *mut _ as *mut AddWitnessContext<FieldPrime>,
        ));
    }
    println!("make_witness added {} witness values.", context.call_count);

    return context;
}


// Call gadget R1CS generator

#[repr(C)]
pub struct AddConstraintContext<'a, T: 'a> {

    pub indices_map: IndicesMap,

    /// Number of rows added. Should be a multiple of 3 for A, B, C.
    pub num_rows: u64,

    pub convert_index: &'a mut FnMut(/*is_inp_out_local*/ u8, /*var_index*/ u64) -> usize,

    pub a: &'a mut Vec<Vec<(usize, T)>>,
    pub b: &'a mut Vec<Vec<(usize, T)>>,
    pub c: &'a mut Vec<Vec<(usize, T)>>,
}


extern "C" fn add_constraint<T: Field>(
    context_ptr: *mut AddConstraintContext<T>,
    is_abc: u8,
    n_terms: u64,
    indices_ptr: &u64,
    coeffs_ptr: &[u8; 32]
) {
    // Cast the pointers
    let context: &mut AddConstraintContext<T>;
    let gadget_indices;
    let coeffs;

    unsafe {
        context = &mut *context_ptr;
        gadget_indices = slice::from_raw_parts(indices_ptr, n_terms as usize);
        coeffs = slice::from_raw_parts(coeffs_ptr, n_terms as usize);
    }

    let mut a_row: Vec<(usize, T)> = Vec::new();
    a_row.reserve(n_terms as usize);

    for i in 0..n_terms as usize {
        let gadget_index = gadget_indices[i];

        // Interpret variable
        let (is_inp_out_local, var_index) = context.indices_map.map_index(gadget_index);

        // Convert to Zokrates variable indices
        let zokrates_index = (context.convert_index)(is_inp_out_local, var_index);

        a_row.push((zokrates_index, bytes_to_field(&coeffs[i])));

        //println ! ("constraint term {} {}: {} -> {}", is_abc, i, gadget_index, zokrates_index);
    }

    match is_abc {
        0 => context.a.push(a_row),
        1 => context.b.push(a_row),
        2 => context.c.push(a_row),
        _ => panic!("is_abc must be 0, 1, or 2 for a, b, or c."),
    };

    context.num_rows += 1;

}


pub fn make_constraints<T: Field>(
    plugin_path: &PathBuf,
    gadget_name: &GadgetName,
    inputs_size: u64,
    context: &mut AddConstraintContext<T>,
) {

    // Receive the indices map
    extern "C" fn map_variables(context_ptr: *mut AddConstraintContext<FieldPrime>, first_input: u64, first_output: u64, first_local: u64) {
        unsafe { &mut *context_ptr }.indices_map.set(first_input, first_output, first_local);
    }

    let lib = lib::Library::new(plugin_path).unwrap();

    unsafe {
        let make_constraints_c: lib::Symbol<MakeConstraintsFn> = lib.get(MAKE_CONSTRAINTS_SYMBOL).unwrap();

        assert!( make_constraints_c(
            gadget_name.as_ptr(),
            inputs_size,
            map_variables,
            add_constraint::<FieldPrime>,
            context as *mut _ as *mut AddConstraintContext<FieldPrime>,
        ));
    }

    println!("make_constraints added {} rows.", context.num_rows);
    assert_eq!(context.num_rows % 3, 0);
}


pub type GadgetName = CString;

#[repr(C)]
pub struct RegisterGadgetContext<'a, T: 'a> where T: Field {
    plugin_path: &'a PathBuf,
    compiled_imports: &'a mut Vec<(FlatProg<T>, String)>,
}

extern "C" fn register_gadget<T: Field>(
    ctx: *mut RegisterGadgetContext<T>,
    name_c: *const c_char, n_inputs: u64, n_outputs: u64,
) {

    // Cast C arguments to Rust types

    let context = unsafe { &mut *ctx };

    let c_str = unsafe { CStr::from_ptr(name_c) };
    let gadget_name: String = c_str.to_str().unwrap().to_owned();

    println!("New gadget: {} {} {}", gadget_name, n_inputs, n_outputs);

    // Prepare input variables
    let mut inputs = FlatExpressionList { expressions: Vec::new() };
    let mut arguments = Vec::new();
    for i in 0..n_inputs {
        let input_name = format!("input_{}", i);
        inputs.expressions.push(FlatExpression::Identifier(input_name.clone()));
        arguments.push(Parameter { id: input_name, private: false });
    }

    // Prepare output variables
    let mut outputs = FlatExpressionList { expressions: Vec::new() };
    for i in 0..n_outputs {
        outputs.expressions.push(FlatExpression::Identifier(format!("output_{}", i)));
    }

    let builtin_function = FlatFunction {
        id: "main".to_string(), // The Importer will look for a main function
        arguments,
        statements: vec![
            FlatStatement::Gadget(context.plugin_path.clone(), CString::new(gadget_name.clone()).unwrap(), "local".to_string(), inputs, outputs.clone()),
            FlatStatement::Return(outputs),
        ],
        return_count: n_outputs as usize,
    };

    let builtin_program = FlatProg {
        functions: vec![builtin_function],
    };

    context.compiled_imports.push((builtin_program, gadget_name));
}


pub fn load_gadgets<T: Field>(plugin_path: &PathBuf, compiled_imports: &mut Vec<(FlatProg<T>, String)>) {
    let mut context = RegisterGadgetContext::<T> {
        plugin_path,
        compiled_imports,
    };
    let ctx = &mut context as *mut _ as *mut RegisterGadgetContext<FieldPrime>;

    let lib = lib::Library::new(plugin_path).unwrap();
    unsafe {
        let init_gadgets_c: lib::Symbol<InitGadgetsFn> = lib.get(INIT_GADGETS_SYMBOL).unwrap();
        assert!(init_gadgets_c(register_gadget, ctx));
    }

}
