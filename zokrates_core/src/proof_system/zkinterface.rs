extern crate core;
extern crate libc;

use ir::{self, Statement};
use std::collections::HashMap;
use flat_absy::flat_variable::FlatVariable;
use proof_system::ProofSystem;
use std::fs::File;
use std::io::{BufReader, Write};
use zkinterface::{
    flatbuffers::{FlatBufferBuilder, WIPOffset},
    writing::{CircuitOwned, VariablesOwned},
    zkinterface_generated::zkinterface::{
        BilinearConstraint,
        BilinearConstraintArgs,
        Message,
        R1CSConstraints,
        R1CSConstraintsArgs,
        Root,
        RootArgs,
        Variables,
        VariablesArgs,
        Witness,
        WitnessArgs,
    },
};

use zokrates_field::field::{Field, FieldPrime};

pub struct ZkInterface {}

impl ZkInterface {
    pub fn new() -> ZkInterface {
        ZkInterface {}
    }
}

impl ProofSystem for ZkInterface {
    fn setup(&self, program: ir::Prog<FieldPrime>, pk_path: &str, vk_path: &str) {
        // transform to R1CS
        let (variables, first_local_id, a, b, c) = r1cs_program(program);
        let free_variable_id = variables.len() as u64;
        // Write R1CSConstraints message.
        write_r1cs(&a, &b, &c, pk_path);

        // Write Return message including free_variable_id.
        write_ciruit(
            first_local_id as u64,
            free_variable_id,
            None,
            true,
            &format!("circuit_{}", pk_path));
    }

    fn generate_proof(
        &self,
        program: ir::Prog<FieldPrime>,
        witness: ir::Witness<FieldPrime>,
        pk_path: &str,
        proof_path: &str,
    ) -> bool {
        let (
            public_inputs_arr,
            private_inputs_arr,
        ) = prepare_generate_proof(program, witness);

        let first_local_id = public_inputs_arr.len() as u64;
        let free_variable_id = first_local_id + private_inputs_arr.len() as u64;

//        println!("{:?}", program);

        // Write assignment to local variables.
        write_assignment(first_local_id as u64, &private_inputs_arr, proof_path);

        // Write Return message including output values.
        write_ciruit(
            first_local_id,
            free_variable_id,
            Some(&public_inputs_arr),
            false,
            &format!("circuit_{}", proof_path));

        true
    }

    fn export_solidity_verifier(&self, _reader: BufReader<File>) -> String {
        format!(
            "func export_solidity_verifier is not implemented",
        );

        return String::from("func export_solidity_verifier is not implemented");
    }
}


fn write_r1cs(
    a: &Vec<Vec<(usize, FieldPrime)>>,
    b: &Vec<Vec<(usize, FieldPrime)>>,
    c: &Vec<Vec<(usize, FieldPrime)>>,
    to_path: &str,
) {
    let mut builder = FlatBufferBuilder::new();

    // create vector of
    let mut vector_lc = vec![];

    for i in 0..a.len() {
        let a_var_val = convert_linear_combination(&mut builder, &a[i]);
        let b_var_val = convert_linear_combination(&mut builder, &b[i]);
        let c_var_val = convert_linear_combination(&mut builder, &c[i]);

        let lc = BilinearConstraint::create(&mut builder, &BilinearConstraintArgs {
            linear_combination_a: Some(a_var_val),
            linear_combination_b: Some(b_var_val),
            linear_combination_c: Some(c_var_val),
        });
        vector_lc.push(lc);
    }

    let vector_offset = builder.create_vector(vector_lc.as_slice());

    let args = R1CSConstraintsArgs { constraints: Some(vector_offset), info: None };

    let r1cs_constraints = R1CSConstraints::create(&mut builder, &args);
    let root_args = RootArgs { message_type: Message::R1CSConstraints, message: Some(r1cs_constraints.as_union_value()) };
    let root = Root::create(&mut builder, &root_args);

    builder.finish_size_prefixed(root, None);

    println!("Writing {}", to_path);
    let mut file = File::create(to_path).unwrap();
    file.write_all(builder.finished_data()).unwrap();
}

fn convert_linear_combination<'a>(builder: &mut FlatBufferBuilder<'a>, item: &Vec<(usize, FieldPrime)>) -> (WIPOffset<Variables<'a>>) {
    let mut variable_ids: Vec<u64> = Vec::new();
    let mut values: Vec<u8> = Vec::new();

    for i in 0..item.len() {
        variable_ids.push(item[i].0 as u64);

        let mut bytes = item[i].1.into_byte_vector();
        values.append(&mut bytes);
    }

    let variable_ids = Some(builder.create_vector(&variable_ids));
    let values = Some(builder.create_vector(&values));
    Variables::create(builder, &VariablesArgs {
        variable_ids,
        values,
        info: None,
    })
}

fn write_assignment(
    first_local_id: u64,
    local_values: &[FieldPrime],
    to_path: &str,
) {
    let mut builder = &mut FlatBufferBuilder::new();

    let mut ids = vec![];
    let mut values = vec![];

    for i in 0..local_values.len() {
        ids.push(first_local_id + i as u64);

        let mut bytes = local_values[i].into_byte_vector();
        values.append(&mut bytes);
    }

    let ids = builder.create_vector(&ids);
    let values = builder.create_vector(&values);
    let values = Variables::create(&mut builder, &VariablesArgs {
        variable_ids: Some(ids),
        values: Some(values),
        info: None,
    });
    let assign = Witness::create(&mut builder, &WitnessArgs {
        assigned_variables: Some(values),
    });
    let message = Root::create(&mut builder, &RootArgs {
        message_type: Message::Witness,
        message: Some(assign.as_union_value()),
    });
    builder.finish_size_prefixed(message, None);

    println!("Writing {}", to_path);
    let mut file = File::create(to_path).unwrap();
    file.write_all(builder.finished_data()).unwrap();
}


fn write_ciruit(
    first_local_id: u64,
    free_variable_id: u64,
    public_inputs: Option<&[FieldPrime]>,
    r1cs_generation: bool,
    to_path: &str,
) {
    // Convert element representations.
    let values = public_inputs.map(|public_inputs| {
        assert_eq!(public_inputs.len() as u64, first_local_id);
        let mut values = vec![];
        for value in public_inputs {
            let mut bytes = value.into_byte_vector();
            values.append(&mut bytes);
        }
        values
    });

    let gadget_return = CircuitOwned {
        connections: VariablesOwned {
            variable_ids: (0..first_local_id).collect(),
            values,
        },
        free_variable_id,
        r1cs_generation,
        field_maximum: None,
    };

    println!("Writing {}", to_path);
    let mut file = File::create(to_path).unwrap();
    gadget_return.write(&mut file).unwrap();
}


pub fn prepare_generate_proof<T: Field>(
    program: ir::Prog<T>,
    witness: ir::Witness<T>,
) -> (Vec<T>, Vec<T>) {
    // recover variable order from the program
    let (variables, public_variables_count, _, _, _) = r1cs_program(program);

    let witness: Vec<T> = variables.iter().map(|x| witness.0[x].clone()).collect();

    // split witness into public and private inputs at offset
    let mut public_inputs: Vec<T> = witness.clone();
    let private_inputs: Vec<T> = public_inputs.split_off(public_variables_count);

    (
        public_inputs,
        private_inputs,
    )
}

pub fn provide_variable_idx(
    variables: &mut HashMap<FlatVariable, usize>,
    var: &FlatVariable,
) -> usize {
    let index = variables.len();
    *variables.entry(*var).or_insert(index)
}

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

    //~out are added after main's arguments as we want variables (columns)
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
        std::mem::replace(&mut variables_list[v], k);
    }
    (variables_list, private_inputs_offset, a, b, c)
}


// tests:
// 1. write_r1cs
// 2. convert_linear_combination
// 3. write_assignment
// 4. write_circuit
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example() {
//            let (_, next_location, alias) =
//                resolve(&Some(String::from("./src")), &String::from("./lib.rs")).unwrap();
//            assert_eq!(next_location, String::from("./src"));
//            assert_eq!(alias, String::from("lib"));
    }
}


