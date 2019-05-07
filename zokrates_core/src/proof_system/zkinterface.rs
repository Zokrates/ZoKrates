extern crate core;
extern crate libc;

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
    fn setup(
        &self,
        variables: Vec<FlatVariable>,
        a: Vec<Vec<(usize, FieldPrime)>>,
        b: Vec<Vec<(usize, FieldPrime)>>,
        c: Vec<Vec<(usize, FieldPrime)>>,
        num_public_inputs: usize,
        pk_path: &str,
        _vk_path: &str,
    ) -> bool {
        let first_local_id = 1 + num_public_inputs as u64;
        let free_variable_id = variables.len() as u64;

        // Write R1CSConstraints message.
        write_r1cs(&a, &b, &c, pk_path);

        // Write Return message including free_variable_id.
        write_ciruit(
            first_local_id,
            free_variable_id,
            None,
            true,
            &format!("circuit_{}", pk_path));

        true
    }

    fn generate_proof(
        &self,
        _pk_path: &str,
        proof_path: &str,
        public_inputs: Vec<FieldPrime>,
        local_values: Vec<FieldPrime>,
    ) -> bool {
        let first_local_id = public_inputs.len() as u64;
        let free_variable_id = first_local_id + local_values.len() as u64;

        println!("{:?}", public_inputs);

        // Write assignment to local variables.
        write_assignment(first_local_id as u64, &local_values, proof_path);

        // Write Return message including output values.
        write_ciruit(
            first_local_id,
            free_variable_id,
            Some(&public_inputs),
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
        field_order: None,
    };

    println!("Writing {}", to_path);
    let mut file = File::create(to_path).unwrap();
    gadget_return.write(&mut file).unwrap();
}
