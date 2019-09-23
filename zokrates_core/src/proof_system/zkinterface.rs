use flat_absy::flat_variable::FlatVariable;
use ir::{self, Statement};
use lazy_static::lazy_static;
use proof_system::ProofSystem;
use std::collections::HashMap;
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

lazy_static! {
    pub static ref FIELD_LENGTH: usize = FieldPrime::max_value().into_byte_vector().len();
}

pub struct ZkInterface {}

impl ZkInterface {
    pub fn new() -> ZkInterface {
        ZkInterface {}
    }
}

impl ProofSystem for ZkInterface {
    fn setup(&self, program: ir::Prog<FieldPrime>, pk_path: &str, _vk_path: &str) {
        let mut out_file = File::create(pk_path).unwrap();
        setup(program, &mut out_file)
    }

    fn generate_proof(
        &self,
        program: ir::Prog<FieldPrime>,
        witness: ir::Witness<FieldPrime>,
        _pk_path: &str,
        proof_path: &str,
    ) -> bool {
        let mut out_file = File::create(proof_path).unwrap();
        generate_proof(program, witness, &mut out_file)
    }

    fn export_solidity_verifier(&self, _reader: BufReader<File>, _is_abiv2: bool) -> String {
        "export_solidity_verifier is not implemented".to_string()
    }
}

pub fn setup<W: Write>(program: ir::Prog<FieldPrime>, out_file: &mut W) {

    // Extract variables from the program
    let (variables_map, first_private_id) = convert_variable_ids(&program);

    let (a, b, c) = r1cs_program(program, &variables_map);

    let free_variable_id = variables_map.len() as u64;

    // Write Circuit message including free_variable_id.
    write_circuit(
        first_private_id,
        free_variable_id,
        None,
        true,
        out_file);

    // Write R1CSConstraints message.
    write_r1cs(&a, &b, &c, out_file);
}

pub fn generate_proof<W: Write>(
    program: ir::Prog<FieldPrime>,
    witness: ir::Witness<FieldPrime>,
    out_file: &mut W,
) -> bool {

    // Extract variables from the program
    let (variables_map, first_private_id) = convert_variable_ids(&program);

    let (
        public_inputs_arr,
        private_inputs_arr,
    ) = convert_variable_values(&variables_map, first_private_id, &witness);

    let first_private_id = public_inputs_arr.len() as u64;
    let free_variable_id = first_private_id + private_inputs_arr.len() as u64;

    // Write Return message including public values.
    write_circuit(
        first_private_id,
        free_variable_id,
        Some(&public_inputs_arr),
        false,
        out_file);

    // Write assignment to local variables.
    write_assignment(
        first_private_id,
        &private_inputs_arr,
        out_file);

    true
}


fn write_r1cs<W: Write>(
    a: &Vec<Vec<(u64, FieldPrime)>>,
    b: &Vec<Vec<(u64, FieldPrime)>>,
    c: &Vec<Vec<(u64, FieldPrime)>>,
    out_file: &mut W,
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

    out_file.write_all(builder.finished_data()).unwrap();
}


fn convert_field(value: &FieldPrime) -> Vec<u8> {
    let mut le_bytes = value.into_byte_vector();
    le_bytes.resize(*FIELD_LENGTH, 0);
    le_bytes
}

fn convert_linear_combination<'a>(builder: &mut FlatBufferBuilder<'a>, item: &Vec<(u64, FieldPrime)>) -> (WIPOffset<Variables<'a>>) {
    let mut variable_ids: Vec<u64> = Vec::new();
    let mut values: Vec<u8> = Vec::new();

    for i in 0..item.len() {
        variable_ids.push(item[i].0);
        values.append(&mut convert_field(&item[i].1));
    }

    let variable_ids = Some(builder.create_vector(&variable_ids));
    let values = Some(builder.create_vector(&values));
    Variables::create(builder, &VariablesArgs {
        variable_ids,
        values,
        info: None,
    })
}

fn write_assignment<W: Write>(
    first_private_id: u64,
    private_values: &[FieldPrime],
    out_file: &mut W,
) {
    let mut builder = &mut FlatBufferBuilder::new();

    let mut ids = vec![];
    let mut values = vec![];

    for i in 0..private_values.len() {
        ids.push(first_private_id + i as u64);
        values.append(&mut convert_field(&private_values[i]));
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

    out_file.write_all(builder.finished_data()).unwrap();
}


fn write_circuit<W: Write>(
    first_private_id: u64,
    free_variable_id: u64,
    public_values: Option<&[FieldPrime]>,
    r1cs_generation: bool,
    out_file: &mut W,
) {
    // Convert element representations.
    let values = public_values.map(|public_inputs| {
        assert_eq!(public_inputs.len() as u64, first_private_id);
        let mut values = vec![];
        for value in public_inputs {
            values.append(&mut convert_field(value));
        }
        values
    });

    let gadget_return = CircuitOwned {
        connections: VariablesOwned {
            variable_ids: (0..first_private_id).collect(),
            values,
        },
        free_variable_id,
        r1cs_generation,
        field_maximum: Some(convert_field(&FieldPrime::max_value())),
    };

    gadget_return.write(out_file).unwrap();
}

fn convert_variable_values<T: Field>(
    variables_map: &HashMap<FlatVariable, u64>,
    first_private_id: u64,
    witness: &ir::Witness<T>,
) -> (Vec<T>, Vec<T>) {
    let num_public = first_private_id as usize;
    let num_private = variables_map.len() - num_public;
    let mut public_values = vec![T::zero(); num_public];
    let mut private_values = vec![T::zero(); num_private];

    for (zok_var, zkif_id) in variables_map.iter() {
        let value = witness.0[zok_var].clone();

        if *zkif_id < first_private_id {
            public_values[*zkif_id as usize] = value;
        } else {
            let index = *zkif_id - first_private_id;
            private_values[index as usize] = value;
        }
    }

    (public_values, private_values)
}

fn provide_variable_idx(
    variables: &mut HashMap<FlatVariable, u64>,
    var: &FlatVariable,
) -> u64 {
    let index = variables.len() as u64;
    *variables.entry(*var).or_insert(index)
}

fn convert_variable_ids<T: Field>(
    prog: &ir::Prog<T>,
) -> (
    HashMap<FlatVariable, u64>,
    u64,
) {
    let mut variables_map: HashMap<FlatVariable, u64> = HashMap::new();

    provide_variable_idx(&mut variables_map, &FlatVariable::one());

    // Map public arguments.
    for x in prog
        .main
        .arguments
        .iter()
        .enumerate()
        .filter(|(index, _)| !prog.private[*index])
        {
            provide_variable_idx(&mut variables_map, &x.1);
        }

    // Map public return variables.
    let main_return_count = prog.main.returns.len();

    for i in 0..main_return_count {
        provide_variable_idx(&mut variables_map, &FlatVariable::public(i));
    }

    // position where private part of witness starts
    let first_private_id = variables_map.len() as u64;

    // Go through the statements to populate `variables_map` with the private variables.
    for (quad, lin) in prog.main.statements.iter().filter_map(|s| match s {
        Statement::Constraint(quad, lin) => Some((quad, lin)),
        Statement::Directive(..) => None,
    }) {
        for (k, _) in &quad.left.0 {
            provide_variable_idx(&mut variables_map, &k);
        }
        for (k, _) in &quad.right.0 {
            provide_variable_idx(&mut variables_map, &k);
        }
        for (k, _) in &lin.0 {
            provide_variable_idx(&mut variables_map, &k);
        }
    }

    (variables_map, first_private_id)
}

fn r1cs_program<T: Field>(
    prog: ir::Prog<T>,
    variables_map: &HashMap<FlatVariable, u64>,
) -> (
    Vec<Vec<(u64, T)>>,
    Vec<Vec<(u64, T)>>,
    Vec<Vec<(u64, T)>>,
) {
    let mut a = vec![];
    let mut b = vec![];
    let mut c = vec![];

    for (quad, lin) in prog.main.statements.into_iter().filter_map(|s| match s {
        Statement::Constraint(quad, lin) => Some((quad, lin)),
        Statement::Directive(..) => None,
    }) {
        a.push(
            quad.left
                .0
                .into_iter()
                .map(|(k, v)| (variables_map.get(&k).unwrap().clone(), v))
                .collect(),
        );
        b.push(
            quad.right
                .0
                .into_iter()
                .map(|(k, v)| (variables_map.get(&k).unwrap().clone(), v))
                .collect(),
        );
        c.push(
            lin.0
                .into_iter()
                .map(|(k, v)| (variables_map.get(&k).unwrap().clone(), v))
                .collect(),
        );
    }

    (a, b, c)
}


#[cfg(test)]
mod tests {
    use crate::compile::compile;
    use crate::imports::Error;
    use super::{convert_field, FIELD_LENGTH, generate_proof, setup};
    use zkinterface::reading::{Constraint, Messages, Term, Variable};
    use zokrates_field::field::{Field, FieldPrime};

    fn encode(x: u8) -> [u8; 32] {
        return [x, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    }

    #[test]
    fn test_zkinterface() {
        assert!(FieldPrime::get_required_bits() <= *FIELD_LENGTH * 8);
        let empty = &[] as &[u8];
        let one = &encode(1);
        let minus_one = &convert_field(&FieldPrime::max_value());

        let code = "
            def main(field x, private field y) -> (field):
                field xx = x * x
                field yy = y * y
                return xx + yy - 1
        ";

        let program = compile::<FieldPrime, &[u8], &[u8], Error>(
            &mut code.as_bytes(), None, None).unwrap();

        // Check the constraint system.
        {
            let mut buf = Vec::<u8>::new();

            setup(program.clone(), &mut buf);

            let mut messages = Messages::new(0);
            messages.push_message(buf).unwrap();
            assert_eq!(messages.into_iter().count(), 2);

            let circuit = messages.last_circuit().unwrap();
            assert_eq!(circuit.free_variable_id(), 6);

            let pub_vars = messages.connection_variables().unwrap();
            assert_eq!(pub_vars, vec![
                Variable { id: 0, value: empty }, // one
                Variable { id: 1, value: empty }, // x
                Variable { id: 2, value: empty }, // return
            ]);

            let pri_vars = messages.private_variables().unwrap();
            assert_eq!(pri_vars, vec![
                Variable { id: 3, value: empty }, // xx
                Variable { id: 4, value: empty }, // y
                Variable { id: 5, value: empty }, // yy
            ]);

            let cs: Vec<_> = messages.iter_constraints().collect();
            assert_eq!(cs, vec![
                Constraint {
                    a: vec![Term { id: 1, value: one }], // x
                    b: vec![Term { id: 1, value: one }], // x
                    c: vec![Term { id: 3, value: one }], // xx
                },
                Constraint {
                    a: vec![Term { id: 4, value: one }], // y
                    b: vec![Term { id: 4, value: one }], // y
                    c: vec![Term { id: 5, value: one }], // yy
                },
                Constraint {
                    a: vec![Term { id: 0, value: one }], // 1
                    b: vec![Term { id: 3, value: one }, Term { id: 5, value: one }, Term { id: 0, value: minus_one }], // xx + yy - 1
                    c: vec![Term { id: 2, value: one }], // return
                },
            ]);
        }

        let witness = program
            .clone()
            .execute::<FieldPrime>(&vec![FieldPrime::from(3), FieldPrime::from(4)])
            .unwrap();

        // Check the witness.
        {
            let mut buf = Vec::<u8>::new();

            generate_proof(program, witness, &mut buf);

            let mut messages = Messages::new(0);
            messages.push_message(buf).unwrap();
            assert_eq!(messages.into_iter().count(), 2);

            let circuit = messages.last_circuit().unwrap();
            assert_eq!(circuit.free_variable_id(), 6);

            let pub_vars = messages.connection_variables().unwrap();
            assert_eq!(pub_vars, vec![
                Variable { id: 0, value: &encode(1) },         // one
                Variable { id: 1, value: &encode(3) },         // x
                Variable { id: 2, value: &encode(5 * 5 - 1) }, // return
            ]);

            let pri_vars = messages.private_variables().unwrap();
            assert_eq!(pri_vars, vec![
                Variable { id: 3, value: &encode(3 * 3) }, // xx
                Variable { id: 4, value: &encode(4) },     // y
                Variable { id: 5, value: &encode(4 * 4) }, // yy
            ]);
        }
    }
}
