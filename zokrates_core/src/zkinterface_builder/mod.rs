use std::fs::File;
use zokrates_field::field::{FieldPrime, Field};
use zkstandard::zkinterface_generated::zkinterface::VariableValues;
use zkstandard::flatbuffers::WIPOffset;
use zkstandard::flatbuffers;
use std::io::Write;



pub struct ZKinterfaceBuilder {
    file_name: String,
}


impl ZKinterfaceBuilder{

    pub fn new() -> Self { Self{
        file_name: String::from("zkinterface_r1cs"),
    } }

    pub fn create_file(
        self,
        num_constraints: usize,
        a: & Vec<Vec<(usize, FieldPrime)>>,
        b: & Vec<Vec<(usize, FieldPrime)>>,
        c: & Vec<Vec<(usize, FieldPrime)>>,
        output_path: &str,
        )  {

        let mut builder = zkstandard::flatbuffers::FlatBufferBuilder::new();

        // create vector of
        let mut vector_lc = vec![];

        for i in 0..num_constraints{

            let a_var_val = convert_to_variable_values(&mut builder, &a[i]);
            let b_var_val = convert_to_variable_values(&mut builder, &b[i]);
            let c_var_val = convert_to_variable_values(&mut builder, &c[i]);

            let args = zkstandard::zkinterface_generated::zkinterface::BilinearConstraintArgs {
                linear_combination_a: Some(a_var_val),
                linear_combination_b: Some(b_var_val),
                linear_combination_c: Some(c_var_val),
            };

            let lc = zkstandard::zkinterface_generated::zkinterface::BilinearConstraint::create(&mut builder, &args);
            vector_lc.push(lc);
        }

        let vector_offset = builder.create_vector(vector_lc.as_slice());

        let args = zkstandard::zkinterface_generated::zkinterface::R1CSConstraintsArgs{constraints: Some(vector_offset)};

        let r1cs_constraints = zkstandard::zkinterface_generated::zkinterface::R1CSConstraints::create(&mut builder, &args);
        let root_args = zkstandard::zkinterface_generated::zkinterface::RootArgs{message_type: zkstandard::zkinterface_generated::zkinterface::Message::R1CSConstraints, message: Some(r1cs_constraints.as_union_value())};
        let root = zkstandard::zkinterface_generated::zkinterface::Root::create(&mut builder,&root_args);

        builder.finish_size_prefixed(root, None);

        self.write_r1cs_to_file(builder.finished_data(),output_path);
    }



    fn write_r1cs_to_file(&self, data: &[u8], output_path: &str) {

        let mut save_file_to: String = String::from(output_path);

        if str::ends_with(output_path, "/") == false {
            save_file_to = format!("{}/", save_file_to);
        }

        save_file_to = format!("{}{}",save_file_to, self.file_name);

        let mut output = File::create(save_file_to).unwrap();

        output.write_all(data).unwrap();
    }
}





fn convert_to_variable_values<'a>(builder:&mut flatbuffers::FlatBufferBuilder<'a>, item: &Vec<(usize, FieldPrime)>) -> (WIPOffset<VariableValues<'a>>) {
    // convert item->usize to Vec<usize>
    let mut var_ids: Vec<u64> = Vec::new();
    let mut elements: Vec<u8> = Vec::new();

    for i in 0..item.len() {
        var_ids.push(item[i].0 as u64);

        let mut ele_byte_vec = item[i].1.into_byte_vector().clone();

        elements.append(&mut ele_byte_vec);
    }

    for i in 0..item.len() {
        var_ids.push(item[i].0 as u64)
    }

    let var_ids_vector = builder.create_vector(&var_ids);
    let elements_vector = builder.create_vector(&elements);


    let var_val_args = zkstandard::zkinterface_generated::zkinterface::VariableValuesArgs{
        variable_ids: Some(var_ids_vector),
        elements: Some(elements_vector),
    };

    let var_val = zkstandard::zkinterface_generated::zkinterface::VariableValues::create(builder,&var_val_args);

    return var_val
}

