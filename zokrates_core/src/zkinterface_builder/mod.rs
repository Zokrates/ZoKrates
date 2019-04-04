
use zokrates_field::field::{Field, FieldPrime};


/// computes new r1cs file format from givin constrains.
pub struct ZKinterfaceBuilder {
    file_name: String,
    file_path: String,
}

impl ZKinterfaceBuilder{

    pub fn new() -> Self { Self{
        file_name: String::from("zkinterface_r1cs"),
        file_path: String::from("/home/ron/qed-it/Zokrates-zkinterface/r1cs_output/"),
    } }

    pub fn create_file(
        &self,
        num_constraints: usize,
        num_variables: usize,
        a: Vec<Vec<(usize, FieldPrime)>>,
        b: Vec<Vec<(usize, FieldPrime)>>,
        c: Vec<Vec<(usize, FieldPrime)>>) -> bool {

        // message type:
       // zkstandard::zkinterface_generated::zkinterface::R1CSConstraints

        let mut builder = zkstandard::flatbuffers::FlatBufferBuilder::new();

        // create vector of
        let mut vector_lc = vec![];

        for i in 0..num_constraints{

//            let args = zkstandard::zkinterface_generated::zkinterface::BilinearConstraintArgs {
//               linear_combination_a: // converted a[i]
//            }

            let lc = zkstandard::zkinterface_generated::zkinterface::BilinearConstraint::create(&mut builder, &args);
            vector_lc.push(lc);

        }


        let vector_offset = builder.create_vector(vector_lc.as_slice());

        let args = zkstandard::zkinterface_generated::zkinterface::R1CSConstraintsArgs{constraints: Some(vector_offset)};

        // create zkstandard::zkinterface_generated::zkinterface::R1CSConstraints
        let r1cs_constraints = zkstandard::zkinterface_generated::zkinterface::R1CSConstraints::create(&mut builder, &args);
        let root_args = zkstandard::zkinterface_generated::zkinterface::RootArgs{message_type: zkstandard::zkinterface_generated::zkinterface::Message::R1CSConstraints, message: Some(r1cs_constraints.as_union_value())};
        let root = zkstandard::zkinterface_generated::zkinterface::Root::create(&mut builder,&root_args);

        builder.finish_size_prefixed(root, None);

        // serialize message
        builder.write()
        // save to file
    }
}
