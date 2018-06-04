
use std::collections::BTreeMap;

// for r1cs import, can be moved.
// r1cs data strucutre reflecting JSON standard format:
//{variables:["a","b", ... ],
//constraints:[
// [{offset_1:value_a1,offset2:value_a2,...},{offset1:value_b1,offset2:value_b2,...},{offset1:value_c1,offset2:value_c2,...}]
//]}
#[derive(Serialize, Deserialize, Debug)]
pub struct R1CS {
    pub constraints: Vec<Vec<BTreeMap<String, isize>>>,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct Witness {
    pub TestVariables: Vec<usize>
}