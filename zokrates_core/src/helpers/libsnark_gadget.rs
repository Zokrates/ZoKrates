use field::Field;
use helpers::{Executable, Signed};
use libsnark::{get_ethsha256_witness, get_sha256_witness, get_sha256round_witness};
use serde_json;
use standard;
use std::fmt;

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub enum LibsnarkGadgetHelper {
    Sha256Compress,
    Sha256Ethereum,
    Sha256Round
}

impl fmt::Display for LibsnarkGadgetHelper {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            LibsnarkGadgetHelper::Sha256Compress => write!(f, "Sha256Compress"),
            LibsnarkGadgetHelper::Sha256Ethereum => write!(f, "Sha256Ethereum"),
            LibsnarkGadgetHelper::Sha256Round => write!(f, "Sha256Round"),
        }
    }
}

impl<T: Field> Executable<T> for LibsnarkGadgetHelper {
    fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, String> {
        let witness_result: Result<standard::Witness, serde_json::Error> = match self {
            LibsnarkGadgetHelper::Sha256Compress => {
                serde_json::from_str(&get_sha256_witness(inputs))
            }
            LibsnarkGadgetHelper::Sha256Ethereum => {
                serde_json::from_str(&get_ethsha256_witness(inputs))
            }
            LibsnarkGadgetHelper::Sha256Round => {
                serde_json::from_str(&get_sha256round_witness(inputs))
            }
        };

        if let Err(e) = witness_result {
            return Err(format!("{}", e));
        }

        let lol : Vec<T> = witness_result
            .unwrap()
            .variables
            .iter()
            .map(|&i| T::from(i))
            .collect();
        
        println!("#Debug Witness size: {:#?}", lol.len());
        println!("#Debug Witness variables: {:#?}", lol);
        Ok(lol)
    }
}

impl Signed for LibsnarkGadgetHelper {
    fn get_signature(&self) -> (usize, usize) {
        match self {
            LibsnarkGadgetHelper::Sha256Compress => (512, 25562),
            LibsnarkGadgetHelper::Sha256Ethereum => (512, 50610),
            // LibsnarkGadgetHelper::Sha256Round => (612, 25662)
            LibsnarkGadgetHelper::Sha256Round => (768, 25818)
        }
    }
}
