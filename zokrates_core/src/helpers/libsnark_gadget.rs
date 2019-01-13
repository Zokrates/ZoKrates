use helpers::{Executable, Signed};
use libsnark::{get_sha256round_witness};
use serde_json;
use standard;
use std::fmt;
use zokrates_field::field::Field;

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize)]
pub enum LibsnarkGadgetHelper {
    Sha256Round
}

impl fmt::Display for LibsnarkGadgetHelper {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            LibsnarkGadgetHelper::Sha256Round => write!(f, "Sha256Round"),
        }
    }
}

impl<T: Field> Executable<T> for LibsnarkGadgetHelper {
    fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, String> {
        let witness_result: Result<standard::Witness, serde_json::Error> = match self {
            LibsnarkGadgetHelper::Sha256Round => {
                serde_json::from_str(&get_sha256round_witness(inputs))
            }
        };

        if let Err(e) = witness_result {
            return Err(format!("{}", e));
        }
        
        Ok(witness_result
            .unwrap()
            .variables
            .iter()
            .map(|&i| T::from(i))
            .collect())
    }
}

impl Signed for LibsnarkGadgetHelper {
    fn get_signature(&self) -> (usize, usize) {
        match self {
            LibsnarkGadgetHelper::Sha256Round => (768, 25817)
        }
    }
}
