mod g16;
mod gm17;

mod utils;

pub use self::g16::G16;
pub use self::gm17::GM17;
use serde::{Deserialize, Serialize};

type G1PairingPoint = (String, String);
type G2PairingPoint = (G1PairingPoint, G1PairingPoint);

#[derive(Serialize, Deserialize)]
struct Proof<T> {
    proof: T,
    inputs: Vec<String>,
    raw: String,
}

impl<'a, T: Serialize + Deserialize<'a>> Proof<T> {
    fn new(proof: T, inputs: Vec<String>, raw: String) -> Self {
        Proof { proof, inputs, raw }
    }
    fn from_str(proof: &'a str) -> Proof<T> {
        serde_json::from_str(proof).expect("Invalid proof json format")
    }
    fn to_json_pretty(&self) -> String {
        serde_json::to_string_pretty(self).unwrap()
    }
}
