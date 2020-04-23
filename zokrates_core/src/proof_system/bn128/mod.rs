mod g16;
#[cfg(feature = "libsnark")]
mod gm17;
#[cfg(feature = "libsnark")]
mod pghr13;

mod utils;

pub use self::g16::G16;
#[cfg(feature = "libsnark")]
pub use self::gm17::GM17;
#[cfg(feature = "libsnark")]
pub use self::pghr13::PGHR13;

type G1PairingPoint = (String, String);
type G2PairingPoint = (G1PairingPoint, G1PairingPoint);

#[derive(Serialize, Deserialize)]
struct Proof<T> {
    proof: T,
    inputs: Vec<String>,
    raw: String,
}

impl<T> Proof<T> {
    fn new(proof: T, inputs: Vec<String>, raw: String) -> Self {
        Proof { proof, inputs, raw }
    }
}
