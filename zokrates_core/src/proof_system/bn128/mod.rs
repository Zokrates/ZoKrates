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

#[derive(Serialize, Deserialize)]
pub struct G1Affine(String, String);

#[derive(Serialize, Deserialize)]
pub struct G2Affine(G1Affine, G1Affine);

impl std::fmt::Display for G1Affine {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}, {}", self.0, self.1)
    }
}

impl std::fmt::Display for G2Affine {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}], [{}]", self.0, self.1)
    }
}
