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

impl ToString for G1Affine {
    fn to_string(&self) -> String {
        format!("{}, {}", self.0, self.1)
    }
}

impl ToString for G2Affine {
    fn to_string(&self) -> String {
        format!("[{}], [{}]", self.0.to_string(), self.1.to_string())
    }
}
