pub const BN128: &str = "bn128";
pub const BLS12_381: &str = "bls12_381";
pub const CURVES: &[&str] = &[BN128, BLS12_381];

pub const G16: &str = "g16";
#[cfg(feature = "libsnark")]
pub const PGHR13: &str = "pghr13";
#[cfg(feature = "libsnark")]
pub const GM17: &str = "gm17";
#[cfg(feature = "libsnark")]
pub const SCHEMES: &[&str] = &[G16, PGHR13, GM17];
#[cfg(not(feature = "libsnark"))]
pub const SCHEMES: &[&str] = &[G16];
