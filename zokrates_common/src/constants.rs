pub const BELLMAN: &str = "bellman";
pub const ARK: &str = "ark";
pub const LIBSNARK: &str = "libsnark";

pub const BN128: &str = "bn128";
pub const BLS12_381: &str = "bls12_381";
pub const BLS12_377: &str = "bls12_377";
pub const BW6_761: &str = "bw6_761";

pub const G16: &str = "g16";
pub const GM17: &str = "gm17";
pub const MARLIN: &str = "marlin";
pub const PGHR13: &str = "pghr13";

#[cfg(any(feature = "bellman", feature = "ark", feature = "libsnark"))]
pub const BACKENDS: &[&str] = if cfg!(feature = "libsnark") {
    if cfg!(feature = "ark") {
        if cfg!(feature = "bellman") {
            &[BELLMAN, LIBSNARK, ARK]
        } else {
            &[LIBSNARK, ARK]
        }
    } else if cfg!(feature = "bellman") {
        &[BELLMAN, LIBSNARK]
    } else {
        &[LIBSNARK]
    }
} else if cfg!(feature = "ark") {
    if cfg!(feature = "bellman") {
        &[BELLMAN, ARK]
    } else {
        &[ARK]
    }
} else if cfg!(feature = "bellman") {
    &[BELLMAN]
} else {
    &[]
};

pub const CURVES: &[&str] = &[BN128, BLS12_381, BLS12_377, BW6_761];
pub const SCHEMES: &[&str] = &[G16, PGHR13, GM17, MARLIN];
pub const UNIVERSAL_SCHEMES: &[&str] = &[MARLIN];
