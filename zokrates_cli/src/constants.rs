pub const FLATTENED_CODE_DEFAULT_PATH: &str = "out";
pub const ABI_SPEC_DEFAULT_PATH: &str = "abi.json";
pub const VERIFICATION_KEY_DEFAULT_PATH: &str = "verification.key";
pub const PROVING_KEY_DEFAULT_PATH: &str = "proving.key";
pub const VERIFICATION_CONTRACT_DEFAULT_PATH: &str = "verifier.sol";
pub const WITNESS_DEFAULT_PATH: &str = "witness";
pub const JSON_PROOF_PATH: &str = "proof.json";

pub const BELLMAN: &str = "bellman";
pub const LIBSNARK: &str = "libsnark";
pub const ARK: &str = "ark";

lazy_static! {
    pub static ref DEFAULT_STDLIB_PATH: String = dirs::home_dir()
        .map(|p| p.join(".zokrates/stdlib"))
        .unwrap()
        .into_os_string()
        .into_string()
        .unwrap();
}

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

pub const BN128: &str = "bn128";
pub const BLS12_381: &str = "bls12_381";
pub const BLS12_377: &str = "bls12_377";
pub const BW6_761: &str = "bw6_761";
pub const CURVES: &[&str] = &[BN128, BLS12_381, BLS12_377, BW6_761];

pub const G16: &str = "g16";
pub const PGHR13: &str = "pghr13";
pub const GM17: &str = "gm17";

pub const SCHEMES: &[&str] = &[G16, PGHR13, GM17];
