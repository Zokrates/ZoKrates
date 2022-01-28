pub const FLATTENED_CODE_DEFAULT_PATH: &str = "out";
pub const ABI_SPEC_DEFAULT_PATH: &str = "abi.json";
pub const VERIFICATION_KEY_DEFAULT_PATH: &str = "verification.key";
pub const PROVING_KEY_DEFAULT_PATH: &str = "proving.key";
pub const VERIFICATION_CONTRACT_DEFAULT_PATH: &str = "verifier.sol";
pub const WITNESS_DEFAULT_PATH: &str = "witness";
pub const JSON_PROOF_PATH: &str = "proof.json";
pub const UNIVERSAL_SETUP_DEFAULT_PATH: &str = "universal_setup.dat";
pub const UNIVERSAL_SETUP_DEFAULT_SIZE: &str = "10";
pub const SMTLIB2_DEFAULT_PATH: &str = "out.smt2";
pub const MPC_DEFAULT_PATH: &str = "mpc.params";

lazy_static! {
    pub static ref DEFAULT_STDLIB_PATH: String = dirs::home_dir()
        .map(|p| p.join(".zokrates/stdlib"))
        .unwrap()
        .into_os_string()
        .into_string()
        .unwrap();
}
