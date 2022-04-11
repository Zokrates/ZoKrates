use primitive_types::U256;

use std::{
    error::Error as ErrorTrait,
    fmt::{self, Debug},
};

pub mod address;
pub mod contract;
pub mod evm;

pub type Error = Box<dyn ErrorTrait>;

#[derive(Debug)]
pub struct EvmTestError(String);

impl ErrorTrait for EvmTestError {
    fn source(&self) -> Option<&(dyn ErrorTrait + 'static)> {
        None
    }
}

impl fmt::Display for EvmTestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub fn to_be_bytes(n: &U256) -> [u8; 32] {
    let mut input_bytes: [u8; 32] = [0; 32];
    n.to_big_endian(&mut input_bytes);
    input_bytes
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{address::Address, contract::Contract, evm::Evm};
    use ethabi::Token;
    use rand::{rngs::StdRng, SeedableRng};

    #[test]
    fn simple_storage_contract_test() {
        let mut rng = StdRng::seed_from_u64(0u64);

        // Compile contract
        let contract_path = format!(
            "{}/contracts/simple_storage.sol",
            env!("CARGO_MANIFEST_DIR")
        );
        let contract =
            Contract::compile_from_solidity_file(contract_path, "SimpleStorage", false).unwrap();

        // Setup EVM
        let mut evm = Evm::default();
        let deployer = Address::random(&mut rng);
        evm.create_account(&deployer, 0);

        // Deploy contract
        let create_result = evm
            .deploy(
                contract.encode_create_contract_bytes(&[]).unwrap(),
                &deployer,
            )
            .unwrap();
        let contract_addr = create_result.addr.clone();
        println!("Contract deploy gas cost: {}", create_result.gas);

        // Call get function on contract
        let get_result = evm
            .call(
                contract.encode_call_contract_bytes("get", &[]).unwrap(),
                &contract_addr,
                &deployer,
            )
            .unwrap();
        assert_eq!(&get_result.out, &to_be_bytes(&U256::from(0)));

        // Call set function on contract
        let _ = evm
            .call(
                contract
                    .encode_call_contract_bytes(
                        "set",
                        &[Token::Tuple(vec![Token::Uint(U256::from(40))])],
                    )
                    .unwrap(),
                &contract_addr,
                &deployer,
            )
            .unwrap();

        // Call get function on contract
        let get_result = evm
            .call(
                contract.encode_call_contract_bytes("get", &[]).unwrap(),
                &contract_addr,
                &deployer,
            )
            .unwrap();
        assert_eq!(&get_result.out, &to_be_bytes(&U256::from(40)));
        println!("{:?}", get_result);
    }
}
