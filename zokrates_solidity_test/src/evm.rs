use primitive_types::U256;
use revm::{AccountInfo, InMemoryDB, Log, Return, TransactOut, TransactTo, EVM};

use crate::{address::Address, Error, EvmTestError};

#[derive(Debug)]
pub struct CallResult {
    pub op_out: Return,
    pub out: Vec<u8>,
    pub gas: u64,
    pub log_out: Vec<Log>,
}

#[derive(Debug)]
pub struct CreateContractResult {
    pub addr: Address,
    pub gas: u64,
}

pub struct Evm {
    vm: EVM<InMemoryDB>,
}

impl Evm {
    pub fn new() -> Self {
        let mut vm = revm::new();
        vm.database(InMemoryDB::default());
        Self { vm }
    }

    pub fn call(&mut self, input: Vec<u8>, addr: &Address, caller: &Address) -> Result<CallResult, Error> {
        self.vm.env.tx.caller = caller.as_ref().clone();
        self.vm.env.tx.transact_to = TransactTo::Call(addr.as_ref().clone());
        self.vm.env.tx.data = input.into();
        let (op_out, tx_out, gas, log_out) = self.vm.transact_commit();
        let out = match tx_out {
            TransactOut::Call(out) => Ok(out.to_vec()),
            _ => Err(Box::new(EvmTestError("call contract function failed".to_string()))),
        }?;
        Ok(CallResult {
            op_out,
            out,
            gas,
            log_out,
        })
    }

    pub fn deploy(
        &mut self,
        contract: Vec<u8>,
        deployer: &Address,
    ) -> Result<CreateContractResult, Error> {
        match self
            .vm
            .db()
            .unwrap()
            .cache()
            .get_key_value(deployer.as_ref())
        {
            Some(_) => {
                self.vm.env.tx.caller = deployer.as_ref().clone();
                self.vm.env.tx.transact_to = TransactTo::create();
                self.vm.env.tx.data = contract.into();
                let (_, tx_out, gas, _) = self.vm.transact_commit();
                let contract_address = match tx_out {
                    TransactOut::Create(_, Some(addr)) => Ok(Address(addr)),
                    _ => Err(Box::new(EvmTestError("create contract failed".to_string()))),
                }?;
                Ok(CreateContractResult {
                    addr: contract_address,
                    gas,
                })
            }
            None => Err(Box::new(EvmTestError(
                "deployer address not found".to_string(),
            ))),
        }
    }

    pub fn create_account(&mut self, address: &Address, balance: impl Into<U256>) {
        let acc = AccountInfo::from_balance(balance.into());
        self.vm
            .db()
            .unwrap()
            .insert_cache(address.as_ref().clone(), acc);
    }

    pub fn set_account_balance(
        &mut self,
        address: &Address,
        balance: impl Into<U256>,
    ) -> Result<(), Error> {
        let mut acc = self
            .vm
            .db()
            .unwrap()
            .cache()
            .get(address.as_ref())
            .ok_or(Box::new(EvmTestError(
                "account address not found".to_string(),
            )))?
            .clone();
        acc.balance = balance.into();
        self.vm
            .db()
            .unwrap()
            .insert_cache(address.as_ref().clone(), acc);
        Ok(())
    }

    pub fn balance_of(&mut self, address: &Address) -> U256 {
        match self.vm.db().unwrap().cache().get(address.as_ref()) {
            Some(acc) => acc.balance,
            None => 0.into(),
        }
    }

    pub fn get_account(&mut self, address: &Address) -> Option<AccountInfo> {
        self.vm.db().unwrap().cache().get(address.as_ref()).cloned()
    }
}
