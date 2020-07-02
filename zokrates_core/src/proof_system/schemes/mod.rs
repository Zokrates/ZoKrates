use proof_system::solidity::SolidityAbi;
use serde::de::DeserializeOwned;
use serde::Serialize;
use zokrates_field::Field;

pub mod gm17;
pub mod groth16;
pub mod pghr13;

pub trait Scheme<T: Field>
where
    Self::VerificationKey: Serialize + DeserializeOwned,
    Self::ProofPoints: Serialize + DeserializeOwned,
{
    type ProvingKey;
    type VerificationKey;
    type ProofPoints;

    fn export_solidity_verifier(vk: Self::VerificationKey, abi: SolidityAbi) -> String;
}
