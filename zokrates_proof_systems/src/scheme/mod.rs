use serde::de::DeserializeOwned;
use serde::Serialize;
use zokrates_field::Field;

pub mod gm17;
pub mod groth16;
pub mod marlin;
pub mod pghr13;

pub use self::gm17::GM17;
pub use self::groth16::G16;
pub use self::marlin::Marlin;
pub use self::pghr13::PGHR13;

pub trait Scheme<T: Field>: Serialize {
    const NAME: &'static str;

    type VerificationKey: Serialize + DeserializeOwned;
    type ProofPoints: Serialize + DeserializeOwned;
}

pub trait NonUniversalScheme<T: Field>: Scheme<T> {}

pub trait UniversalScheme<T: Field>: Scheme<T> {}

pub trait MpcScheme<T: Field>: Scheme<T> {}
