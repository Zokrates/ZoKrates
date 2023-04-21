//
// @file field.rs
// @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
// @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
// @date 2017

#[cfg(feature = "bellman_extensions")]
use bellman_ce::pairing::{ff::ScalarEngine, Engine};
#[cfg(feature = "bellperson_extensions")]
use nova_snark::provider::pedersen::CommitmentEngine;
use num_bigint::BigUint;
use num_traits::{CheckedDiv, One, Zero};
use serde::{Deserialize, Serialize};
use std::convert::{From, TryFrom};
use std::fmt;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::io::{Read, Write};
use std::ops::{Add, Div, Mul, Sub};

#[cfg(feature = "bellperson_extensions")]
use nova_snark::traits::Group;

pub trait Pow<RHS> {
    type Output;
    fn pow(self, _: RHS) -> Self::Output;
}

#[cfg(feature = "bellperson_extensions")]
pub trait Cycle {
    type Other: Field + BellpersonFieldExtensions + Cycle<Other = Self>;
    type Point: Group<
        Base = <<Self::Other as Cycle>::Point as Group>::Scalar,
        CE = CommitmentEngine<Self::Point>,
    >;
}

#[cfg(feature = "bellman_extensions")]
pub trait BellmanFieldExtensions {
    /// An associated type to be able to operate with Bellman ff traits
    type BellmanEngine: Engine;

    fn from_bellman(e: <Self::BellmanEngine as ScalarEngine>::Fr) -> Self;
    fn into_bellman(self) -> <Self::BellmanEngine as ScalarEngine>::Fr;
    fn new_fq2(c0: &str, c1: &str) -> <Self::BellmanEngine as Engine>::Fqe;
}

#[cfg(feature = "bellperson_extensions")]
pub trait BellpersonFieldExtensions {
    /// An associated type to be able to operate with Bellperson ff traits
    type BellpersonField: ff::PrimeField;

    fn from_bellperson(e: Self::BellpersonField) -> Self;
    fn into_bellperson(self) -> Self::BellpersonField;
}
pub trait ArkFieldExtensions {
    /// An associated type to be able to operate with ark ff traits
    type ArkEngine: ark_ec::PairingEngine;

    fn from_ark(e: <Self::ArkEngine as ark_ec::PairingEngine>::Fr) -> Self;
    fn into_ark(self) -> <Self::ArkEngine as ark_ec::PairingEngine>::Fr;
}

pub struct FieldParseError;

impl fmt::Debug for FieldParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Failed to parse to field element")
    }
}

pub enum G2Type {
    Fq,
    Fq2,
}

pub trait Field:
    'static
    + Sync
    + Send
    + From<u128>
    + From<u64>
    + From<u32>
    + From<u16>
    + From<u8>
    + From<usize>
    + From<bool>
    + From<i32>
    + TryFrom<BigUint, Error = ()>
    + Zero
    + One
    + Clone
    + Copy
    + PartialEq
    + Eq
    + Hash
    + PartialOrd
    + Ord
    + Display
    + Debug
    + Default
    + Hash
    + Add<Self, Output = Self>
    + for<'a> Add<&'a Self, Output = Self>
    + Sub<Self, Output = Self>
    + for<'a> Sub<&'a Self, Output = Self>
    + Mul<Self, Output = Self>
    + for<'a> Mul<&'a Self, Output = Self>
    + CheckedDiv
    + Div<Self, Output = Self>
    + for<'a> Div<&'a Self, Output = Self>
    + Pow<usize, Output = Self>
    + for<'a> Deserialize<'a>
    + Serialize
    + num_traits::CheckedAdd
    + num_traits::CheckedMul
{
    const G2_TYPE: G2Type = G2Type::Fq2;
    // Read field from the reader
    fn read<R: Read>(reader: R) -> std::io::Result<Self>;
    // Write field to the writer
    fn write<W: Write>(&self, writer: W) -> std::io::Result<()>;
    /// Returns this `Field`'s contents as little-endian byte vector
    fn to_byte_vector(&self) -> Vec<u8>;
    /// Returns an element of this `Field` from a little-endian byte vector
    fn from_byte_vector(_: Vec<u8>) -> Self;
    /// Returns this `Field`'s contents as decimal string
    fn to_dec_string(&self) -> String;
    /// Returns the multiplicative inverse, i.e.: self * self.inverse_mul() = Self::one()
    fn inverse_mul(&self) -> Option<Self>;
    /// Returns the smallest value that can be represented by this field type.
    fn min_value() -> Self;
    /// Returns the largest value that can be represented by this field type.
    fn max_value() -> Self;
    /// Returns the largest value `m` such that there exist a number of bits `n` so that any value smaller or equal to
    /// m` has a single `n`-bit decomposition
    fn max_unique_value() -> Self;
    /// Return the number of bits required to represent this element
    fn to_bits_be(&self) -> Vec<bool>;
    /// Returns the number of bits required to represent any element of this field type.
    fn get_required_bits() -> usize;
    /// Tries to parse a string into this representation
    fn try_from_dec_str(s: &str) -> Result<Self, FieldParseError>;
    fn try_from_str(s: &str, radix: u32) -> Result<Self, FieldParseError>;
    /// Returns a decimal string representing a the member of the equivalence class of this `Field` in Z/pZ
    /// which lies in [-(p-1)/2, (p-1)/2]
    fn to_compact_dec_string(&self) -> String;
    /// Returns the size of the field as a decimal string
    fn id() -> [u8; 4];
    /// the name of the curve associated with this field
    fn name() -> &'static str;
    /// Gets the number of bits
    fn bits(&self) -> u32;
    /// Returns the value as a BigUint
    fn to_biguint(&self) -> BigUint;
}

#[macro_use]
mod prime_field {
    macro_rules! prime_field {
        ($name:expr, $v:ty, $g2_ty:expr) => {
            use crate::{Field, FieldParseError, Pow};
            use ark_ff::{Field as ArkField, PrimeField};
            use num_bigint::BigUint;
            use num_traits::{CheckedDiv, One, Zero};
            use serde::de::{self, Visitor};
            use serde::{Deserialize, Deserializer, Serialize, Serializer};
            use std::convert::From;
            use std::convert::TryFrom;
            use std::fmt;
            use std::fmt::{Debug, Display};
            use std::io::{Read, Write};
            use std::ops::{Add, Div, Mul, Sub};

            type Fr = $v;

            #[derive(PartialEq, PartialOrd, Clone, Copy, Eq, Ord, Hash)]
            pub struct FieldPrime {
                v: Fr,
            }

            impl Field for FieldPrime {
                const G2_TYPE: G2Type = $g2_ty;

                fn bits(&self) -> u32 {
                    use ark_ff::BigInteger;
                    let bits = self.v.into_repr().to_bits_be();
                    let mut size = bits.len();
                    for bit in bits {
                        if !bit {
                            size -= 1;
                        } else {
                            break;
                        }
                    }
                    std::cmp::max(size as u32, 1)
                }

                fn to_biguint(&self) -> BigUint {
                    use ark_ff::BigInteger;
                    BigUint::from_bytes_le(&self.v.into_repr().to_bytes_le())
                }

                fn to_bits_be(&self) -> Vec<bool> {
                    use ark_ff::BigInteger;
                    let res = self.v.into_repr().to_bits_be();
                    res[res.len() - Self::get_required_bits()..].to_vec()
                }

                fn to_byte_vector(&self) -> Vec<u8> {
                    use ark_ff::BigInteger;
                    self.v.into_repr().to_bytes_le()
                }

                fn read<R: Read>(reader: R) -> std::io::Result<Self> {
                    use ark_ff::FromBytes;
                    Ok(FieldPrime {
                        v: Fr::read(reader)?,
                    })
                }

                fn write<W: Write>(&self, mut writer: W) -> std::io::Result<()> {
                    use ark_ff::ToBytes;
                    self.v.write(&mut writer)?;
                    Ok(())
                }

                fn from_byte_vector(bytes: Vec<u8>) -> Self {
                    use ark_ff::FromBytes;
                    FieldPrime {
                        v: Fr::from(<Fr as PrimeField>::BigInt::read(&bytes[..]).unwrap()),
                    }
                }

                fn to_dec_string(&self) -> String {
                    self.to_string()
                }

                fn inverse_mul(&self) -> Option<Self> {
                    use ark_ff::Field;
                    Some(FieldPrime {
                        v: self.v.inverse()?,
                    })
                }

                fn min_value() -> FieldPrime {
                    FieldPrime { v: Fr::zero() }
                }
                fn max_value() -> FieldPrime {
                    FieldPrime { v: -Fr::one() }
                }
                fn max_unique_value() -> FieldPrime {
                    FieldPrime {
                        v: Fr::from(2u32).pow([Self::get_required_bits() as u64 - 1]) - Fr::one(),
                    }
                }
                fn get_required_bits() -> usize {
                    use ark_ff::FpParameters;
                    <Fr as PrimeField>::Params::MODULUS_BITS as usize
                }
                fn try_from_dec_str(s: &str) -> Result<Self, FieldParseError> {
                    use std::str::FromStr;

                    Ok(FieldPrime {
                        v: Fr::from_str(s).map_err(|_| FieldParseError)?,
                    })
                }
                fn try_from_str(s: &str, radix: u32) -> Result<Self, FieldParseError> {
                    let x = BigUint::parse_bytes(s.as_bytes(), radix).ok_or(FieldParseError)?;
                    FieldPrime::try_from(x).map_err(|_| FieldParseError)
                }
                fn to_compact_dec_string(&self) -> String {
                    //values up to (p-1)/2 included are represented as positive, values between (p+1)/2 and p-1 as represented as negative by subtracting p
                    if self.v.into_repr() <= Fr::modulus_minus_one_div_two() {
                        format!("{}", self.to_string())
                    } else {
                        format!(
                            "(-{})",
                            (FieldPrime::max_value() - self + FieldPrime::one()).to_string()
                        )
                    }
                }
                fn id() -> [u8; 4] {
                    let mut res = [0u8; 4];
                    use ark_ff::BigInteger;
                    use ark_ff::FpParameters;
                    use sha2::{Digest, Sha256};
                    let hash = Sha256::digest(&<Fr as PrimeField>::Params::MODULUS.to_bytes_le());
                    for i in 0..4 {
                        res[i] = hash[i];
                    }
                    res
                }

                fn name() -> &'static str {
                    $name
                }
            }

            impl Default for FieldPrime {
                fn default() -> Self {
                    FieldPrime { v: Fr::zero() }
                }
            }

            impl Display for FieldPrime {
                fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                    write!(f, "{}", self.to_biguint())
                }
            }

            impl Debug for FieldPrime {
                fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                    write!(f, "{}", self.to_biguint())
                }
            }

            impl From<u128> for FieldPrime {
                fn from(num: u128) -> Self {
                    FieldPrime { v: Fr::from(num) }
                }
            }

            impl From<u64> for FieldPrime {
                fn from(num: u64) -> Self {
                    FieldPrime { v: Fr::from(num) }
                }
            }

            impl From<u32> for FieldPrime {
                fn from(num: u32) -> Self {
                    FieldPrime { v: Fr::from(num) }
                }
            }

            impl From<u16> for FieldPrime {
                fn from(num: u16) -> Self {
                    FieldPrime { v: Fr::from(num) }
                }
            }

            impl From<u8> for FieldPrime {
                fn from(num: u8) -> Self {
                    FieldPrime { v: Fr::from(num) }
                }
            }

            impl From<usize> for FieldPrime {
                fn from(num: usize) -> Self {
                    FieldPrime {
                        v: Fr::from(num as u128),
                    }
                }
            }

            impl From<bool> for FieldPrime {
                fn from(b: bool) -> Self {
                    FieldPrime { v: Fr::from(b) }
                }
            }

            impl From<i32> for FieldPrime {
                fn from(num: i32) -> Self {
                    if num < 0 {
                        FieldPrime {
                            v: -Fr::from((-num) as u32),
                        }
                    } else {
                        FieldPrime {
                            v: Fr::from(num as u32),
                        }
                    }
                }
            }

            impl TryFrom<BigUint> for FieldPrime {
                type Error = ();

                fn try_from(value: BigUint) -> Result<Self, ()> {
                    match value <= Self::max_value().to_biguint() {
                        true => {
                            use std::str::FromStr;
                            Ok(FieldPrime {
                                v: Fr::from_str(&value.to_string()).unwrap(),
                            })
                        }
                        false => Err(()),
                    }
                }
            }

            impl Zero for FieldPrime {
                fn zero() -> FieldPrime {
                    FieldPrime { v: Fr::zero() }
                }
                fn is_zero(&self) -> bool {
                    self.v.is_zero()
                }
            }

            impl One for FieldPrime {
                fn one() -> FieldPrime {
                    FieldPrime { v: Fr::one() }
                }
            }

            impl Add<FieldPrime> for FieldPrime {
                type Output = FieldPrime;

                fn add(self, other: FieldPrime) -> FieldPrime {
                    FieldPrime {
                        v: self.v + other.v,
                    }
                }
            }

            impl<'a> Add<&'a FieldPrime> for FieldPrime {
                type Output = FieldPrime;

                fn add(self, other: &FieldPrime) -> FieldPrime {
                    FieldPrime {
                        v: self.v + other.v,
                    }
                }
            }

            impl Sub<FieldPrime> for FieldPrime {
                type Output = FieldPrime;

                fn sub(self, other: FieldPrime) -> FieldPrime {
                    FieldPrime {
                        v: self.v - other.v,
                    }
                }
            }

            impl<'a> Sub<&'a FieldPrime> for FieldPrime {
                type Output = FieldPrime;

                fn sub(self, other: &FieldPrime) -> FieldPrime {
                    FieldPrime {
                        v: self.v - other.v,
                    }
                }
            }

            impl Mul<FieldPrime> for FieldPrime {
                type Output = FieldPrime;

                fn mul(self, other: FieldPrime) -> FieldPrime {
                    FieldPrime {
                        v: self.v * other.v,
                    }
                }
            }

            impl<'a> Mul<&'a FieldPrime> for FieldPrime {
                type Output = FieldPrime;

                fn mul(self, other: &FieldPrime) -> FieldPrime {
                    FieldPrime {
                        v: self.v * other.v,
                    }
                }
            }

            impl CheckedDiv for FieldPrime {
                fn checked_div(&self, other: &FieldPrime) -> Option<FieldPrime> {
                    if other.v == Fr::zero() {
                        None
                    } else {
                        Some(FieldPrime {
                            v: self.v / other.v,
                        })
                    }
                }
            }

            impl Div<FieldPrime> for FieldPrime {
                type Output = FieldPrime;

                fn div(self, other: FieldPrime) -> FieldPrime {
                    self.checked_div(&other).unwrap()
                }
            }

            impl<'a> Div<&'a FieldPrime> for FieldPrime {
                type Output = FieldPrime;

                fn div(self, other: &FieldPrime) -> FieldPrime {
                    self.checked_div(&other).unwrap()
                }
            }

            impl Pow<usize> for FieldPrime {
                type Output = FieldPrime;

                fn pow(self, exp: usize) -> FieldPrime {
                    FieldPrime {
                        v: self.v.pow(&[exp as u64]),
                    }
                }
            }

            impl num_traits::CheckedAdd for FieldPrime {
                fn checked_add(&self, other: &Self) -> Option<Self> {
                    let bound = Self::max_unique_value();

                    assert!(self <= &bound);
                    assert!(other <= &bound);

                    let left = self.to_biguint();
                    let right = other.to_biguint();

                    let big_res = left + right;

                    // we only go up to 2**(bitwidth - 1) because after that we lose uniqueness of bit decomposition
                    if big_res > bound.to_biguint() {
                        None
                    } else {
                        Some(self.clone() + other)
                    }
                }
            }

            impl num_traits::CheckedMul for FieldPrime {
                fn checked_mul(&self, other: &Self) -> Option<Self> {
                    let bound = Self::max_unique_value();

                    assert!(self <= &bound);
                    assert!(other <= &bound);

                    let left = self.to_biguint();
                    let right = other.to_biguint();

                    let big_res = left * right;

                    // we only go up to 2**(bitwidth - 1) because after that we lose uniqueness of bit decomposition
                    if big_res > bound.to_biguint() {
                        None
                    } else {
                        Some(self.clone() * other)
                    }
                }
            }

            impl Serialize for FieldPrime {
                fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
                where
                    S: Serializer,
                {
                    use ark_serialize::CanonicalSerialize;
                    use serde::ser::Error;
                    let mut data: Vec<u8> = vec![];
                    self.v
                        .serialize(&mut data)
                        .map_err(|e| S::Error::custom(e.to_string()))?;
                    serializer.serialize_bytes(&data)
                }
            }

            struct FieldVisitor;

            use serde::de::SeqAccess;

            impl<'de> Visitor<'de> for FieldVisitor {
                type Value = FieldPrime;

                fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                    formatter.write_str("an ark field element")
                }

                fn visit_bytes<E>(self, value: &[u8]) -> Result<Self::Value, E>
                where
                    E: de::Error,
                {
                    use ark_serialize::CanonicalDeserialize;
                    let value: Fr = Fr::deserialize(value).map_err(|e| E::custom(e.to_string()))?;

                    Ok(FieldPrime { v: value })
                }

                fn visit_byte_buf<E>(self, value: Vec<u8>) -> Result<Self::Value, E>
                where
                    E: de::Error,
                {
                    self.visit_bytes(&value[..])
                }

                fn visit_seq<A>(self, value: A) -> Result<Self::Value, A::Error>
                where
                    A: SeqAccess<'de>,
                {
                    let mut value = value;
                    let mut elements = vec![];
                    while let Some(v) = value.next_element()? {
                        elements.push(v);
                    }

                    self.visit_bytes(&elements[..])
                }
            }

            impl<'de> Deserialize<'de> for FieldPrime {
                fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
                where
                    D: Deserializer<'de>,
                {
                    deserializer.deserialize_bytes(FieldVisitor)
                }
            }
        };
    }

    #[cfg(feature = "bellman_extensions")]
    macro_rules! bellman_extensions {
        ($bellman_type:ty, $fq2_type:ident) => {
            use crate::BellmanFieldExtensions;
            use bellman_ce::pairing::ff::ScalarEngine;

            impl BellmanFieldExtensions for FieldPrime {
                type BellmanEngine = $bellman_type;

                fn from_bellman(e: <Self::BellmanEngine as ScalarEngine>::Fr) -> Self {
                    use bellman_ce::pairing::ff::{PrimeField, PrimeFieldRepr};
                    let mut res: Vec<u8> = vec![];
                    e.into_repr().write_le(&mut res).unwrap();
                    Self::from_byte_vector(res)
                }

                fn into_bellman(self) -> <Self::BellmanEngine as ScalarEngine>::Fr {
                    use bellman_ce::pairing::ff::{PrimeField, PrimeFieldRepr};
                    let bytes = self.to_byte_vector();
                    let mut repr =
                        <<Self::BellmanEngine as ScalarEngine>::Fr as PrimeField>::Repr::default();
                    repr.read_le(bytes.as_slice()).unwrap();
                    <Self::BellmanEngine as ScalarEngine>::Fr::from_repr(repr).unwrap()
                }

                fn new_fq2(
                    c0: &str,
                    c1: &str,
                ) -> <Self::BellmanEngine as bellman_ce::pairing::Engine>::Fqe {
                    $fq2_type {
                        c0: bellman_ce::pairing::from_hex(c0).unwrap(),
                        c1: bellman_ce::pairing::from_hex(c1).unwrap(),
                    }
                }
            }
        };
    }

    #[cfg(feature = "bellperson")]
    macro_rules! bellperson_extensions {
        ($bellperson_type:ty) => {
            use crate::BellpersonFieldExtensions;

            impl BellpersonFieldExtensions for FieldPrime {
                type BellpersonField = $bellperson_type;

                fn from_bellperson(e: Self::BellpersonField) -> Self {
                    use ff::PrimeField;
                    let res = e.to_repr().to_vec();
                    Self::from_byte_vector(res)
                }

                fn into_bellperson(self) -> Self::BellpersonField {
                    use ff::PrimeField;
                    let bytes = self.to_byte_vector();
                    Self::BellpersonField::from_repr_vartime(bytes.try_into().unwrap()).unwrap()
                }
            }
        };
    }

    macro_rules! ark_extensions {
        ($ark_type:ty) => {
            use crate::ArkFieldExtensions;

            impl ArkFieldExtensions for FieldPrime {
                type ArkEngine = $ark_type;

                fn from_ark(e: <Self::ArkEngine as ark_ec::PairingEngine>::Fr) -> Self {
                    Self { v: e }
                }

                fn into_ark(self) -> <Self::ArkEngine as ark_ec::PairingEngine>::Fr {
                    self.v
                }
            }
        };
    }
}

pub mod bls12_377;
pub mod bls12_381;
pub mod bn128;
pub mod bw6_761;
pub mod dummy_curve;
pub mod pallas;
pub mod vesta;

pub use bls12_377::FieldPrime as Bls12_377Field;
pub use bls12_381::FieldPrime as Bls12_381Field;
pub use bn128::FieldPrime as Bn128Field;
pub use bw6_761::FieldPrime as Bw6_761Field;
pub use dummy_curve::FieldPrime as DummyCurveField;
pub use pallas::FieldPrime as PallasField;
pub use vesta::FieldPrime as VestaField;
