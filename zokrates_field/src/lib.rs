//
// @file field.rs
// @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
// @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
// @date 2017

use bellman_ce::pairing::ff::ScalarEngine;
use bellman_ce::pairing::Engine;
use num_bigint::BigUint;
use num_traits::{One, Zero};
use serde::{Deserialize, Serialize};
use std::convert::{From, TryFrom};
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::ops::{Add, Div, Mul, Sub};

pub trait Pow<RHS> {
    type Output;
    fn pow(self, _: RHS) -> Self::Output;
}

pub trait Field:
    From<i32>
    + From<u32>
    + From<usize>
    + From<u128>
    + TryFrom<BigUint, Error = ()>
    + Zero
    + One
    + Clone
    + PartialEq
    + Eq
    + Hash
    + PartialOrd
    + Ord
    + Display
    + Debug
    + Add<Self, Output = Self>
    + for<'a> Add<&'a Self, Output = Self>
    + Sub<Self, Output = Self>
    + for<'a> Sub<&'a Self, Output = Self>
    + Mul<Self, Output = Self>
    + for<'a> Mul<&'a Self, Output = Self>
    + Div<Self, Output = Self>
    + for<'a> Div<&'a Self, Output = Self>
    + Pow<usize, Output = Self>
    + Pow<Self, Output = Self>
    + for<'a> Pow<&'a Self, Output = Self>
    + for<'a> Deserialize<'a>
    + Serialize
    + num_traits::CheckedAdd
    + num_traits::CheckedMul
{
    /// An associated type to be able to operate with Bellman ff traits
    type BellmanEngine: Engine;

    fn from_bellman(e: <Self::BellmanEngine as ScalarEngine>::Fr) -> Self {
        use bellman_ce::pairing::ff::{PrimeField, PrimeFieldRepr};
        let mut res: Vec<u8> = vec![];
        e.into_repr().write_le(&mut res).unwrap();
        Self::from_byte_vector(res)
    }

    fn into_bellman(self) -> <Self::BellmanEngine as ScalarEngine>::Fr {
        use bellman_ce::pairing::ff::PrimeField;
        let s = self.to_dec_string();
        <Self::BellmanEngine as ScalarEngine>::Fr::from_str(&s).unwrap()
    }

    fn new_fq2(c0: &str, c1: &str) -> <Self::BellmanEngine as Engine>::Fqe;

    /// Returns this `Field`'s contents as little-endian byte vector
    fn into_byte_vector(&self) -> Vec<u8>;
    /// Returns an element of this `Field` from a little-endian byte vector
    fn from_byte_vector(_: Vec<u8>) -> Self;
    /// Returns this `Field`'s contents as decimal string
    fn to_dec_string(&self) -> String;
    /// Returns the multiplicative inverse, i.e.: self * self.inverse_mul() = Self::one()
    fn inverse_mul(&self) -> Self;
    /// Returns the smallest value that can be represented by this field type.
    fn min_value() -> Self;
    /// Returns the largest value that can be represented by this field type.
    fn max_value() -> Self;
    /// Returns the largest value `m` such that there exist a number of bits `n` so that any value smaller or equal to
    /// m` has a single `n`-bit decomposition
    fn max_unique_value() -> Self;
    /// Returns the number of bits required to represent any element of this field type.
    fn get_required_bits() -> usize;
    /// Tries to parse a string into this representation
    fn try_from_dec_str<'a>(s: &'a str) -> Result<Self, ()>;
    fn try_from_str(s: &str, radix: u32) -> Result<Self, ()>;
    /// Returns a decimal string representing a the member of the equivalence class of this `Field` in Z/pZ
    /// which lies in [-(p-1)/2, (p-1)/2]
    fn to_compact_dec_string(&self) -> String;
    /// Returns the size of the field as a decimal string
    fn id() -> [u8; 4];
    /// the name of the curve associated with this field
    fn name() -> &'static str;
    /// Gets the number of bits
    fn bits(&self) -> u32;
    /// Returns this `Field`'s largest value as a big-endian bit vector
    fn max_value_bit_vector_be() -> Vec<bool> {
        fn bytes_to_bits(bytes: &[u8]) -> Vec<bool> {
            bytes
                .iter()
                .flat_map(|&v| (0..8).rev().map(move |i| (v >> i) & 1 == 1))
                .collect()
        }

        let field_bytes_le = Self::into_byte_vector(&Self::max_value());
        // reverse for big-endianess
        let field_bytes_be = field_bytes_le.into_iter().rev().collect::<Vec<u8>>();
        let field_bits_be = bytes_to_bits(&field_bytes_be);

        let field_bits_be = &field_bits_be[field_bits_be.len() - Self::get_required_bits()..];
        field_bits_be.to_vec()
    }
    /// Returns the value as a BigUint
    fn to_biguint(&self) -> BigUint;
}

#[macro_use]
mod prime_field {
    macro_rules! prime_field {
        ($modulus:expr, $bellman_type:ty, $fq2_type: ident, $name:expr) => {
            use crate::{Field, Pow};
            use lazy_static::lazy_static;
            use num_bigint::{BigInt, BigUint, Sign, ToBigInt};
            use num_integer::Integer;
            use num_traits::{One, Zero};
            use serde_derive::{Deserialize, Serialize};
            use std::convert::From;
            use std::convert::TryFrom;
            use std::fmt;
            use std::fmt::{Debug, Display};
            use std::ops::{Add, Div, Mul, Sub};

            lazy_static! {
                static ref P: BigInt = BigInt::parse_bytes($modulus, 10).unwrap();
            }

            #[derive(PartialEq, PartialOrd, Clone, Eq, Ord, Hash, Serialize, Deserialize)]
            pub struct FieldPrime {
                value: BigInt,
            }

            impl Field for FieldPrime {
                type BellmanEngine = $bellman_type;

                fn bits(&self) -> u32 {
                    self.value.bits() as u32
                }

                fn new_fq2(c0: &str, c1: &str) -> $fq2_type {
                    $fq2_type {
                        c0: bellman_ce::pairing::from_hex(c0).unwrap(),
                        c1: bellman_ce::pairing::from_hex(c1).unwrap(),
                    }
                }

                fn to_biguint(&self) -> BigUint {
                    self.value.to_biguint().unwrap()
                }

                fn into_byte_vector(&self) -> Vec<u8> {
                    match self.value.to_biguint() {
                        Option::Some(val) => val.to_bytes_le(),
                        Option::None => panic!("Should never happen."),
                    }
                }

                fn from_byte_vector(bytes: Vec<u8>) -> Self {
                    let uval = BigUint::from_bytes_le(bytes.as_slice());
                    FieldPrime {
                        value: BigInt::from_biguint(Sign::Plus, uval),
                    }
                }

                fn to_dec_string(&self) -> String {
                    self.value.to_str_radix(10)
                }

                fn inverse_mul(&self) -> FieldPrime {
                    let (b, s, _) = extended_euclid(&self.value, &*P);
                    assert_eq!(b, BigInt::one());
                    FieldPrime {
                        value: &s - s.div_floor(&*P) * &*P,
                    }
                }
                fn min_value() -> FieldPrime {
                    FieldPrime {
                        value: ToBigInt::to_bigint(&0).unwrap(),
                    }
                }
                fn max_value() -> FieldPrime {
                    FieldPrime {
                        value: &*P - ToBigInt::to_bigint(&1).unwrap(),
                    }
                }
                fn max_unique_value() -> FieldPrime {
                    use num_traits::Pow;

                    FieldPrime {
                        value: BigInt::from(2u32).pow(Self::get_required_bits() - 1) - 1,
                    }
                }
                fn get_required_bits() -> usize {
                    (*P).bits()
                }
                fn try_from_dec_str<'a>(s: &'a str) -> Result<Self, ()> {
                    Self::try_from_str(s, 10)
                }
                fn try_from_str(s: &str, radix: u32) -> Result<Self, ()> {
                    let x = BigInt::parse_bytes(s.as_bytes(), radix).ok_or(())?;
                    Ok(FieldPrime {
                        value: &x - x.div_floor(&*P) * &*P,
                    })
                }
                fn to_compact_dec_string(&self) -> String {
                    // values up to (p-1)/2 included are represented as positive, values between (p+1)/2 and p-1 as represented as negative by subtracting p
                    if self.value <= FieldPrime::max_value().value / 2 {
                        format!("{}", self.value.to_str_radix(10))
                    } else {
                        format!(
                            "({})",
                            (&self.value - (FieldPrime::max_value().value + BigInt::one()))
                                .to_str_radix(10)
                        )
                    }
                }
                fn id() -> [u8; 4] {
                    let mut res = [0u8; 4];
                    use sha2::{Digest, Sha256};
                    let hash = Sha256::digest(&P.to_bytes_le().1);
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
                    FieldPrime {
                        value: BigInt::default(),
                    }
                }
            }

            impl Display for FieldPrime {
                fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                    write!(f, "{}", self.value.to_str_radix(10))
                }
            }

            impl Debug for FieldPrime {
                fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                    write!(f, "{}", self.value.to_str_radix(10))
                }
            }

            impl From<i32> for FieldPrime {
                fn from(num: i32) -> Self {
                    let x = ToBigInt::to_bigint(&num).unwrap();
                    FieldPrime {
                        value: &x - x.div_floor(&*P) * &*P,
                    }
                }
            }

            impl From<u32> for FieldPrime {
                fn from(num: u32) -> Self {
                    let x = ToBigInt::to_bigint(&num).unwrap();
                    FieldPrime {
                        value: &x - x.div_floor(&*P) * &*P,
                    }
                }
            }

            impl From<usize> for FieldPrime {
                fn from(num: usize) -> Self {
                    let x = ToBigInt::to_bigint(&num).unwrap();
                    FieldPrime {
                        value: &x - x.div_floor(&*P) * &*P,
                    }
                }
            }

            impl From<u128> for FieldPrime {
                fn from(num: u128) -> Self {
                    let x = ToBigInt::to_bigint(&num).unwrap();
                    FieldPrime {
                        value: &x - x.div_floor(&*P) * &*P,
                    }
                }
            }

            impl TryFrom<BigUint> for FieldPrime {
                type Error = ();

                fn try_from(value: BigUint) -> Result<Self, ()> {
                    match value <= Self::max_value().to_biguint() {
                        true => {
                            let x = ToBigInt::to_bigint(&value).unwrap();
                            Ok(FieldPrime { value: x })
                        }
                        false => Err(()),
                    }
                }
            }

            impl Zero for FieldPrime {
                fn zero() -> FieldPrime {
                    FieldPrime {
                        value: ToBigInt::to_bigint(&0).unwrap(),
                    }
                }
                fn is_zero(&self) -> bool {
                    self.value == ToBigInt::to_bigint(&0).unwrap()
                }
            }

            impl One for FieldPrime {
                fn one() -> FieldPrime {
                    FieldPrime {
                        value: ToBigInt::to_bigint(&1).unwrap(),
                    }
                }
            }

            impl Add<FieldPrime> for FieldPrime {
                type Output = FieldPrime;

                fn add(self, other: FieldPrime) -> FieldPrime {
                    FieldPrime {
                        value: (self.value + other.value) % &*P,
                    }
                }
            }

            impl<'a> Add<&'a FieldPrime> for FieldPrime {
                type Output = FieldPrime;

                fn add(self, other: &FieldPrime) -> FieldPrime {
                    FieldPrime {
                        value: (self.value + other.value.clone()) % &*P,
                    }
                }
            }

            impl Sub<FieldPrime> for FieldPrime {
                type Output = FieldPrime;

                fn sub(self, other: FieldPrime) -> FieldPrime {
                    let x = self.value - other.value;
                    FieldPrime {
                        value: &x - x.div_floor(&*P) * &*P,
                    }
                }
            }

            impl<'a> Sub<&'a FieldPrime> for FieldPrime {
                type Output = FieldPrime;

                fn sub(self, other: &FieldPrime) -> FieldPrime {
                    let x = self.value - other.value.clone();
                    FieldPrime {
                        value: &x - x.div_floor(&*P) * &*P,
                    }
                }
            }

            impl Mul<FieldPrime> for FieldPrime {
                type Output = FieldPrime;

                fn mul(self, other: FieldPrime) -> FieldPrime {
                    FieldPrime {
                        value: (self.value * other.value) % &*P,
                    }
                }
            }

            impl<'a> Mul<&'a FieldPrime> for FieldPrime {
                type Output = FieldPrime;

                fn mul(self, other: &FieldPrime) -> FieldPrime {
                    FieldPrime {
                        value: (self.value * other.value.clone()) % &*P,
                    }
                }
            }

            impl Div<FieldPrime> for FieldPrime {
                type Output = FieldPrime;

                fn div(self, other: FieldPrime) -> FieldPrime {
                    self * other.inverse_mul()
                }
            }

            impl<'a> Div<&'a FieldPrime> for FieldPrime {
                type Output = FieldPrime;

                fn div(self, other: &FieldPrime) -> FieldPrime {
                    self / other.clone()
                }
            }

            impl Pow<usize> for FieldPrime {
                type Output = FieldPrime;

                fn pow(self, exp: usize) -> FieldPrime {
                    let mut res = FieldPrime::from(1);
                    for _ in 0..exp {
                        res = res * &self;
                    }
                    res
                }
            }

            impl Pow<FieldPrime> for FieldPrime {
                type Output = FieldPrime;

                fn pow(self, exp: FieldPrime) -> FieldPrime {
                    let mut res = FieldPrime::one();
                    let mut current = FieldPrime::zero();
                    loop {
                        if current >= exp {
                            return res;
                        }
                        res = res * &self;
                        current = current + FieldPrime::one();
                    }
                }
            }

            impl<'a> Pow<&'a FieldPrime> for FieldPrime {
                type Output = FieldPrime;

                fn pow(self, exp: &'a FieldPrime) -> FieldPrime {
                    let mut res = FieldPrime::one();
                    let mut current = FieldPrime::zero();
                    loop {
                        if &current >= exp {
                            return res;
                        }
                        res = res * &self;
                        current = current + FieldPrime::one();
                    }
                }
            }

            impl num_traits::CheckedAdd for FieldPrime {
                fn checked_add(&self, other: &Self) -> Option<Self> {
                    let bound = Self::max_unique_value();

                    assert!(self <= &bound);
                    assert!(other <= &bound);

                    let big_res = self.value.clone() + other.value.clone();

                    if big_res > bound.value {
                        None
                    } else {
                        Some(FieldPrime { value: big_res })
                    }
                }
            }

            impl num_traits::CheckedMul for FieldPrime {
                fn checked_mul(&self, other: &Self) -> Option<Self> {
                    let bound = Self::max_unique_value();

                    assert!(self <= &bound);
                    assert!(other <= &bound);

                    let big_res = self.value.clone() * other.value.clone();

                    // we only go up to 2**(bitwidth - 1) because after that we lose uniqueness of bit decomposition
                    if big_res > bound.value {
                        None
                    } else {
                        Some(FieldPrime { value: big_res })
                    }
                }
            }

            /// Calculates the gcd using an iterative implementation of the extended euclidian algorithm.
            /// Returning `(d, s, t)` so that `d = s * a + t * b`
            ///
            /// # Arguments
            /// * `a` - First number as `BigInt`
            /// * `b` - Second number as `BigInt`
            fn extended_euclid(a: &BigInt, b: &BigInt) -> (BigInt, BigInt, BigInt) {
                let (mut s, mut old_s) = (BigInt::zero(), BigInt::one());
                let (mut t, mut old_t) = (BigInt::one(), BigInt::zero());
                let (mut r, mut old_r) = (b.clone(), a.clone());
                while !&r.is_zero() {
                    let quotient = &old_r / &r;
                    let tmp_r = old_r.clone();
                    old_r = r.clone();
                    r = &tmp_r - &quotient * &r;
                    let tmp_s = old_s.clone();
                    old_s = s.clone();
                    s = &tmp_s - &quotient * &s;
                    let tmp_t = old_t.clone();
                    old_t = t.clone();
                    t = &tmp_t - &quotient * &t;
                }
                return (old_r, old_s, old_t);
            }
        };
    }
}

pub mod bls12_381;
pub mod bn128;

pub use bls12_381::FieldPrime as Bls12Field;
pub use bn128::FieldPrime as Bn128Field;
