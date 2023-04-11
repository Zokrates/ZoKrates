use crate::{Field, Pow};
use num_bigint::BigUint;
use num_traits::{CheckedDiv, One, Zero};
use serde_derive::{Deserialize, Serialize};
use std::convert::{From, TryFrom};
use std::fmt;
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::{Add, Div, Mul, Sub};

const _PRIME: u8 = 7;

#[derive(
    Default, Debug, Hash, Clone, Copy, PartialOrd, Ord, Serialize, Deserialize, PartialEq, Eq,
)]
pub struct FieldPrime {
    v: u8,
}

impl fmt::Display for FieldPrime {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.v)
    }
}

impl From<u128> for FieldPrime {
    fn from(_: u128) -> Self {
        unimplemented!()
    }
}

impl From<u64> for FieldPrime {
    fn from(_: u64) -> Self {
        unimplemented!()
    }
}

impl From<u32> for FieldPrime {
    fn from(_: u32) -> Self {
        unimplemented!()
    }
}

impl From<u16> for FieldPrime {
    fn from(_: u16) -> Self {
        unimplemented!()
    }
}

impl From<u8> for FieldPrime {
    fn from(num: u8) -> Self {
        FieldPrime { v: num }
    }
}

impl From<usize> for FieldPrime {
    fn from(_: usize) -> Self {
        unimplemented!()
    }
}

impl From<bool> for FieldPrime {
    fn from(_: bool) -> Self {
        unimplemented!()
    }
}

impl From<i32> for FieldPrime {
    fn from(num: i32) -> Self {
        assert!(num < _PRIME as i32);
        assert!(num >= 0);
        Self::from(num as u8)
    }
}

impl TryFrom<BigUint> for FieldPrime {
    type Error = ();

    fn try_from(_: BigUint) -> Result<Self, ()> {
        unimplemented!()
    }
}

impl Zero for FieldPrime {
    fn zero() -> FieldPrime {
        FieldPrime { v: 0 }
    }
    fn is_zero(&self) -> bool {
        self.v.is_zero()
    }
}

impl One for FieldPrime {
    fn one() -> FieldPrime {
        FieldPrime { v: 1 }
    }
}

impl Add<FieldPrime> for FieldPrime {
    type Output = FieldPrime;

    fn add(self, _: FieldPrime) -> FieldPrime {
        unimplemented!()
    }
}

impl<'a> Add<&'a FieldPrime> for FieldPrime {
    type Output = FieldPrime;

    fn add(self, _: &FieldPrime) -> FieldPrime {
        unimplemented!()
    }
}

impl Sub<FieldPrime> for FieldPrime {
    type Output = FieldPrime;

    fn sub(self, _: FieldPrime) -> FieldPrime {
        unimplemented!()
    }
}

impl<'a> Sub<&'a FieldPrime> for FieldPrime {
    type Output = FieldPrime;

    fn sub(self, _: &FieldPrime) -> FieldPrime {
        unimplemented!()
    }
}

impl Mul<FieldPrime> for FieldPrime {
    type Output = FieldPrime;

    fn mul(self, _: FieldPrime) -> FieldPrime {
        unimplemented!()
    }
}

impl<'a> Mul<&'a FieldPrime> for FieldPrime {
    type Output = FieldPrime;

    fn mul(self, _: &FieldPrime) -> FieldPrime {
        unimplemented!()
    }
}

impl CheckedDiv for FieldPrime {
    fn checked_div(&self, _: &FieldPrime) -> Option<FieldPrime> {
        unimplemented!()
    }
}

impl Div<FieldPrime> for FieldPrime {
    type Output = FieldPrime;

    fn div(self, _: FieldPrime) -> FieldPrime {
        unimplemented!()
    }
}

impl<'a> Div<&'a FieldPrime> for FieldPrime {
    type Output = FieldPrime;

    fn div(self, _: &FieldPrime) -> FieldPrime {
        unimplemented!()
    }
}

impl Pow<usize> for FieldPrime {
    type Output = FieldPrime;

    fn pow(self, _: usize) -> FieldPrime {
        unimplemented!()
    }
}

impl num_traits::CheckedAdd for FieldPrime {
    fn checked_add(&self, _: &Self) -> Option<Self> {
        unimplemented!()
    }
}

impl num_traits::CheckedMul for FieldPrime {
    fn checked_mul(&self, _: &Self) -> Option<Self> {
        unimplemented!()
    }
}

impl Field for FieldPrime {
    const G2_TYPE: crate::G2Type = crate::G2Type::Fq2;

    fn to_byte_vector(&self) -> Vec<u8> {
        unimplemented!()
    }

    fn from_byte_vector(_: Vec<u8>) -> Self {
        unimplemented!()
    }

    fn to_dec_string(&self) -> String {
        unimplemented!()
    }

    fn inverse_mul(&self) -> Option<Self> {
        unimplemented!()
    }

    fn min_value() -> Self {
        unimplemented!()
    }

    fn max_value() -> Self {
        unimplemented!()
    }

    fn max_unique_value() -> Self {
        unimplemented!()
    }

    fn to_bits_be(&self) -> Vec<bool> {
        unimplemented!()
    }

    fn get_required_bits() -> usize {
        3 // ceil(log2(7))
    }

    fn try_from_dec_str(_: &str) -> Result<Self, crate::FieldParseError> {
        unimplemented!()
    }

    fn try_from_str(_: &str, _: u32) -> Result<Self, crate::FieldParseError> {
        unimplemented!()
    }

    fn to_compact_dec_string(&self) -> String {
        unimplemented!()
    }

    fn id() -> [u8; 4] {
        unimplemented!()
    }

    fn name() -> &'static str {
        unimplemented!()
    }

    fn bits(&self) -> u32 {
        unimplemented!()
    }

    fn to_biguint(&self) -> num_bigint::BigUint {
        unimplemented!()
    }

    fn read<R: std::io::Read>(_: R) -> std::io::Result<Self> {
        unimplemented!()
    }

    fn write<W: std::io::Write>(&self, _: W) -> std::io::Result<()> {
        unimplemented!()
    }
}
