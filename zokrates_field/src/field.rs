//
// @file field.rs
// @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
// @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
// @date 2017

use lazy_static::lazy_static;
use num_bigint::{BigInt, BigUint, Sign, ToBigInt};
use num_integer::Integer;
use num_traits::{One, Zero};
use pairing::bn256::Bn256;
use pairing::ff::ScalarEngine;
use pairing::Engine;
use serde_derive::{Deserialize, Serialize};
use std::convert::From;
use std::fmt;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::ops::{Add, Div, Mul, Sub};

#[cfg(not(feature = "curve25519"))]
lazy_static! {
    static ref P: BigInt = BigInt::parse_bytes(
        b"21888242871839275222246405745257275088548364400416034343698204186575808495617", // BN128 order.
        10
    )
    .unwrap();
}

#[cfg(feature = "curve25519")]
lazy_static! {
    static ref P: BigInt = BigInt::parse_bytes(
        b"7237005577332262213973186563042994240857116359379907606001950938285454250989", // Curve25519 order.
        10
    )
    .unwrap();
}

pub trait Pow<RHS> {
    type Output;
    fn pow(self, _: RHS) -> Self::Output;
}

pub trait Field:
    From<i32>
    + From<u32>
    + From<usize>
    + Zero
    + One
    + Clone
    + PartialEq
    + Eq
    + Hash
    + PartialOrd
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
{
    /// An associated type to be able to operate with Bellman ff traits
    type BellmanEngine: Engine;

    fn from_bellman(e: <Self::BellmanEngine as ScalarEngine>::Fr) -> Self {
        use ff::{PrimeField, PrimeFieldRepr};
        let mut res: Vec<u8> = vec![];
        e.into_repr().write_le(&mut res).unwrap();
        Self::from_byte_vector(res)
    }

    fn into_bellman(self) -> <Self::BellmanEngine as ScalarEngine>::Fr {
        use ff::PrimeField;
        let s = self.to_dec_string();
        <Self::BellmanEngine as ScalarEngine>::Fr::from_str(&s).unwrap()
    }

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
    /// Returns the number of required bits to represent this field type.
    fn get_required_bits() -> usize;
    /// Tries to parse a string into this representation
    fn try_from_dec_str<'a>(s: &'a str) -> Result<Self, ()>;
    /// Returns a decimal string representing a the member of the equivalence class of this `Field` in Z/pZ
    /// which lies in [-(p-1)/2, (p-1)/2]
    fn to_compact_dec_string(&self) -> String;
}

#[derive(PartialEq, PartialOrd, Clone, Eq, Ord, Hash, Serialize, Deserialize)]
pub struct FieldPrime {
    value: BigInt,
}

impl Field for FieldPrime {
    type BellmanEngine = Bn256;

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
    fn get_required_bits() -> usize {
        (*P).bits()
    }
    fn try_from_dec_str<'a>(s: &'a str) -> Result<Self, ()> {
        let x = BigInt::parse_bytes(s.as_bytes(), 10).ok_or(())?;
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
                (&self.value - (FieldPrime::max_value().value + BigInt::one())).to_str_radix(10)
            )
        }
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

#[cfg(test)]
mod tests {
    use super::*;

    impl<'a> From<&'a str> for FieldPrime {
        fn from(s: &'a str) -> FieldPrime {
            FieldPrime::try_from_dec_str(s).unwrap()
        }
    }

    #[cfg(test)]
    mod field_prime {
        use super::*;
        use bincode::{deserialize, serialize, Infinite};

        #[test]
        fn positive_number() {
            assert_eq!(
                "1234245612".parse::<BigInt>().unwrap(),
                FieldPrime::from("1234245612").value
            );
        }

        #[test]
        fn negative_number() {
            assert_eq!(
                P.checked_sub(&"12".parse::<BigInt>().unwrap()).unwrap(),
                FieldPrime::from("-12").value
            );
        }

        #[test]
        fn addition() {
            assert_eq!(
                "65484493".parse::<BigInt>().unwrap(),
                (FieldPrime::from("65416358") + FieldPrime::from("68135")).value
            );
            assert_eq!(
                "65484493".parse::<BigInt>().unwrap(),
                (FieldPrime::from("65416358") + &FieldPrime::from("68135")).value
            );
        }

        #[test]
        fn addition_negative_small() {
            assert_eq!(
                "3".parse::<BigInt>().unwrap(),
                (FieldPrime::from("5") + FieldPrime::from("-2")).value
            );
            assert_eq!(
                "3".parse::<BigInt>().unwrap(),
                (FieldPrime::from("5") + &FieldPrime::from("-2")).value
            );
        }

        #[test]
        fn addition_negative() {
            assert_eq!(
                "65348223".parse::<BigInt>().unwrap(),
                (FieldPrime::from("65416358") + FieldPrime::from("-68135")).value
            );
            assert_eq!(
                "65348223".parse::<BigInt>().unwrap(),
                (FieldPrime::from("65416358") + &FieldPrime::from("-68135")).value
            );
        }

        #[test]
        fn subtraction() {
            assert_eq!(
                "65348223".parse::<BigInt>().unwrap(),
                (FieldPrime::from("65416358") - FieldPrime::from("68135")).value
            );
            assert_eq!(
                "65348223".parse::<BigInt>().unwrap(),
                (FieldPrime::from("65416358") - &FieldPrime::from("68135")).value
            );
        }

        #[test]
        fn subtraction_negative() {
            assert_eq!(
                "65484493".parse::<BigInt>().unwrap(),
                (FieldPrime::from("65416358") - FieldPrime::from("-68135")).value
            );
            assert_eq!(
                "65484493".parse::<BigInt>().unwrap(),
                (FieldPrime::from("65416358") - &FieldPrime::from("-68135")).value
            );
        }

        #[test]
        fn subtraction_overflow() {
            assert_eq!(
                "21888242871839275222246405745257275088548364400416034343698204186575743147394"
                    .parse::<BigInt>()
                    .unwrap(),
                (FieldPrime::from("68135") - FieldPrime::from("65416358")).value
            );
            assert_eq!(
                "21888242871839275222246405745257275088548364400416034343698204186575743147394"
                    .parse::<BigInt>()
                    .unwrap(),
                (FieldPrime::from("68135") - &FieldPrime::from("65416358")).value
            );
        }

        #[test]
        fn multiplication() {
            assert_eq!(
                "13472".parse::<BigInt>().unwrap(),
                (FieldPrime::from("32") * FieldPrime::from("421")).value
            );
            assert_eq!(
                "13472".parse::<BigInt>().unwrap(),
                (FieldPrime::from("32") * &FieldPrime::from("421")).value
            );
        }

        #[test]
        fn multiplication_negative() {
            assert_eq!(
                "21888242871839275222246405745257275088548364400416034343698204186575808014369"
                    .parse::<BigInt>()
                    .unwrap(),
                (FieldPrime::from("54") * FieldPrime::from("-8912")).value
            );
            assert_eq!(
                "21888242871839275222246405745257275088548364400416034343698204186575808014369"
                    .parse::<BigInt>()
                    .unwrap(),
                (FieldPrime::from("54") * &FieldPrime::from("-8912")).value
            );
        }

        #[test]
        fn multiplication_two_negative() {
            assert_eq!(
                "648".parse::<BigInt>().unwrap(),
                (FieldPrime::from("-54") * FieldPrime::from("-12")).value
            );
            assert_eq!(
                "648".parse::<BigInt>().unwrap(),
                (FieldPrime::from("-54") * &FieldPrime::from("-12")).value
            );
        }

        #[test]
        fn multiplication_overflow() {
            assert_eq!(
                "6042471409729479866150380306128222617399890671095126975526159292198160466142"
                    .parse::<BigInt>()
                    .unwrap(),
                (FieldPrime::from(
                    "21888242871839225222246405785257275088694311157297823662689037894645225727"
                ) * FieldPrime::from("218882428715392752222464057432572755886923"))
                .value
            );
            assert_eq!(
                "6042471409729479866150380306128222617399890671095126975526159292198160466142"
                    .parse::<BigInt>()
                    .unwrap(),
                (FieldPrime::from(
                    "21888242871839225222246405785257275088694311157297823662689037894645225727"
                ) * &FieldPrime::from("218882428715392752222464057432572755886923"))
                    .value
            );
        }

        #[test]
        fn division() {
            assert_eq!(
                FieldPrime::from(4),
                FieldPrime::from(48) / FieldPrime::from(12)
            );
            assert_eq!(
                FieldPrime::from(4),
                FieldPrime::from(48) / &FieldPrime::from(12)
            );
        }

        #[test]
        fn division_negative() {
            let res = FieldPrime::from(-54) / FieldPrime::from(12);
            assert_eq!(FieldPrime::from(-54), FieldPrime::from(12) * res);
        }

        #[test]
        fn division_two_negative() {
            let res = FieldPrime::from(-12) / FieldPrime::from(-85);
            assert_eq!(FieldPrime::from(-12), FieldPrime::from(-85) * res);
        }

        #[test]
        fn pow_small() {
            assert_eq!(
                "8".parse::<BigInt>().unwrap(),
                (FieldPrime::from("2").pow(FieldPrime::from("3"))).value
            );
            assert_eq!(
                "8".parse::<BigInt>().unwrap(),
                (FieldPrime::from("2").pow(&FieldPrime::from("3"))).value
            );
        }

        #[test]
        fn pow_usize() {
            assert_eq!(
                "614787626176508399616".parse::<BigInt>().unwrap(),
                (FieldPrime::from("54").pow(12)).value
            );
        }

        #[test]
        fn pow() {
            assert_eq!(
                "614787626176508399616".parse::<BigInt>().unwrap(),
                (FieldPrime::from("54").pow(FieldPrime::from("12"))).value
            );
            assert_eq!(
                "614787626176508399616".parse::<BigInt>().unwrap(),
                (FieldPrime::from("54").pow(&FieldPrime::from("12"))).value
            );
        }

        #[test]
        fn pow_negative() {
            assert_eq!(
                "21888242871839275222246405745257275088548364400416034343686819230535502784513"
                    .parse::<BigInt>()
                    .unwrap(),
                (FieldPrime::from("-54").pow(FieldPrime::from("11"))).value
            );
            assert_eq!(
                "21888242871839275222246405745257275088548364400416034343686819230535502784513"
                    .parse::<BigInt>()
                    .unwrap(),
                (FieldPrime::from("-54").pow(&FieldPrime::from("11"))).value
            );
        }

        #[test]
        fn serde_ser_deser() {
            let serialized = &serialize(&FieldPrime::from("11"), Infinite).unwrap();
            let deserialized = deserialize(serialized).unwrap();
            assert_eq!(FieldPrime::from("11"), deserialized);
        }

        #[test]
        fn serde_json_ser_deser() {
            let serialized = serde_json::to_string(&FieldPrime::from("11")).unwrap();
            let deserialized = serde_json::from_str(&serialized).unwrap();
            assert_eq!(FieldPrime::from("11"), deserialized);
        }

        #[test]
        fn bytes_ser_deser() {
            let fp = FieldPrime::from("101");
            let bv = fp.into_byte_vector();
            assert_eq!(fp, FieldPrime::from_byte_vector(bv));
        }

        #[test]
        fn dec_string_ser_deser() {
            let fp = FieldPrime::from("101");
            let bv = fp.to_dec_string();
            assert_eq!(fp, FieldPrime::try_from_dec_str(&bv).unwrap());
        }

        #[test]
        fn compact_representation() {
            let one = FieldPrime::from(1);
            assert_eq!("1", &one.to_compact_dec_string());
            let minus_one = FieldPrime::from(0) - one;
            assert_eq!("(-1)", &minus_one.to_compact_dec_string());
            // (p-1)/2 -> positive notation
            let p_minus_one_over_two =
                (FieldPrime::from(0) - FieldPrime::from(1)) / FieldPrime::from(2);
            assert_eq!(
                "10944121435919637611123202872628637544274182200208017171849102093287904247808",
                &p_minus_one_over_two.to_compact_dec_string()
            );
            // (p-1)/2 + 1 -> negative notation (p-1)/2 + 1 - p == (-p+1)/2
            let p_minus_one_over_two_plus_one = ((FieldPrime::from(0) - FieldPrime::from(1))
                / FieldPrime::from(2))
                + FieldPrime::from(1);
            assert_eq!(
                "(-10944121435919637611123202872628637544274182200208017171849102093287904247808)",
                &p_minus_one_over_two_plus_one.to_compact_dec_string()
            );
        }
    }

    #[test]
    fn bigint_assertions() {
        let x = BigInt::parse_bytes(b"65", 10).unwrap();
        assert_eq!(&x + &x, BigInt::parse_bytes(b"130", 10).unwrap());
        assert_eq!(
            "1".parse::<BigInt>().unwrap(),
            "3".parse::<BigInt>()
                .unwrap()
                .div_floor(&"2".parse::<BigInt>().unwrap())
        );
        assert_eq!(
            "-2".parse::<BigInt>().unwrap(),
            "-3".parse::<BigInt>()
                .unwrap()
                .div_floor(&"2".parse::<BigInt>().unwrap())
        );
    }

    #[test]
    fn test_extended_euclid() {
        assert_eq!(
            (
                ToBigInt::to_bigint(&1).unwrap(),
                ToBigInt::to_bigint(&-9).unwrap(),
                ToBigInt::to_bigint(&47).unwrap()
            ),
            extended_euclid(
                &ToBigInt::to_bigint(&120).unwrap(),
                &ToBigInt::to_bigint(&23).unwrap()
            )
        );
        assert_eq!(
            (
                ToBigInt::to_bigint(&2).unwrap(),
                ToBigInt::to_bigint(&2).unwrap(),
                ToBigInt::to_bigint(&-11).unwrap()
            ),
            extended_euclid(
                &ToBigInt::to_bigint(&122).unwrap(),
                &ToBigInt::to_bigint(&22).unwrap()
            )
        );
        assert_eq!(
            (
                ToBigInt::to_bigint(&2).unwrap(),
                ToBigInt::to_bigint(&-9).unwrap(),
                ToBigInt::to_bigint(&47).unwrap()
            ),
            extended_euclid(
                &ToBigInt::to_bigint(&240).unwrap(),
                &ToBigInt::to_bigint(&46).unwrap()
            )
        );
        let (b, s, _) = extended_euclid(&ToBigInt::to_bigint(&253).unwrap(), &*P);
        assert_eq!(b, BigInt::one());
        let s_field = FieldPrime {
            value: &s - s.div_floor(&*P) * &*P,
        };
        assert_eq!(
            FieldPrime::from(
                "12717674712096337777352654721552646000065650461901806515903699665717959876900"
            ),
            s_field
        );
    }

    mod bellman {
        use super::*;

        use ff::Field as FField;

        extern crate rand;
        use pairing::bn256::Fr;
        use rand::{thread_rng, Rng};
        use Field;

        #[test]
        fn fr_to_field_to_fr() {
            let rng = &mut thread_rng();
            for _ in 0..1000 {
                let a: Fr = rng.gen();
                assert_eq!(FieldPrime::from_bellman(a).into_bellman(), a);
            }
        }

        #[test]
        fn field_to_fr_to_field() {
            // use Fr to get a random element
            let rng = &mut thread_rng();
            for _ in 0..1000 {
                let a: Fr = rng.gen();
                // now test idempotence
                let a = FieldPrime::from_bellman(a);
                assert_eq!(FieldPrime::from_bellman(a.clone().into_bellman()), a);
            }
        }

        #[test]
        fn one() {
            let a = FieldPrime::from(1);

            assert_eq!(a.into_bellman(), Fr::one());
        }

        #[test]
        fn zero() {
            let a = FieldPrime::from(0);

            assert_eq!(a.into_bellman(), Fr::zero());
        }

        #[test]
        fn minus_one() {
            let mut a: Fr = Fr::one();
            a.negate();
            assert_eq!(FieldPrime::from_bellman(a), FieldPrime::from(-1));
        }

        #[test]
        fn add() {
            let rng = &mut thread_rng();

            let mut a: Fr = rng.gen();
            let b: Fr = rng.gen();

            let aa = FieldPrime::from_bellman(a);
            let bb = FieldPrime::from_bellman(b);
            let cc = aa + bb;

            a.add_assign(&b);

            assert_eq!(FieldPrime::from_bellman(a), cc);
        }
    }
}
