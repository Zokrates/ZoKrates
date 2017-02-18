//
// @file field.rs
// @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
// @date 2017

extern crate num;

use self::num::{Integer, Zero, One};
use self::num::bigint::{BigInt, ToBigInt};
use std::convert::From;
use std::ops::{Add, Sub, Mul, Div};
use std::fmt;
use std::fmt::{Display, Debug};

lazy_static! {
    static ref P: BigInt = BigInt::parse_bytes(b"21888242871839275222246405745257275088696311157297823662689037894645226208583", 10).unwrap();
}

pub trait Pow<RHS> {
    type Output;
    fn pow(self, RHS) -> Self::Output;
}

pub trait Field : From<i32> + From<u32> + for<'a> From<&'a str>
                + Zero + One + Clone + PartialEq + PartialOrd + Display + Debug
                + Add<Self, Output=Self> + for<'a> Add<&'a Self, Output=Self>
                + Sub<Self, Output=Self> + for<'a> Sub<&'a Self, Output=Self>
                + Mul<Self, Output=Self> + for<'a> Mul<&'a Self, Output=Self>
                + Div<Self, Output=Self> + for<'a> Div<&'a Self, Output=Self>
                + Pow<Self, Output=Self> + Pow<u32, Output=Self>
{
    /// Returns the smallest value that can be represented by this field type.
    fn min_value() -> Self;
    /// Returns the largest value that can be represented by this field type.
    fn max_value() -> Self;
    // Raises self to the power of exp.
    // fn pow<T>(self, exp: T) -> Self;
}

#[derive(PartialEq,PartialOrd,Clone)]
pub struct FieldPrime {
    value: BigInt,
}

impl Field for FieldPrime {
    fn min_value() -> FieldPrime {
        FieldPrime { value: ToBigInt::to_bigint(&0).unwrap() }
    }
    fn max_value() -> FieldPrime {
        FieldPrime { value: &*P - ToBigInt::to_bigint(&1).unwrap() }
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

impl Iterator for FieldPrime {
    type Item = FieldPrime;

    fn next(&mut self) -> Option<FieldPrime> {
        Some(self.clone() + FieldPrime::from(1))
    }
}

impl From<i32> for FieldPrime {
    fn from(num: i32) -> Self {
        let x = ToBigInt::to_bigint(&num).unwrap();
        FieldPrime { value: &x - x.div_floor(&*P) * &*P }
    }
}

impl From<u32> for FieldPrime {
    fn from(num: u32) -> Self {
        let x = ToBigInt::to_bigint(&num).unwrap();
        FieldPrime { value: &x - x.div_floor(&*P) * &*P }
    }
}

impl<'a> From<&'a str> for FieldPrime {
    fn from(s: &'a str) -> Self {
        let x = BigInt::parse_bytes(s.as_bytes(), 10).unwrap();
        FieldPrime { value: &x - x.div_floor(&*P) * &*P }
    }
}

impl Zero for FieldPrime {
    fn zero() -> FieldPrime {
        FieldPrime { value: ToBigInt::to_bigint(&0).unwrap() }
    }
    fn is_zero(&self) -> bool {
        self.value == ToBigInt::to_bigint(&0).unwrap()
    }
}

impl One for FieldPrime {
    fn one() -> FieldPrime {
        FieldPrime { value: ToBigInt::to_bigint(&1).unwrap() }
    }
}

impl Add<FieldPrime> for FieldPrime {
    type Output = FieldPrime;

    fn add(self, other: FieldPrime) -> FieldPrime {
        FieldPrime { value: (self.value + other.value) % &*P }
    }
}

impl<'a> Add<&'a FieldPrime> for FieldPrime {
    type Output = FieldPrime;

    fn add(self, other: &FieldPrime) -> FieldPrime {
        FieldPrime { value: (self.value + other.value.clone()) % &*P }
    }
}

// impl<'a> Add<&'a mut FieldPrime> for FieldPrime {
//     type Output = FieldPrime;
//
//     fn add(self, other: &mut FieldPrime) -> FieldPrime {
//         FieldPrime { value: (self.value + other.value.clone()) % &*P }
//     }
// }

impl Sub<FieldPrime> for FieldPrime {
    type Output = FieldPrime;

    fn sub(self, other: FieldPrime) -> FieldPrime {
        let x = self.value - other.value;
        FieldPrime { value: &x - x.div_floor(&*P) * &*P }
    }
}

impl<'a> Sub<&'a FieldPrime> for FieldPrime {
    type Output = FieldPrime;

    fn sub(self, other: &FieldPrime) -> FieldPrime {
        let x = self.value - other.value.clone();
        FieldPrime { value: &x - x.div_floor(&*P) * &*P }
    }
}

impl Mul<FieldPrime> for FieldPrime {
    type Output = FieldPrime;

    fn mul(self, other: FieldPrime) -> FieldPrime {
        FieldPrime { value: (self.value * other.value) % &*P }
    }
}

impl<'a> Mul<&'a FieldPrime> for FieldPrime {
    type Output = FieldPrime;

    fn mul(self, other: &FieldPrime) -> FieldPrime {
        FieldPrime { value: (self.value * other.value.clone()) % &*P }
    }
}

impl Div<FieldPrime> for FieldPrime {
    type Output = FieldPrime;

    fn div(self, other: FieldPrime) -> FieldPrime {
        FieldPrime { value: (self.value / other.value) % &*P }
    }
}

impl<'a> Div<&'a FieldPrime> for FieldPrime {
    type Output = FieldPrime;

    fn div(self, other: &FieldPrime) -> FieldPrime {
        FieldPrime { value: (self.value / other.value.clone()) % &*P }
    }
}

impl Pow<u32> for FieldPrime {
    type Output = FieldPrime;

    fn pow(self, exp: u32) -> FieldPrime {
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
            res = res * &self;
            if current >= exp {
                return res;
            }
            current = current + FieldPrime::one();
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(test)]
    mod field_prime {
        use super::*;

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
                "21888242871839275222246405745257275088696311157297823662689037894645160860360".parse::<BigInt>().unwrap(),
                (FieldPrime::from("68135") - FieldPrime::from("65416358")).value
            );
            assert_eq!(
                "21888242871839275222246405745257275088696311157297823662689037894645160860360".parse::<BigInt>().unwrap(),
                (FieldPrime::from("68135") - &FieldPrime::from("65416358")).value
            );
        }
    }

    #[test]
    fn bigint_assertions() {
        let x = BigInt::parse_bytes(b"65", 10).unwrap();
        assert_eq!(&x + &x, BigInt::parse_bytes(b"130", 10).unwrap());
        assert_eq!("1".parse::<BigInt>().unwrap(), "3".parse::<BigInt>().unwrap().div_floor(&"2".parse::<BigInt>().unwrap()));
        assert_eq!("-2".parse::<BigInt>().unwrap(), "-3".parse::<BigInt>().unwrap().div_floor(&"2".parse::<BigInt>().unwrap()));
    }
}
