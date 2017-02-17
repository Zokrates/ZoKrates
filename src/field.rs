//
// @file field.rs
// @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
// @date 2017

extern crate num;

use self::num::Integer;
use self::num::bigint::{BigInt, ToBigInt};
use std::convert::From;
use std::ops::{Add, Sub, Mul, Div};

lazy_static! {
    static ref P: BigInt = BigInt::parse_bytes(b"21888242871839275222246405745257275088696311157297823662689037894645226208583", 10).unwrap();
}

trait Field : for<'a> From<&'a str>
            + Add<Self> + for<'a> Add<&'a Self>
            + Sub<Self> + for<'a> Sub<&'a Self>
            + Mul<Self> + for<'a> Mul<&'a Self>
            + Div<Self> + for<'a> Div<&'a Self>
{
    /// Returns the smallest value that can be represented by this field type.
    fn min_value() -> Self;
    /// Returns the largest value that can be represented by this field type.
    fn max_value() -> Self;
}

#[derive(Debug)]
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

impl<'a> From<&'a str> for FieldPrime {
    fn from(s: &'a str) -> Self {
        let x = BigInt::parse_bytes(s.as_bytes(), 10).unwrap();
        FieldPrime { value: &x - x.div_floor(&*P) * &*P }
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
