extern crate ff;
extern crate pairing;

use crate::field::{Field, FieldPrime};
use ff::{PrimeField, PrimeFieldRepr};
use pairing::bn256::Fr;

impl From<FieldPrime> for Fr {
    fn from(e: FieldPrime) -> Fr {
        let s = e.to_dec_string();
        Fr::from_str(&s).unwrap()
    }
}

impl From<Fr> for FieldPrime {
    fn from(e: Fr) -> FieldPrime {
        let mut res: Vec<u8> = vec![];
        e.into_repr().write_le(&mut res).unwrap();
        FieldPrime::from_byte_vector(res)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ff::Field;

    extern crate rand;
    use rand::{thread_rng, Rng};

    #[test]
    fn fr_to_field_to_fr() {
        let rng = &mut thread_rng();
        let a: Fr = rng.gen();

        assert_eq!(Fr::from(FieldPrime::from(a)), a);
    }

    #[test]
    fn field_to_fr_to_field() {
        // use Fr to get a random element
        let rng = &mut thread_rng();
        let a: Fr = rng.gen();

        // now test idempotence
        let a = FieldPrime::from(a);

        assert_eq!(FieldPrime::from(Fr::from(a.clone())), a);
    }

    #[test]
    fn one() {
        let a = FieldPrime::from(1);

        assert_eq!(Fr::from(a), Fr::one());
    }

    #[test]
    fn zero() {
        let a = FieldPrime::from(0);

        assert_eq!(Fr::from(a), Fr::zero());
    }

    #[test]
    fn minus_one() {
        let mut a: Fr = Fr::one();
        a.negate();
        assert_eq!(FieldPrime::from(a), FieldPrime::from(-1));
    }

    #[test]
    fn add() {
        let rng = &mut thread_rng();

        let mut a: Fr = rng.gen();
        let b: Fr = rng.gen();

        let aa = FieldPrime::from(a);
        let bb = FieldPrime::from(b);
        let cc = aa + bb;

        a.add_assign(&b);

        assert_eq!(FieldPrime::from(a), cc);
    }
}
