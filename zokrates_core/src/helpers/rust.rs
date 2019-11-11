use crate::helpers::{Executable, Signed};
use std::fmt;
use zokrates_embed::generate_sha256_round_witness;
use zokrates_field::Field;

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize, Hash, Eq)]
pub enum RustHelper {
    Identity,
    ConditionEq,
    Bits,
    Div,
    Sha256Round,
}

impl fmt::Display for RustHelper {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Signed for RustHelper {
    fn get_signature<T: Field>(&self) -> (usize, usize) {
        match self {
            RustHelper::Identity => (1, 1),
            RustHelper::ConditionEq => (1, 2),
            RustHelper::Bits => (1, T::get_required_bits()),
            RustHelper::Div => (2, 1),
            RustHelper::Sha256Round => (768, 26935),
        }
    }
}

impl<T: Field> Executable<T> for RustHelper {
    fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, String> {
        match self {
            RustHelper::Identity => Ok(inputs.clone()),
            RustHelper::ConditionEq => match inputs[0].is_zero() {
                true => Ok(vec![T::zero(), T::one()]),
                false => Ok(vec![T::one(), T::one() / inputs[0].clone()]),
            },
            RustHelper::Bits => {
                let mut num = inputs[0].clone();
                let mut res = vec![];
                let bits = T::get_required_bits();
                for i in (0..bits).rev() {
                    if T::from(2).pow(i) <= num {
                        num = num - T::from(2).pow(i);
                        res.push(T::one());
                    } else {
                        res.push(T::zero());
                    }
                }
                assert_eq!(num, T::zero());
                Ok(res)
            }
            RustHelper::Div => Ok(vec![inputs[0].clone() / inputs[1].clone()]),
            RustHelper::Sha256Round => {
                let i = &inputs[0..512];
                let h = &inputs[512..];
                let i: Vec<_> = i.iter().map(|x| x.clone().into_bellman()).collect();
                let h: Vec<_> = h.iter().map(|x| x.clone().into_bellman()).collect();
                assert!(h.len() == 256);
                Ok(generate_sha256_round_witness::<T::BellmanEngine>(&i, &h)
                    .into_iter()
                    .map(|x| T::from_bellman(x))
                    .collect())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::Bn128Field;

    #[test]
    fn bits_of_one() {
        let inputs = vec![Bn128Field::from(1)];
        let res = RustHelper::Bits.execute(&inputs).unwrap();
        assert_eq!(res[253], Bn128Field::from(1));
        for i in 0..252 {
            assert_eq!(res[i], Bn128Field::from(0));
        }
    }

    #[test]
    fn bits_of_42() {
        let inputs = vec![Bn128Field::from(42)];
        let res = RustHelper::Bits.execute(&inputs).unwrap();
        assert_eq!(res[253], Bn128Field::from(0));
        assert_eq!(res[252], Bn128Field::from(1));
        assert_eq!(res[251], Bn128Field::from(0));
        assert_eq!(res[250], Bn128Field::from(1));
        assert_eq!(res[249], Bn128Field::from(0));
        assert_eq!(res[248], Bn128Field::from(1));
        assert_eq!(res[247], Bn128Field::from(0));
    }
}
