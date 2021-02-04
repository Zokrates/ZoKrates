#[cfg(feature = "bellman")]
use pairing_ce::bn256::Bn256;
use serde::{Deserialize, Serialize};
use std::fmt;
use zokrates_embed::blake2s::generate_blake2s_round_witness;
#[cfg(feature = "bellman")]
use zokrates_embed::sha256::generate_sha256_round_witness;
use zokrates_field::{Bn128Field, Field};

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize, Hash, Eq)]
pub enum Solver {
    ConditionEq,
    Bits(usize),
    Div,
    Xor,
    Or,
    ShaAndXorAndXorAnd,
    ShaCh,
    EuclideanDiv,
    #[cfg(feature = "bellman")]
    Sha256Round,
    #[cfg(feature = "bellman")]
    Blake2s,
}

impl fmt::Display for Solver {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Solver {
    pub fn get_signature(&self) -> (usize, usize) {
        match self {
            Solver::ConditionEq => (1, 2),
            Solver::Bits(bit_width) => (1, *bit_width),
            Solver::Div => (2, 1),
            Solver::Xor => (2, 1),
            Solver::Or => (2, 1),
            Solver::ShaAndXorAndXorAnd => (3, 1),
            Solver::ShaCh => (3, 1),
            Solver::EuclideanDiv => (2, 2),
            #[cfg(feature = "bellman")]
            Solver::Sha256Round => (768, 26935),
            #[cfg(feature = "bellman")]
            Solver::Blake2s => (512, 21473),
        }
    }
}

impl Solver {
    pub fn bits(width: usize) -> Self {
        Solver::Bits(width)
    }
}

pub trait Executable<T> {
    fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, String>;
}

impl<T: Field> Executable<T> for Solver {
    fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, String> {
        let (expected_input_count, expected_output_count) = self.get_signature();
        assert_eq!(inputs.len(), expected_input_count);

        let res = match self {
            Solver::ConditionEq => match inputs[0].is_zero() {
                true => vec![T::zero(), T::one()],
                false => vec![
                    T::one(),
                    T::one().checked_div(&inputs[0]).unwrap_or(T::one()),
                ],
            },
            Solver::Bits(bit_width) => {
                let mut num = inputs[0].clone();
                let mut res = vec![];

                for i in (0..*bit_width).rev() {
                    if T::from(2).pow(i) <= num {
                        num = num - T::from(2).pow(i);
                        res.push(T::one());
                    } else {
                        res.push(T::zero());
                    }
                }
                res
            }
            Solver::Xor => {
                let x = inputs[0].clone();
                let y = inputs[1].clone();

                vec![x.clone() + y.clone() - T::from(2) * x * y]
            }
            Solver::Or => {
                let x = inputs[0].clone();
                let y = inputs[1].clone();

                vec![x.clone() + y.clone() - x * y]
            }
            // res = b * c - (2b * c - b - c) * (a)
            Solver::ShaAndXorAndXorAnd => {
                let a = inputs[0].clone();
                let b = inputs[1].clone();
                let c = inputs[2].clone();
                vec![b.clone() * c.clone() - (T::from(2) * b.clone() * c.clone() - b - c) * a]
            }
            // res = a(b - c) + c
            Solver::ShaCh => {
                let a = inputs[0].clone();
                let b = inputs[1].clone();
                let c = inputs[2].clone();
                vec![a * (b - c.clone()) + c]
            }
            Solver::Div => vec![inputs[0]
                .clone()
                .checked_div(&inputs[1])
                .unwrap_or(T::one())],
            Solver::EuclideanDiv => {
                use num::CheckedDiv;

                let n = inputs[0].clone().to_biguint();
                let d = inputs[1].clone().to_biguint();

                let q = n.checked_div(&d).unwrap_or(0u32.into());
                let r = n - d * &q;
                vec![T::try_from(q).unwrap(), T::try_from(r).unwrap()]
            }
            #[cfg(feature = "bellman")]
            Solver::Sha256Round => {
                assert_eq!(T::id(), Bn128Field::id());
                let i = &inputs[0..512];
                let h = &inputs[512..];
                let to_fr = |x: &T| {
                    use pairing_ce::ff::{PrimeField, ScalarEngine};
                    let s = x.to_dec_string();
                    <Bn256 as ScalarEngine>::Fr::from_str(&s).unwrap()
                };
                let i: Vec<_> = i.iter().map(|x| to_fr(x)).collect();
                let h: Vec<_> = h.iter().map(|x| to_fr(x)).collect();
                assert_eq!(h.len(), 256);
                generate_sha256_round_witness::<Bn256>(&i, &h)
                    .into_iter()
                    .map(|x| {
                        use bellman_ce::pairing::ff::{PrimeField, PrimeFieldRepr};
                        let mut res: Vec<u8> = vec![];
                        x.into_repr().write_le(&mut res).unwrap();
                        T::from_byte_vector(res)
                    })
                    .collect()
            }
            #[cfg(feature = "bellman")]
            Solver::Blake2s => {
                assert_eq!(T::id(), Bn128Field::id());
                let i = &inputs[0..512];
                let to_fr = |x: &T| {
                    use pairing_ce::ff::{PrimeField, ScalarEngine};
                    let s = x.to_dec_string();
                    <Bn256 as ScalarEngine>::Fr::from_str(&s).unwrap()
                };
                let i: Vec<_> = i.iter().map(|x| to_fr(x)).collect();
                generate_blake2s_round_witness::<Bn256>(&i)
                    .into_iter()
                    .map(|x| {
                        use bellman_ce::pairing::ff::{PrimeField, PrimeFieldRepr};
                        let mut res: Vec<u8> = vec![];
                        x.into_repr().write_le(&mut res).unwrap();
                        T::from_byte_vector(res)
                    })
                    .collect()
            }
        };

        assert_eq!(res.len(), expected_output_count);

        Ok(res)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::Bn128Field;

    mod eq_condition {

        // Wanted: (Y = (X != 0) ? 1 : 0)
        // # Y = if X == 0 then 0 else 1 fi
        // # M = if X == 0 then 1 else 1/X fi

        use super::*;

        #[test]
        fn execute() {
            let cond_eq = Solver::ConditionEq;
            let inputs = vec![0];
            let r = cond_eq
                .execute(&inputs.iter().map(|&i| Bn128Field::from(i)).collect())
                .unwrap();
            let res: Vec<Bn128Field> = vec![0, 1].iter().map(|&i| Bn128Field::from(i)).collect();
            assert_eq!(r, &res[..]);
        }

        #[test]
        fn execute_non_eq() {
            let cond_eq = Solver::ConditionEq;
            let inputs = vec![1];
            let r = cond_eq
                .execute(&inputs.iter().map(|&i| Bn128Field::from(i)).collect())
                .unwrap();
            let res: Vec<Bn128Field> = vec![1, 1].iter().map(|&i| Bn128Field::from(i)).collect();
            assert_eq!(r, &res[..]);
        }
    }

    #[test]
    fn bits_of_one() {
        let bits = Solver::Bits(Bn128Field::get_required_bits());
        let inputs = vec![Bn128Field::from(1)];
        let res = bits.execute(&inputs).unwrap();
        assert_eq!(res[253], Bn128Field::from(1));
        for i in 0..253 {
            assert_eq!(res[i], Bn128Field::from(0));
        }
    }

    #[test]
    fn bits_of_42() {
        let bits = Solver::Bits(Bn128Field::get_required_bits());
        let inputs = vec![Bn128Field::from(42)];
        let res = bits.execute(&inputs).unwrap();

        assert_eq!(res[253], Bn128Field::from(0));
        assert_eq!(res[252], Bn128Field::from(1));
        assert_eq!(res[251], Bn128Field::from(0));
        assert_eq!(res[250], Bn128Field::from(1));
        assert_eq!(res[249], Bn128Field::from(0));
        assert_eq!(res[248], Bn128Field::from(1));
        assert_eq!(res[247], Bn128Field::from(0));
    }
}
