use std::fmt;
use zokrates_embed::generate_sha256_round_witness;
use zokrates_field::field::Field;

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize, Hash, Eq)]
pub enum Solver {
    Identity,
    ConditionEq,
    Bits(usize),
    Div,
    Sha256Round,
}

impl fmt::Display for Solver {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Solver {
    pub fn get_signature(&self) -> (usize, usize) {
        match self {
            Solver::Identity => (1, 1),
            Solver::ConditionEq => (1, 2),
            Solver::Bits(bit_width) => (1, *bit_width),
            Solver::Div => (2, 1),
            Solver::Sha256Round => (768, 26935),
        }
    }
}

impl Solver {
    pub fn execute<T: Field>(&self, inputs: &Vec<T>) -> Result<Vec<T>, String> {
        let res = match self {
            Solver::Identity => inputs.clone(),
            Solver::ConditionEq => match inputs[0].is_zero() {
                true => vec![T::zero(), T::one()],
                false => vec![T::one(), T::one() / inputs[0].clone()],
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
                assert_eq!(num, T::zero());
                res
            }
            Solver::Div => vec![inputs[0].clone() / inputs[1].clone()],
            Solver::Sha256Round => {
                let i = &inputs[0..512];
                let h = &inputs[512..];
                let i: Vec<_> = i.iter().map(|x| x.clone().into_bellman()).collect();
                let h: Vec<_> = h.iter().map(|x| x.clone().into_bellman()).collect();
                assert!(h.len() == 256);
                generate_sha256_round_witness::<T::BellmanEngine>(&i, &h)
                    .into_iter()
                    .map(|x| T::from_bellman(x))
                    .collect()
            }
        };

        assert_eq!(res.len(), self.get_signature().1);

        Ok(res)
    }
}

impl Solver {
    pub fn bits(width: usize) -> Self {
        Solver::Bits(width)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    #[test]
    fn bits_of_one() {
        let inputs = vec![FieldPrime::from(1)];
        let res = Solver::Bits(FieldPrime::get_required_bits())
            .execute(&inputs)
            .unwrap();
        assert_eq!(res[253], FieldPrime::from(1));
        for i in 0..252 {
            assert_eq!(res[i], FieldPrime::from(0));
        }
    }

    #[test]
    fn bits_of_42() {
        let inputs = vec![FieldPrime::from(42)];
        let res = Solver::Bits(FieldPrime::get_required_bits())
            .execute(&inputs)
            .unwrap();
        assert_eq!(res[253], FieldPrime::from(0));
        assert_eq!(res[252], FieldPrime::from(1));
        assert_eq!(res[251], FieldPrime::from(0));
        assert_eq!(res[250], FieldPrime::from(1));
        assert_eq!(res[249], FieldPrime::from(0));
        assert_eq!(res[248], FieldPrime::from(1));
        assert_eq!(res[247], FieldPrime::from(0));
    }
}
