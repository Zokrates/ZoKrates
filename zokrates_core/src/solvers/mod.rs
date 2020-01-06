use std::fmt;
use zokrates_embed::generate_sha256_round_witness;
use zokrates_field::field::Field;

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize, Hash, Eq)]
pub enum Solver {
    ConditionEq,
    Bits,
    Div,
    Sha256Round,
}

impl fmt::Display for Solver {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Signed for Solver {
    fn get_signature(&self) -> (usize, usize) {
        match self {
            Solver::ConditionEq => (1, 2),
            Solver::Bits => (1, 254),
            Solver::Div => (2, 1),
            Solver::Sha256Round => (768, 26935),
        }
    }
}

impl<T: Field> Executable<T> for Solver {
    fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, String> {
        let (expected_input_count, expected_output_count) = self.get_signature();
        assert!(inputs.len() == expected_input_count);

        let res = match self {
            Solver::ConditionEq => match inputs[0].is_zero() {
                true => vec![T::zero(), T::one()],
                false => vec![T::one(), T::one() / inputs[0].clone()],
            },
            Solver::Bits => {
                let mut num = inputs[0].clone();
                let mut res = vec![];
                let bits = 254;
                for i in (0..bits).rev() {
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

        assert_eq!(res.len(), expected_output_count);

        Ok(res)
    }
}

impl Solver {
    pub fn bits() -> Self {
        Solver::Bits
    }
}

pub trait Executable<T: Field>: Signed {
    fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, String>;
}

pub trait Signed {
    fn get_signature(&self) -> (usize, usize);
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

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
                .execute(&inputs.iter().map(|&i| FieldPrime::from(i)).collect())
                .unwrap();
            let res: Vec<FieldPrime> = vec![0, 1].iter().map(|&i| FieldPrime::from(i)).collect();
            assert_eq!(r, &res[..]);
        }

        #[test]
        fn execute_non_eq() {
            let cond_eq = Solver::ConditionEq;
            let inputs = vec![1];
            let r = cond_eq
                .execute(&inputs.iter().map(|&i| FieldPrime::from(i)).collect())
                .unwrap();
            let res: Vec<FieldPrime> = vec![1, 1].iter().map(|&i| FieldPrime::from(i)).collect();
            assert_eq!(r, &res[..]);
        }
    }

    #[test]
    fn bits_of_one() {
        let inputs = vec![FieldPrime::from(1)];
        let res = Solver::Bits.execute(&inputs).unwrap();
        assert_eq!(res[253], FieldPrime::from(1));
        for i in 0..252 {
            assert_eq!(res[i], FieldPrime::from(0));
        }
    }

    #[test]
    fn bits_of_42() {
        let inputs = vec![FieldPrime::from(42)];
        let res = Solver::Bits.execute(&inputs).unwrap();
        assert_eq!(res[253], FieldPrime::from(0));
        assert_eq!(res[252], FieldPrime::from(1));
        assert_eq!(res[251], FieldPrime::from(0));
        assert_eq!(res[250], FieldPrime::from(1));
        assert_eq!(res[249], FieldPrime::from(0));
        assert_eq!(res[248], FieldPrime::from(1));
        assert_eq!(res[247], FieldPrime::from(0));
    }
}
