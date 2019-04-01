use bellman::pairing::Engine;
use bellman::ConstraintSystem;
use bellman::{Index, LinearCombination, SynthesisError, Variable};
use sapling_crypto::circuit::boolean::{AllocatedBit, Boolean};
use sapling_crypto::circuit::sha256::sha256_compression_function;
use sapling_crypto::circuit::uint32::UInt32;
use zokrates_field::field::Field;

#[derive(Debug)]
struct BellmanR1CS<E: Engine> {
    aux_count: usize,
    constraints: Vec<BellmanConstraint<E>>,
}

impl<E: Engine> BellmanR1CS<E> {
    pub fn new() -> Self {
        BellmanR1CS {
            aux_count: 0,
            constraints: vec![],
        }
    }
}

#[derive(Debug)]
struct BellmanWitness<E: Engine> {
    pub values: Vec<E::Fr>,
}

#[derive(Debug, PartialEq)]
struct BellmanConstraint<E: Engine> {
    pub a: Vec<(usize, E::Fr)>,
    pub b: Vec<(usize, E::Fr)>,
    pub c: Vec<(usize, E::Fr)>,
}

#[derive(Debug, PartialEq)]
pub struct Constraint<T: Field> {
    pub a: Vec<(usize, T)>,
    pub b: Vec<(usize, T)>,
    pub c: Vec<(usize, T)>,
}

#[derive(Debug)]
pub struct R1CS<T: Field> {
    pub aux_count: usize,
    pub constraints: Vec<Constraint<T>>,
}

fn sha256_round<T: Field, CS: ConstraintSystem<T::BellmanEngine>>(
    mut cs: CS,
    input: Option<&Vec<T>>,
    current_hash: Option<&Vec<T>>,
) -> Result<(Vec<usize>, Vec<usize>, Vec<usize>), SynthesisError> {
    let input_bits = (0..512)
        .map(|i| {
            AllocatedBit::alloc::<T::BellmanEngine, _>(
                &mut cs.namespace(|| format!("input_{}", i)),
                Some(input.as_ref().unwrap()[i] == T::from(1)),
            )
            .unwrap()
        })
        .collect::<Vec<_>>();

    let input = input_bits
        .iter()
        .map(|i| Boolean::Is(i.clone()))
        .collect::<Vec<_>>();

    let current_hash_bits = (0..256)
        .map(|i| {
            AllocatedBit::alloc::<T::BellmanEngine, _>(
                &mut cs.namespace(|| format!("current_hash_{}", i)),
                Some(current_hash.as_ref().unwrap()[i] == T::from(1)),
            )
            .unwrap()
        })
        .collect::<Vec<_>>();

    let current_hash = current_hash_bits
        .chunks(32)
        .map(|chunk| {
            UInt32::from_bits_be(
                &chunk
                    .into_iter()
                    .map(|i| Boolean::Is(i.clone()))
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<Vec<_>>();

    let res =
        sha256_compression_function::<T::BellmanEngine, _>(&mut cs, &input, &current_hash).unwrap();

    let output_bits = res
        .into_iter()
        .flat_map(|u| u.into_bits_be())
        .map(|b| b.get_variable().unwrap().clone())
        .collect::<Vec<_>>();

    Ok((
        input_bits
            .into_iter()
            .map(|b| BellmanR1CS::<T::BellmanEngine>::var_to_index(b.get_variable()))
            .collect(),
        current_hash_bits
            .into_iter()
            .map(|b| BellmanR1CS::<T::BellmanEngine>::var_to_index(b.get_variable()))
            .collect(),
        output_bits
            .into_iter()
            .map(|b| BellmanR1CS::<T::BellmanEngine>::var_to_index(b.get_variable()))
            .collect(),
    ))
}

impl<T: Field> R1CS<T> {
    fn from_bellman(cs: BellmanR1CS<T::BellmanEngine>) -> Self {
        R1CS {
            aux_count: cs.aux_count,
            constraints: cs
                .constraints
                .into_iter()
                .map(|c| Constraint::from_bellman(c))
                .collect(),
        }
    }
}

impl<T: Field> Constraint<T> {
    fn from_bellman(cs: BellmanConstraint<T::BellmanEngine>) -> Self {
        let res = Constraint {
            a: cs
                .a
                .into_iter()
                .map(|(variable, coefficient)| (variable, T::from_bellman(coefficient)))
                .collect(),
            b: cs
                .b
                .into_iter()
                .map(|(variable, coefficient)| (variable, T::from_bellman(coefficient)))
                .collect(),
            c: cs
                .c
                .into_iter()
                .map(|(variable, coefficient)| (variable, T::from_bellman(coefficient)))
                .collect(),
        };
        res
    }
}

impl<E: Engine> ConstraintSystem<E> for BellmanWitness<E> {
    type Root = Self;

    fn alloc<F, A, AR>(&mut self, _annotation: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // we only care about the value
        let index = self.values.len();
        let var = Variable::new_unchecked(Index::Aux(index));
        self.values.push(f().unwrap());
        Ok(var)
    }

    fn alloc_input<F, A, AR>(&mut self, _annotation: A, _f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        unreachable!("Bellman helpers are not allowed to allocate public variables")
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, _annotation: A, _a: LA, _b: LB, _c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
        LB: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
        LC: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
    {
        // do nothing
    }

    fn push_namespace<NR, N>(&mut self, _name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // do nothing
    }

    fn pop_namespace(&mut self) {
        // do nothing
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }
}

impl<E: Engine> ConstraintSystem<E> for BellmanR1CS<E> {
    type Root = Self;

    fn alloc<F, A, AR>(&mut self, _annotation: A, _f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // we don't care about the value as we're only getting the CS
        let index = self.aux_count;
        let var = Variable::new_unchecked(Index::Aux(index));
        self.aux_count += 1;
        Ok(var)
    }

    fn alloc_input<F, A, AR>(&mut self, _annotation: A, _f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        unreachable!("Bellman helpers are not allowed to allocate public variables")
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, _annotation: A, a: LA, b: LB, c: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
        LB: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
        LC: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
    {
        let a = a(LinearCombination::zero());
        let b = b(LinearCombination::zero());
        let c = c(LinearCombination::zero());

        let a = a
            .as_ref()
            .into_iter()
            .map(|(variable, coefficient)| {
                (BellmanR1CS::<E>::var_to_index(*variable), *coefficient)
            })
            .collect();
        let b = b
            .as_ref()
            .into_iter()
            .map(|(variable, coefficient)| {
                (BellmanR1CS::<E>::var_to_index(*variable), *coefficient)
            })
            .collect();
        let c = c
            .as_ref()
            .into_iter()
            .map(|(variable, coefficient)| {
                (BellmanR1CS::<E>::var_to_index(*variable), *coefficient)
            })
            .collect();

        self.constraints.push(BellmanConstraint { a, b, c });
    }

    fn push_namespace<NR, N>(&mut self, _name_fn: N)
    where
        NR: Into<String>,
        N: FnOnce() -> NR,
    {
        // do nothing
    }

    fn pop_namespace(&mut self) {
        // do nothing
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }
}

pub fn generate_xor_constraints<T: Field>() -> (R1CS<T>, usize) {
    let mut cs = BellmanR1CS::new();

    let i0 = Boolean::Is(AllocatedBit::alloc::<T::BellmanEngine, _>(&mut cs, None).unwrap());
    let i1 = Boolean::Is(AllocatedBit::alloc::<T::BellmanEngine, _>(&mut cs, None).unwrap());

    let res = Boolean::xor(&mut cs, &i0, &i1).unwrap();
    let res =
        BellmanR1CS::<T::BellmanEngine>::var_to_index(res.get_variable().unwrap().get_variable());

    let cs = R1CS::from_bellman(cs);

    (cs, res)
}

pub fn generate_xor_witness<T: Field>(i1: bool, i2: bool) -> Vec<T> {
    let mut cs = BellmanWitness {
        values: vec![T::from(1).into_bellman()],
    };

    let i0 = Boolean::Is(AllocatedBit::alloc::<T::BellmanEngine, _>(&mut cs, Some(i1)).unwrap());
    let i1 = Boolean::Is(AllocatedBit::alloc::<T::BellmanEngine, _>(&mut cs, Some(i2)).unwrap());

    Boolean::xor(&mut cs, &i0, &i1).unwrap();

    cs.values.into_iter().map(|v| T::from_bellman(v)).collect()
}

pub fn generate_sha256_round_constraints<T: Field>() -> (R1CS<T>, Vec<usize>, Vec<usize>, Vec<usize>)
{
    let mut cs = BellmanR1CS::new();

    let (input_bits, current_hash_bits, output_bits) = sha256_round::<T, _>(
        &mut cs,
        Some(&vec![T::from(0); 512]),
        Some(&vec![T::from(0); 256]),
    )
    .unwrap();

    // res is now the allocated bits for input, current_hash and sha256_output

    let cs = R1CS::<T>::from_bellman(cs);

    (cs, input_bits, current_hash_bits, output_bits)
}

pub fn generate_sha256_round_witness<T: Field>(input: &[T], current_hash: &[T]) -> Vec<T> {
    assert_eq!(input.len(), 512);
    assert_eq!(current_hash.len(), 256);

    let mut cs = BellmanWitness {
        values: vec![T::from(1).into_bellman()],
    };

    sha256_round(&mut cs, Some(&input.to_vec()), Some(&current_hash.to_vec())).unwrap();

    cs.values.into_iter().map(|v| T::from_bellman(v)).collect()
}

impl<E: Engine> BellmanR1CS<E> {
    fn var_to_index(v: Variable) -> usize {
        match v.get_unchecked() {
            Index::Aux(i) => i + 1,
            Index::Input(0) => 0,
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    #[test]
    fn generate_constraints() {
        let (_c, input, current_hash, output) = generate_sha256_round_constraints::<FieldPrime>();
        assert_eq!(input.len(), 512);
        assert_eq!(current_hash.len(), 256);
        assert_eq!(output.len(), 256);
    }

    #[test]
    fn generate_witness() {
        let witness = generate_sha256_round_witness(
            &vec![FieldPrime::from(0); 512],
            &vec![FieldPrime::from(0); 256],
        );
        assert_eq!(witness.len(), 26935);
    }

    #[test]
    fn xor() {
        let (_, indice) = generate_xor_constraints::<FieldPrime>();

        assert_eq!(
            FieldPrime::from(0),
            generate_xor_witness::<FieldPrime>(true, true)[indice]
        );
        assert_eq!(
            FieldPrime::from(1),
            generate_xor_witness::<FieldPrime>(true, false)[indice]
        );
        assert_eq!(
            FieldPrime::from(1),
            generate_xor_witness::<FieldPrime>(false, true)[indice]
        );
        assert_eq!(
            FieldPrime::from(0),
            generate_xor_witness::<FieldPrime>(false, false)[indice]
        );
    }

    #[test]
    fn test_cs() {
        use sapling_crypto::circuit::test::TestConstraintSystem;

        let mut cs = TestConstraintSystem::new();

        let _ = sha256_round::<FieldPrime, _>(
            &mut cs,
            Some(&vec![FieldPrime::from(0); 512]),
            Some(&vec![FieldPrime::from(1); 256]),
        )
        .unwrap();

        assert!(cs.is_satisfied());
    }
}
