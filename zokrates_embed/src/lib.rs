pub mod blake2s;
pub mod sha256;

extern crate sapling_crypto_ce as sapling_crypto;
use sapling_crypto::bellman;

use bellman::{
    pairing::Engine, ConstraintSystem, Index, LinearCombination, SynthesisError, Variable,
};

#[derive(Debug)]
pub struct BellmanR1CS<E: Engine> {
    pub aux_count: usize,
    pub constraints: Vec<BellmanConstraint<E>>,
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
pub struct BellmanWitness<E: Engine> {
    pub values: Vec<E::Fr>,
}

#[derive(Debug, PartialEq)]
pub struct BellmanConstraint<E: Engine> {
    pub a: Vec<(usize, E::Fr)>,
    pub b: Vec<(usize, E::Fr)>,
    pub c: Vec<(usize, E::Fr)>,
}

impl<E: Engine> ConstraintSystem<E> for BellmanWitness<E> {
    type Root = Self;

    fn alloc<F, A, AR>(&mut self, _: A, f: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        let index = self.values.len();
        let var = Variable::new_unchecked(Index::Aux(index));
        self.values.push(f().unwrap());
        Ok(var)
    }

    fn alloc_input<F, A, AR>(&mut self, _: A, _: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        unreachable!("Bellman helpers are not allowed to allocate public variables")
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, _: A, _: LA, _: LB, _: LC)
    where
        A: FnOnce() -> AR,
        AR: Into<String>,
        LA: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
        LB: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
        LC: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
    {
        // do nothing
    }

    fn push_namespace<NR, N>(&mut self, _: N)
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

    fn alloc<F, A, AR>(&mut self, _: A, _: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        // we don't care about the value as we're only generating the CS
        let index = self.aux_count;
        let var = Variable::new_unchecked(Index::Aux(index));
        self.aux_count += 1;
        Ok(var)
    }

    fn alloc_input<F, A, AR>(&mut self, _: A, _: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>,
        A: FnOnce() -> AR,
        AR: Into<String>,
    {
        unreachable!("Bellman helpers are not allowed to allocate public variables")
    }

    fn enforce<A, AR, LA, LB, LC>(&mut self, _: A, a: LA, b: LB, c: LC)
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
            .map(|(variable, coefficient)| (var_to_index(*variable), *coefficient))
            .collect();
        let b = b
            .as_ref()
            .into_iter()
            .map(|(variable, coefficient)| (var_to_index(*variable), *coefficient))
            .collect();
        let c = c
            .as_ref()
            .into_iter()
            .map(|(variable, coefficient)| (var_to_index(*variable), *coefficient))
            .collect();

        self.constraints.push(BellmanConstraint { a, b, c });
    }

    fn push_namespace<NR, N>(&mut self, _: N)
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

fn var_to_index(v: Variable) -> usize {
    match v.get_unchecked() {
        Index::Aux(i) => i + 1,
        Index::Input(0) => 0,
        _ => unreachable!("No public variables should have been allocated"),
    }
}
