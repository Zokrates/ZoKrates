#[cfg(feature = "ark")]
pub mod ark;
#[cfg(feature = "bellman")]
pub mod bellman;

#[derive(Debug, Clone)]
#[allow(clippy::upper_case_acronyms)]
pub struct R1CS<T> {
    pub aux_count: usize,
    pub constraints: Vec<Constraint<T>>,
}

impl<T> Default for R1CS<T> {
    fn default() -> Self {
        Self {
            aux_count: 0,
            constraints: vec![],
        }
    }
}

#[derive(Debug)]
pub struct Witness<T> {
    pub values: Vec<T>,
}

#[derive(Default, Debug, PartialEq, Eq, Clone)]
pub struct Constraint<T> {
    pub a: Vec<(T, usize)>,
    pub b: Vec<(T, usize)>,
    pub c: Vec<(T, usize)>,
}
