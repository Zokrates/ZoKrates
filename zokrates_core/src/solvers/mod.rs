use std::fmt;
use zokrates_field::Field;

#[derive(Clone, PartialEq, Debug, Serialize, Deserialize, Hash, Eq)]
pub enum Solver {
    ConditionEq,
    Bits(usize),
    Div,
    Xor,
    Or,
    ShaAndXorAndXorAnd,
    ShaCh,
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
        }
    }
}

impl Solver {
    pub fn bits(width: usize) -> Self {
        Solver::Bits(width)
    }
}

pub trait Executable<T: Field>: Signed {
    fn execute(&self, inputs: &Vec<T>) -> Result<Vec<T>, String>;
}

pub trait Signed {
    fn get_signature(&self) -> (usize, usize);
}
