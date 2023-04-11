use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;
use std::io::{Read, Write};

// A variable in a constraint system
// id > 0 for intermediate variables
// id == 0 for ~one
// id < 0 for public outputs
#[derive(Serialize, Deserialize, Clone, PartialEq, Hash, Eq, Ord, PartialOrd, Copy)]
pub struct Variable {
    pub id: isize,
}

impl Variable {
    pub fn new(id: usize) -> Self {
        Variable {
            id: 1 + id as isize,
        }
    }

    pub fn one() -> Self {
        Variable { id: 0 }
    }

    pub fn public(id: usize) -> Self {
        Variable {
            id: -(id as isize) - 1,
        }
    }

    pub fn id(&self) -> usize {
        assert!(self.id > 0);
        (self.id as usize) - 1
    }

    pub fn write<W: Write>(&self, mut writer: W) -> std::io::Result<()> {
        writer.write_all(&self.id.to_le_bytes())?;
        Ok(())
    }

    pub fn read<R: Read>(mut reader: R) -> std::io::Result<Self> {
        let mut buf = [0; std::mem::size_of::<isize>()];
        reader.read_exact(&mut buf)?;

        Ok(Variable {
            id: isize::from_le_bytes(buf),
        })
    }
}

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.id {
            0 => write!(f, "~one"),
            i if i > 0 => write!(f, "_{}", i - 1),
            i => write!(f, "~out_{}", -(i + 1)),
        }
    }
}

impl fmt::Debug for Variable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.id {
            0 => write!(f, "~one"),
            i if i > 0 => write!(f, "_{}", i - 1),
            i => write!(f, "~out_{}", -(i + 1)),
        }
    }
}

impl Variable {
    pub fn apply_substitution(self, substitution: &HashMap<Variable, Variable>) -> &Self {
        substitution.get(&self).unwrap()
    }

    pub fn is_output(&self) -> bool {
        self.id < 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn one() {
        assert_eq!(format!("{}", Variable::one()), "~one");
    }

    #[test]
    fn public() {
        assert_eq!(format!("{}", Variable::public(0)), "~out_0");
        assert_eq!(format!("{}", Variable::public(42)), "~out_42");
    }

    #[test]
    fn private() {
        assert_eq!(format!("{}", Variable::new(0)), "_0");
        assert_eq!(format!("{}", Variable::new(42)), "_42");
    }
}
