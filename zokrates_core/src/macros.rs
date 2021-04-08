use std::fmt;
use zokrates_field::Field;
use zokrates_pest_ast::File;

#[derive(Debug)]
pub enum Error {
    Curve(String, String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Curve(expected, found) => write!(
                f,
                "When processing macros: curve `{}` is incompatible with curve `{}`",
                found, expected
            ),
        }
    }
}

pub fn process_macros<T: Field>(file: File) -> Result<File, Error> {
    match &file.pragma {
        Some(pragma) => {
            if T::name() != pragma.curve.name {
                Err(Error::Curve(
                    T::name().to_string(),
                    pragma.curve.name.clone(),
                ))
            } else {
                Ok(file)
            }
        }
        None => Ok(file),
    }
}
