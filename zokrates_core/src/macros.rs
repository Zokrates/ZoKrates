use crate::compile::CompileError;
use std::fmt;
use zokrates_field::Field;
use zokrates_pest_ast::File;

pub fn process_macros<T: Field>(file: File) -> Result<File, CompileError> {
    match &file.pragma {
        Some(pragma) => {
            if T::name() != pragma.curve.name {
                Err(CompileError::in_module(
                    unimplemented!(),
                    format!(
                        "When processing macros: curve `{}` is incompatible with curve `{}`",
                        T::name().to_string(),
                        pragma.curve.name.clone()
                    ),
                ))
            } else {
                Ok(file)
            }
        }
        None => Ok(file),
    }
}
