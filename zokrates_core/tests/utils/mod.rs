use std::io;
use zokrates_core::compile::{compile, CompileError};
use zokrates_core::field::FieldPrime;
use zokrates_core::ir;

pub fn compile_test(code: &str) -> Result<ir::Prog<FieldPrime>, CompileError<FieldPrime>> {
    compile::<FieldPrime, &[u8], &[u8], io::Error>(&mut code.as_bytes(), None, None)
}
