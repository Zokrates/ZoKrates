extern crate zokrates_common;
extern crate zokrates_core;
extern crate zokrates_field;

use std::io;
use zokrates_common::Resolver;
use zokrates_core::compile::CompileConfig;
use zokrates_core::{
    compile::{compile, CompilationArtifacts},
    ir::Interpreter,
};
use zokrates_field::Bn128Field;

#[test]
fn lt_field() {
    let source = r#"
		def main(private field a, private field b) -> field:
	        field x = if a < b then 3333 else 4444 fi
	        assert(x == 3333)
			return 1
	"#
    .to_string();

    // let's try to prove that "10000f < 5555f" is true by exploiting
    // the fact that `2*10000 - 2*5555` has two distinct bit decompositions
    // we chose the one which is out of range, ie the sum check features an overflow

    let res: CompilationArtifacts<Bn128Field> = compile(
        source,
        "./path/to/file".into(),
        None::<&dyn Resolver<io::Error>>,
        &CompileConfig::default(),
    )
    .unwrap();

    let interpreter = Interpreter::try_out_of_range();

    assert!(interpreter
        .execute(
            &res.prog(),
            &[Bn128Field::from(10000), Bn128Field::from(5555)]
        )
        .is_err());
}

#[test]
fn lt_uint() {
    let source = r#"
		def main(private u32 a, private u32 b):
	        field x = if a < b then 3333 else 4444 fi
	        assert(x == 3333)
			return
	"#
    .to_string();

    // let's try to prove that "10000u32 < 5555u32" is true by exploiting
    // the fact that `2*10000 - 2*5555` has two distinct bit decompositions
    // we chose the one which is out of range, ie the sum check features an overflow

    let res: CompilationArtifacts<Bn128Field> = compile(
        source,
        "./path/to/file".into(),
        None::<&dyn Resolver<io::Error>>,
        &CompileConfig::default(),
    )
    .unwrap();

    let interpreter = Interpreter::try_out_of_range();

    assert!(interpreter
        .execute(
            &res.prog(),
            &[Bn128Field::from(10000), Bn128Field::from(5555)]
        )
        .is_err());
}
