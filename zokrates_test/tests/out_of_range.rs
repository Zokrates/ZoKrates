extern crate zokrates_common;
extern crate zokrates_core;
extern crate zokrates_field;

use std::io;
use typed_arena::Arena;
use zokrates_common::CompileConfig;
use zokrates_common::Resolver;
use zokrates_core::compile::{compile, CompilationArtifacts};
use zokrates_field::Bn128Field;
use zokrates_fs_resolver::FileSystemResolver;
use zokrates_interpreter::Interpreter;

#[test]
fn lt_field() {
    let source = r#"
		def main(private field a, private field b) {
	        field x = a < b ? 3333 : 4444;
	        assert(x == 3333);
			return;
        }
	"#
    .to_string();

    // let's try to prove that "10000f < 5555f" is true by exploiting
    // the fact that `2*10000 - 2*5555` has two distinct bit decompositions
    // we chose the one which is out of range, ie the sum check features an overflow

    let arena = Arena::new();

    let res: CompilationArtifacts<Bn128Field, _> = compile(
        source,
        "./path/to/file".into(),
        None::<&dyn Resolver<io::Error>>,
        CompileConfig::default(),
        &arena,
    )
    .unwrap();

    let interpreter = Interpreter::try_out_of_range();
    let prog = res.prog();

    assert!(interpreter
        .execute(
            &[Bn128Field::from(10000), Bn128Field::from(5555)],
            prog.statements.into_iter(),
            &prog.arguments,
            &prog.solvers
        )
        .is_err());
}

#[test]
fn lt_uint() {
    let source = r#"
		def main(private u32 a, private u32 b) {
	        field x = a < b ? 3333 : 4444;
	        assert(x == 3333);
			return;
        }
	"#
    .to_string();

    // let's try to prove that "10000u32 < 5555u32" is true by exploiting
    // the fact that `2*10000 - 2*5555` has two distinct bit decompositions
    // we chose the one which is out of range, ie the sum check features an overflow

    let arena = Arena::new();

    let res: CompilationArtifacts<Bn128Field, _> = compile(
        source,
        "./path/to/file".into(),
        None::<&dyn Resolver<io::Error>>,
        CompileConfig::default(),
        &arena,
    )
    .unwrap();

    let interpreter = Interpreter::try_out_of_range();
    let prog = res.prog();

    assert!(interpreter
        .execute(
            &[Bn128Field::from(10000), Bn128Field::from(5555)],
            prog.statements.into_iter(),
            &prog.arguments,
            &prog.solvers
        )
        .is_err());
}

#[test]
fn unpack256() {
    let source = r#"
        import "utils/pack/bool/unpack256";

		def main(private field a) {
	        bool[256] bits = unpack256(a);
			assert(bits[255]);
            return;
        }
	"#
    .to_string();

    // let's try to prove that the least significant bit of 0 is 1
    // we exploit the fact that the bits of 0 are the bits of p, and p is even
    // we want this to still fail

    let stdlib_path = std::fs::canonicalize(
        std::env::current_dir()
            .unwrap()
            .join("../zokrates_stdlib/stdlib"),
    )
    .unwrap();

    let arena = Arena::new();

    let res: CompilationArtifacts<Bn128Field, _> = compile(
        source,
        "./path/to/file".into(),
        Some(&FileSystemResolver::with_stdlib_root(
            stdlib_path.to_str().unwrap(),
        )),
        CompileConfig::default(),
        &arena,
    )
    .unwrap();

    let interpreter = Interpreter::try_out_of_range();
    let prog = res.prog();

    assert!(interpreter
        .execute(
            &[Bn128Field::from(0)],
            prog.statements.into_iter(),
            &prog.arguments,
            &prog.solvers
        )
        .is_err());
}

#[test]
fn unpack256_unchecked() {
    let source = r#"
        import "utils/pack/bool/nonStrictUnpack256";

		def main(private field a) {
	        bool[256] bits = nonStrictUnpack256(a);
			assert(bits[255]);
            return;
        }
	"#
    .to_string();

    // let's try to prove that the least significant bit of 0 is 1
    // we exploit the fact that the bits of 0 are the bits of p, and p is odd
    // we want this to succeed as the non strict version does not enforce the bits to be in range

    let stdlib_path = std::fs::canonicalize(
        std::env::current_dir()
            .unwrap()
            .join("../zokrates_stdlib/stdlib"),
    )
    .unwrap();

    let arena = Arena::new();

    let res: CompilationArtifacts<Bn128Field, _> = compile(
        source,
        "./path/to/file".into(),
        Some(&FileSystemResolver::with_stdlib_root(
            stdlib_path.to_str().unwrap(),
        )),
        CompileConfig::default(),
        &arena,
    )
    .unwrap();

    let interpreter = Interpreter::try_out_of_range();
    let prog = res.prog();

    assert!(interpreter
        .execute(
            &[Bn128Field::from(0)],
            prog.statements.into_iter(),
            &prog.arguments,
            &prog.solvers
        )
        .is_ok());
}
