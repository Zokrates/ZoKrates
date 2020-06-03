extern crate zokrates_core;
extern crate zokrates_field;

use std::io;
use zokrates_core::{
    compile::{compile, CompilationArtifacts, Resolve},
    ir::Interpreter,
};
use zokrates_field::field::FieldPrime;

#[test]
fn out_of_range() {
    let source = r#"
		def main(field a) -> ():
			true == a < 1
			return
	"#
    .to_string();

    // let's try to prove that "2 < 1" is true by exploiting
    // the fact that `2*2 - 2*1` has two distinct bit decompositions
    // we chose the one which is out of range, ie the sum check features an overflow

    let res: CompilationArtifacts<FieldPrime> =
        compile(source, "./path/to/file".into(), None::<Resolve<io::Error>>).unwrap();

    let interpreter = Interpreter::try_out_of_range();

    assert!(interpreter
        .execute(&res.prog(), &vec![FieldPrime::from(2)])
        .is_err());
}
