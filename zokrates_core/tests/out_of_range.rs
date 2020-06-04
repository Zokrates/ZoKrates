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
		def main(private field a) -> (field):
	        field x = if a < 5555 then 3333 else 4444 fi
	        x == 3333
			return 1
	"#
    .to_string();

    // let's try to prove that "10000 < 5555" is true by exploiting
    // the fact that `2*10000 - 2*5555` has two distinct bit decompositions
    // we chose the one which is out of range, ie the sum check features an overflow

    let res: CompilationArtifacts<FieldPrime> =
        compile(source, "./path/to/file".into(), None::<Resolve<io::Error>>).unwrap();

    let interpreter = Interpreter::try_out_of_range();

    assert!(interpreter
        .execute(&res.prog(), &vec![FieldPrime::from(10000)])
        .is_err());
}
