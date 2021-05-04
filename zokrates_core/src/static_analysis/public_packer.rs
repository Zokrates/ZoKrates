use crate::zir::{Folder, ZirFunction, ZirProgram};
use zokrates_field::Field;

pub struct PublicPacker;

impl PublicPacker {
    pub fn pack<'ast, T>(p: ZirProgram<'ast, T>) -> ZirProgram<'ast, T> {
        p
    }
}

impl<'ast, T: Field> Folder<'ast, T> for PublicPacker {
    fn fold_function(&mut self, fun: ZirFunction<'ast, T>) -> ZirFunction<'ast, T> {
        let signature = fun.signature;

        let packed_signature = unimplemented!(); // based on signature

        let packed_arguments = unimplemented!(); // based on signature

        let input_unpacking_statements: Vec<_> = unimplemented!(); // based on signature and argument names

        let output_packing_statements: Vec<_> = unimplemented!(); // based on signature and return statement

        let statements = input_unpacking_statements
            .into_iter()
            .chain(fun.statements)
            .chain(output_packing_statements)
            .collect();

        ZirFunction {
            arguments: packed_arguments,
            statements,
            signature: packed_signature,
            ..fun
        }
    }
}
