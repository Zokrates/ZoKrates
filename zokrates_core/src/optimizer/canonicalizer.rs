use zokrates_ast::ir::{folder::Folder, LinComb};
use zokrates_field::Field;

#[derive(Default)]
pub struct Canonicalizer;

impl<T: Field> Folder<T> for Canonicalizer {
    fn fold_linear_combination(&mut self, l: LinComb<T>) -> LinComb<T> {
        l.into_canonical().into()
    }
}
