use zokrates_field::field::Field;
use std::collections::HashSet;
use typed_absy::identifier::CallIdentifier;

pub struct Memoizer<'ast, T: Field> {
	identifiers: HashSet<CallIdentifier<'ast, T>>
}