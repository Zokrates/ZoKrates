use std::collections::HashSet;
use zokrates_ast::ir::folder::Folder;
use zokrates_ast::ir::Directive;
use zokrates_ast::ir::Parameter;
use zokrates_ast::ir::ProgIterator;
use zokrates_ast::ir::Statement;
use zokrates_ast::ir::Variable;
use zokrates_field::Field;

#[derive(Debug)]
pub struct UnconstrainedVariableDetector {
    pub(self) variables: HashSet<Variable>,
}

impl UnconstrainedVariableDetector {
    pub fn new<T: Field, I: IntoIterator<Item = Statement<T>>>(p: &ProgIterator<T, I>) -> Self {
        UnconstrainedVariableDetector {
            variables: p
                .arguments
                .iter()
                .filter(|p| p.private)
                .map(|p| p.id)
                .collect(),
        }
    }

    pub fn finalize(self) -> Result<(), usize> {
        if self.variables.is_empty() {
            return Ok(());
        }
        Err(self.variables.len())
    }
}

impl<T: Field> Folder<T> for UnconstrainedVariableDetector {
    fn fold_argument(&mut self, p: Parameter) -> Parameter {
        p
    }
    fn fold_variable(&mut self, v: Variable) -> Variable {
        self.variables.remove(&v);
        v
    }
    fn fold_directive(&mut self, d: Directive<T>) -> Directive<T> {
        self.variables.extend(d.outputs.iter());
        d
    }
}
