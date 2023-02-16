use crate::ir::folder::Folder;
use crate::ir::DirectiveStatement;
use crate::ir::Parameter;
use crate::ir::ProgIterator;
use crate::ir::Statement;
use crate::ir::Variable;
use std::collections::HashSet;
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
    fn fold_directive_statement(&mut self, d: DirectiveStatement<T>) -> Vec<Statement<T>> {
        self.variables.extend(d.outputs.iter());
        vec![Statement::Directive(d)]
    }
}
