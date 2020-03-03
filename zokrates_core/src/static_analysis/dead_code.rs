use std::collections::HashSet;
use std::marker::PhantomData;
use typed_absy::folder::*;
use typed_absy::*;
use zokrates_field::field::Field;

enum Mode {
    Add,
    Check,
    Ignore,
}

impl Default for Mode {
    fn default() -> Self {
        Mode::Check
    }
}

pub struct DeadCodeAnalyser<'ast, T: Field> {
    used: HashSet<Identifier<'ast>>,
    mode: Mode,
    phantom: PhantomData<T>,
    errors: Vec<Identifier<'ast>>,
}

impl<'ast, T: Field> Default for DeadCodeAnalyser<'ast, T> {
    fn default() -> Self {
        DeadCodeAnalyser {
            used: HashSet::default(),
            mode: Mode::default(),
            phantom: PhantomData,
            errors: vec![],
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Error<'ast, T: Field> {
    pub(crate) program: TypedProgram<'ast, T>,
    pub(crate) identifiers: Vec<Identifier<'ast>>,
}

impl<'ast, T: Field> DeadCodeAnalyser<'ast, T> {
    pub fn analyse(p: TypedProgram<'ast, T>) -> Result<TypedProgram<'ast, T>, Error<'ast, T>> {
        let mut analyser = DeadCodeAnalyser::default();
        let p = analyser.fold_program(p);
        match analyser.errors.len() {
            0 => Ok(p),
            _ => Err(Error {
                program: p,
                identifiers: analyser.errors,
            }),
        }
    }
}

impl<'ast, T: Field> Folder<'ast, T> for DeadCodeAnalyser<'ast, T> {
    fn fold_function(&mut self, f: TypedFunction<'ast, T>) -> TypedFunction<'ast, T> {
        self.used = HashSet::default();
        let statements = f
            .statements
            .into_iter()
            .rev()
            .map(|s| self.fold_statement(s))
            .flat_map(|x| x)
            .rev()
            .collect();

        TypedFunction { statements, ..f }
    }

    fn fold_statement(&mut self, s: TypedStatement<'ast, T>) -> Vec<TypedStatement<'ast, T>> {
        match s {
            TypedStatement::Return(e) => {
                self.mode = Mode::Add;
                fold_statement(self, TypedStatement::Return(e))
            }
            TypedStatement::Condition(left, right) => {
                self.mode = Mode::Add;
                fold_statement(self, TypedStatement::Condition(left, right))
            }
            TypedStatement::Definition(a, e) => {
                self.mode = Mode::Check;
                let a = self.fold_assignee(a);
                self.mode = Mode::Add;
                let e = self.fold_expression(e);
                vec![TypedStatement::Definition(a, e)]
            }
            TypedStatement::MultipleDefinition(vars, e) => {
                self.mode = Mode::Check;
                let vars = vars.into_iter().map(|v| self.fold_variable(v)).collect();
                self.mode = Mode::Add;
                let e = self.fold_expression_list(e);
                vec![TypedStatement::MultipleDefinition(vars, e)]
            }
            TypedStatement::Declaration(v) => {
                self.mode = Mode::Ignore;
                fold_statement(self, TypedStatement::Declaration(v))
            }
            TypedStatement::For(..) => unreachable!(),
        }
    }

    fn fold_name(&mut self, i: Identifier<'ast>) -> Identifier<'ast> {
        match self.mode {
            Mode::Add => {
                self.used.insert(i.clone());
            }
            Mode::Check => {
                if !self.used.contains(&i) {
                    self.errors.push(i.clone());
                }
                self.used.insert(i.clone());
            }
            Mode::Ignore => {}
        };

        i
    }
}

#[cfg(test)]
mod tests {
    use self::types::FunctionKey;
    use super::*;
    use zokrates_field::field::FieldPrime;

    fn wrap<'ast, T: Field>(f: TypedFunction<'ast, T>) -> TypedProgram<'ast, T> {
        TypedProgram {
            modules: vec![(
                "main".into(),
                TypedModule {
                    functions: vec![(
                        FunctionKey::with_id("main").signature(f.signature.clone()),
                        TypedFunctionSymbol::Here(f),
                    )]
                    .into_iter()
                    .collect(),
                },
            )]
            .into_iter()
            .collect(),
            main: "main".into(),
        }
    }

    #[test]
    fn remove_unused_def() {
        // def main() -> ():
        // 	field a = 10
        // 	bool b = foo()
        // 	bool[2][2] c = [[false, false], [false, false]]
        // 	return

        // should return the error
        // [a, b, c]

        let f = TypedFunction {
            arguments: vec![],
            signature: Signature::new(),
            statements: vec![
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element("a".into())),
                    FieldElementExpression::Number(FieldPrime::from(10)).into(),
                ),
                TypedStatement::MultipleDefinition(
                    vec![Variable::field_element("b".into())],
                    TypedExpressionList::FunctionCall(
                        FunctionKey::with_id("foo")
                            .signature(Signature::new().outputs(vec![Type::Boolean])),
                        vec![],
                        vec![Type::Boolean],
                    ),
                ),
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::with_id_and_type(
                        "c".into(),
                        Type::array(Type::array(Type::Boolean, 2), 2),
                    )),
                    ArrayExpressionInner::Value(vec![
                        ArrayExpressionInner::Value(
                            vec![BooleanExpression::Value(false).into(); 2]
                        )
                        .annotate(Type::Boolean, 2)
                        .into();
                        2
                    ])
                    .annotate(Type::array(Type::Boolean, 2), 2)
                    .into(),
                ),
                TypedStatement::Return(vec![]),
            ],
        };

        let res = DeadCodeAnalyser::analyse(wrap(f.clone()));

        assert_eq!(
            res,
            Err(Error {
                program: wrap(f),
                identifiers: vec!["a".into(), "b".into(), "c".into()]
            })
        );
    }
}
