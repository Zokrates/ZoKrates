use ir::*;
use zokrates_field::field::Field;

// A memory layout for a program
// The ~one variable is not counted in variable_count
#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
pub struct Layout {
    pub variable_count: usize,
    pub public_count: usize,
    pub outputs_count: usize,
}

impl Layout {
    fn new(variable_count: usize, public_count: usize, outputs_count: usize) -> Self {
        assert!(variable_count >= public_count + outputs_count);
        Layout {
            variable_count,
            public_count,
            outputs_count,
        }
    }

    fn private_count(&self) -> usize {
        self.variable_count - self.public_count - self.outputs_count
    }

    pub fn public_count(&self) -> usize {
        self.public_count + self.outputs_count
    }

    pub fn from_prog<T: Field>(p: &Prog<T>) -> Self {
        let public_count = p.public_arguments_count();
        let outputs_count = p.main.returns.len();
        use std::collections::HashSet;
        let mut variables: HashSet<&Variable> = HashSet::new();
        variables.extend(&p.main.arguments);
        for s in &p.main.statements {
            match s {
                Statement::Constraint(ref quad, ref lin) => {
                    variables.extend(lin.0.keys());
                    variables.extend(quad.left.0.keys());
                    variables.extend(quad.right.0.keys());
                }
                Statement::Directive(ref ds) => {
                    variables.extend(ds.outputs.iter());
                }
            }
        }
        variables.remove(&Variable::One);
        Layout::new(variables.len(), public_count, outputs_count)
    }

    pub fn get_index(&self, v: &Variable) -> usize {
        match *v {
            Variable::One => 0,
            Variable::Public(i) => {
                assert!(i < self.public_count);
                i + 1
            }
            Variable::Output(i) => {
                assert!(i < self.outputs_count);
                i + 1 + self.public_count
            }
            Variable::Private(i) => {
                assert!(i < self.private_count());
                i + 1 + self.public_count + self.outputs_count
            }
        }
    }
}

#[derive(PartialEq, Debug, Eq, Hash, Serialize, Deserialize, Clone)]
pub enum Variable {
    Private(usize),
    Public(usize),
    Output(usize),
    One,
}

impl Variable {
    pub fn is_private(&self) -> bool {
        match self {
            Variable::Private(..) => true,
            _ => false,
        }
    }
}

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Variable::One => write!(f, "~one"),
            Variable::Public(i) => write!(f, "_pub_{}", i),
            Variable::Output(i) => write!(f, "~out_{}", i),
            Variable::Private(i) => write!(f, "_{}", i),
        }
    }
}

impl<T: Field> IncompleteWitness<T> {
    pub fn for_prog(p: &Prog<T>) -> Self {
        let layout = Layout::from_prog(p);
        IncompleteWitness {
            values: vec![None; layout.variable_count + 1],
            layout,
        }
    }

    pub fn insert(&mut self, k: Variable, v: T) {
        assert_eq!(self.values[self.layout.get_index(&k)], None);
        self.values[self.layout.get_index(&k)] = Some(v);
    }

    pub fn get(&self, k: &Variable) -> &Option<T> {
        &self.values[self.layout.get_index(k)]
    }
}

impl<T: Field> Witness<T> {
    pub fn get(&self, k: &Variable) -> Option<&T> {
        self.values.get(self.layout.get_index(k))
    }

    pub fn outputs(&self) -> &[T] {
        let l = &self.layout;
        let start = l.public_count + 1;
        let size = l.outputs_count;
        &self.values[start..start + size]
    }

    pub fn public(&self) -> &[T] {
        let l = &self.layout;
        let start = 1;
        let size = l.public_count;
        &self.values[start..start + size]
    }

    pub fn private(&self) -> &[T] {
        let l = &self.layout;
        let start = l.public_count + l.outputs_count + 1;
        let size = l.variable_count - l.public_count - l.outputs_count;
        &self.values[start..start + size]
    }

    pub fn one(&self) -> &T {
        &self.values[0]
    }

    pub fn format_outputs(&self) -> String {
        self.outputs()
            .iter()
            .map(|x| format!("{}", x))
            .collect::<Vec<_>>()
            .join("\n")
    }
}

impl<T: Field> From<IncompleteWitness<T>> for Witness<T> {
    fn from(iw: IncompleteWitness<T>) -> Witness<T> {
        Witness {
            values: iw.values.into_iter().map(|x| x.unwrap()).collect(),
            layout: iw.layout,
        }
    }
}

impl<T: Field> fmt::Display for Witness<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            &[
                "PUBLIC INPUTS",
                &self
                    .public()
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join("\n"),
                "PUBLIC OUTPUTS",
                &self
                    .outputs()
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join("\n"),
                "PRIVATE",
                &self
                    .private()
                    .iter()
                    .map(|x| x.to_string())
                    .collect::<Vec<_>>()
                    .join("\n")
            ]
            .join("\n")
        )
    }
}

#[derive(Serialize, Deserialize, Debug)]
pub struct IncompleteWitness<T: Field> {
    layout: Layout,
    values: Vec<Option<T>>,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct Witness<T: Field> {
    layout: Layout,
    values: Vec<T>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    #[test]
    fn witness() {
        let l = Layout::new(3, 2, 1);
        let w = Witness {
            values: vec![
                FieldPrime::from(1),
                FieldPrime::from(2),
                FieldPrime::from(3),
                FieldPrime::from(4),
            ],
            layout: l,
        };

        assert_eq!(w.get(&Variable::Output(0)), Some(&FieldPrime::from(4)));
        assert_eq!(w.outputs(), &[FieldPrime::from(4)]);
        assert_eq!(w.public(), &[FieldPrime::from(2), FieldPrime::from(3)]);
        assert_eq!(w.private(), &[]);
    }

    #[test]
    fn from_prog() {
        let p: Prog<FieldPrime> = Prog {
            main: Function {
                id: "main".to_string(),
                statements: vec![],
                arguments: vec![],
                returns: vec![],
            },
        };
        assert_eq!(Layout::from_prog(&p), Layout::new(0, 0, 0));

        let p: Prog<FieldPrime> = Prog {
            main: Function {
                id: "main".to_string(),
                statements: vec![Statement::Constraint(
                    QuadComb::from_linear_combinations(
                        Variable::Private(42).into(),
                        Variable::Private(33).into(),
                    ),
                    Variable::Private(22).into(),
                )],
                arguments: vec![Variable::Private(42), Variable::Public(33)],
                returns: vec![Variable::Private(22).into()],
            },
        };
        assert_eq!(Layout::from_prog(&p), Layout::new(3, 1, 1),);

        let p: Prog<FieldPrime> = Prog {
            main: Function {
                id: "main".to_string(),
                statements: vec![Statement::Constraint(
                    QuadComb::from_linear_combinations(
                        LinComb::from(Variable::Private(42)) + Variable::Private(33).into(),
                        Variable::One.into(),
                    ),
                    Variable::Private(22).into(),
                )],
                arguments: vec![Variable::Public(42), Variable::Public(33)],
                returns: vec![Variable::Private(22).into()],
            },
        };
        assert_eq!(Layout::from_prog(&p), Layout::new(3, 0, 1),);
    }
}
