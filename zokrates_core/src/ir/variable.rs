use ir::*;
use zokrates_field::field::Field;

#[derive(Serialize, Deserialize, Debug, Clone)]
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

    fn variables(&self) -> Vec<Variable> {
        std::iter::once(Variable::One)
            .chain((0..self.public_count).map(|i| Variable::Public(i)))
            .chain((0..self.outputs_count).map(|i| Variable::Output(i)))
            .chain(
                (0..(self.variable_count - self.public_count - self.outputs_count))
                    .map(|i| Variable::Private(i)),
            )
            .collect()
    }

    fn private_count(&self) -> usize {
        self.variable_count - self.public_count - self.outputs_count
    }

    pub fn public_count(&self) -> usize {
        self.public_count + self.outputs_count
    }

    pub fn from_prog<T: Field>(p: &Prog<T>) -> Self {
        let public_count = p.private.iter().filter(|p| !*p).count();
        let outputs_count = p.main.returns.len();
        use std::collections::HashSet;
        let mut variables: HashSet<&Variable> = HashSet::new();
        for a in &p.main.arguments {
            variables.insert(a);
        }
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

#[derive(PartialEq, Debug, Eq, Hash, Serialize, Deserialize, Clone, Ord)]
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

use std::cmp::Ordering;

impl PartialOrd for Variable {
    fn partial_cmp(&self, other: &Variable) -> Option<Ordering> {
        match (self, other) {
            (Variable::One, Variable::One) => Some(Ordering::Equal),
            (Variable::One, _) => Some(Ordering::Less),
            (Variable::Public(i), Variable::Public(j)) => i.partial_cmp(&j),
            _ => unimplemented!(),
        }
    }
}

impl<T: Field> Witness<T> {
    fn outputs(&self) -> Vec<T> {
        let l = &self.layout;
        let start = l.public_count + 1;
        let size = l.outputs_count;
        self.values[start..start + size]
            .iter()
            .map(|x| x.clone().unwrap())
            .collect()
    }

    fn public(&self) -> Vec<T> {
        let l = &self.layout;
        let start = 1;
        let size = l.public_count;
        self.values[start..start + size]
            .iter()
            .map(|x| x.clone().unwrap())
            .collect()
    }

    fn private(&self) -> Vec<T> {
        let l = &self.layout;
        let start = l.public_count + l.outputs_count + 1;
        let size = l.variable_count - l.public_count - l.outputs_count;
        self.values[start..start + size]
            .iter()
            .map(|x| x.clone().unwrap())
            .collect()
    }

    pub fn format_outputs(&self) -> String {
        self.outputs()
            .iter()
            .map(|x| format!("{}", x))
            .collect::<Vec<_>>()
            .join("\n")
    }

    pub fn for_prog(p: &Prog<T>) -> Self {
        let layout = Layout::from_prog(p);
        Witness {
            values: vec![None; layout.variable_count + 1],
            layout,
        }
    }

    pub fn insert(&mut self, k: Variable, v: T) -> Option<T> {
        self.values[self.layout.get_index(&k)] = Some(v);
        // TODO check not only set
        None
    }

    pub fn get(&self, k: &Variable) -> Option<T> {
        self.values[self.layout.get_index(k)].clone()
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
pub struct Witness<T: Field> {
    layout: Layout,
    values: Vec<Option<T>>,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct FullWitness<T: Field> {
    layout: Layout,
    values: Vec<T>,
}

impl<T: Field> From<Witness<T>> for FullWitness<T> {
    fn from(w: Witness<T>) -> FullWitness<T> {
        FullWitness {
            layout: w.layout,
            values: w.values.into_iter().map(|x| x.unwrap()).collect(),
        }
    }
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
            ]
            .into_iter()
            .map(|x| Some(x))
            .collect(),
            layout: l,
        };

        assert_eq!(w.get(&Variable::Output(0)), Some(FieldPrime::from(4)));
        assert_eq!(w.outputs(), &[FieldPrime::from(4)]);
        assert_eq!(w.public(), &[FieldPrime::from(2), FieldPrime::from(3)]);
        assert_eq!(w.private(), &[]);
    }

    #[test]
    fn test() {
        let l = Layout::new(0, 0, 0);
        assert_eq!(l.variables(), vec![Variable::One]);
        let l = Layout::new(3, 0, 0);
        assert_eq!(
            l.variables(),
            vec![
                Variable::One,
                Variable::Private(0),
                Variable::Private(1),
                Variable::Private(2),
            ]
            .into_iter()
            .map(|x| Some(x))
            .collect()
        );
        assert_eq!(l.get_index(&Variable::One), 0);
        assert_eq!(l.get_index(&Variable::Private(1)), 2);
        assert_eq!(l.get_index(&Variable::Private(2)), 3);
        let l = Layout::new(3, 2, 1);
        assert_eq!(
            l.variables(),
            vec![
                Variable::One,
                Variable::Public(0),
                Variable::Public(1),
                Variable::Output(0),
            ]
        );
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
            private: vec![],
        };
        assert_eq!(Layout::from_prog(&p).variables(), vec![Variable::One,],);

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
                arguments: vec![Variable::Private(42), Variable::Private(33)],
                returns: vec![Variable::Private(22).into()],
            },
            private: vec![true, false],
        };
        assert_eq!(
            Layout::from_prog(&p).variables(),
            vec![
                Variable::One,
                Variable::Public(0),
                Variable::Output(0),
                Variable::Private(0)
            ],
        );

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
                arguments: vec![Variable::Private(42), Variable::Private(33)],
                returns: vec![Variable::Private(22).into()],
            },
            private: vec![true, true],
        };
        assert_eq!(
            Layout::from_prog(&p).variables(),
            vec![
                Variable::One,
                Variable::Output(0),
                Variable::Private(0),
                Variable::Private(1),
            ],
        );
    }
}
