use ir::*;
use zokrates_field::field::Field;

#[derive(Serialize, Deserialize)]
struct Layout {
    variable_count: usize,
    public_count: usize,
    outputs_count: usize,
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

    fn from_prog<T: Field>(p: &Prog<T>) -> Self {
        let public_count = p.private.iter().filter(|p| !*p).count();
        let outputs_count = p.main.returns.len();
        use std::collections::HashSet;
        let mut variables: HashSet<FlatVariable> = HashSet::new();
        for a in &p.main.arguments {
            variables.insert(*a);
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
        variables.remove(&FlatVariable::one());
        Layout::new(variables.len(), public_count, outputs_count)
    }
}

#[derive(PartialEq, Debug, Eq, Hash)]
enum Variable {
    Private(usize),
    Public(usize),
    Output(usize),
    One,
}

impl Variable {
    fn get_index(&self, l: &Layout) -> usize {
        match *self {
            Variable::One => 0,
            Variable::Public(i) => {
                assert!(i < l.public_count);
                i + 1
            }
            Variable::Output(i) => {
                assert!(i < l.outputs_count);
                i + 1 + l.public_count
            }
            Variable::Private(i) => {
                assert!(i < l.private_count());
                i + 1 + l.public_count + l.outputs_count
            }
        }
    }
}

#[derive(Serialize, Deserialize)]
struct Witness<T: Field>(Vec<T>);

#[derive(Debug, PartialEq)]
struct WitnessMap<T: Field>(HashMap<Variable, T>);
impl<T: Field> WitnessMap<T> {
    fn from_witness_with_layout(w: Witness<T>, l: &Layout) -> Self {
        WitnessMap(
            w.0.into_iter()
                .enumerate()
                .map(|(index, value)| {
                    if index == 0 {
                        (Variable::One, value)
                    } else if index < l.public_count + 1 {
                        (Variable::Public(index - 1), value)
                    } else if index < l.public_count + l.outputs_count + 1 {
                        (Variable::Output(index - l.public_count - 1), value)
                    } else {
                        (
                            Variable::Private(index - l.public_count - l.outputs_count - 1),
                            value,
                        )
                    }
                })
                .collect::<HashMap<_, _>>(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    #[test]
    fn witness_to_map() {
        let l = Layout::new(3, 2, 1);
        let wm = WitnessMap(
            vec![
                (Variable::One, FieldPrime::from(1)),
                (Variable::Public(0), FieldPrime::from(1)),
                (Variable::Public(1), FieldPrime::from(1)),
                (Variable::Output(0), FieldPrime::from(1)),
            ]
            .into_iter()
            .collect(),
        );
        let w = Witness(vec![
            FieldPrime::from(1),
            FieldPrime::from(1),
            FieldPrime::from(1),
            FieldPrime::from(1),
        ]);

        //assert_eq!(WitnessMap::from_witness_with_layout(w, &l), wm);
        println!("{:?}", WitnessMap::from_witness_with_layout(w, &l));
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
        );
        assert_eq!(Variable::One.get_index(&l), 0);
        assert_eq!(Variable::Private(1).get_index(&l), 2);
        assert_eq!(Variable::Private(2).get_index(&l), 3);
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
                        FlatVariable::new(42).into(),
                        FlatVariable::new(33).into(),
                    ),
                    FlatVariable::new(22).into(),
                )],
                arguments: vec![FlatVariable::new(42), FlatVariable::new(33)],
                returns: vec![FlatVariable::new(22).into()],
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
                        LinComb::from(FlatVariable::new(42)) + FlatVariable::new(33).into(),
                        FlatVariable::one().into(),
                    ),
                    FlatVariable::new(22).into(),
                )],
                arguments: vec![FlatVariable::new(42), FlatVariable::new(33)],
                returns: vec![FlatVariable::new(22).into()],
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
