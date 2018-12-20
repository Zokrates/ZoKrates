//! Module containing the `Flattener` to process a program that it is R1CS-able.
//!
//! @file flatten.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

mod bool;
mod field;
mod field_array;

use absy::parameter::Parameter;
use absy::variable::Variable;
use bimap::BiMap;
use field::Field;
use flat_absy::*;
use helpers::DirectiveStatement;
use std::collections::HashMap;
use typed_absy::*;
use types::conversions::cast;
use types::Signature;
use types::Type;

/// Flattener, computes flattened program.
#[derive(Debug)]
pub struct Flattener<T: Field> {
    /// Map of renamings for reassigned variables while processing the program.
    substitution: HashMap<FlatVariable, FlatVariable>,
    /// Index of the next introduced variable while processing the program.
    next_var_idx: usize,
    /// Map of correspondence between zokrates variables and wires
    bijection: BiMap<String, FlatVariable>,
    /// Vector of
    functions_flattened: Vec<FlatFunction<T>>,
}
impl<T: Field> Flattener<T> {
    /// Returns a `Flattener` with fresh a fresh [substitution] and [variables].
    ///
    /// # Arguments
    ///
    /// * `bits` - Number of bits needed to represent the maximum value.
    fn new() -> Flattener<T> {
        Flattener {
            substitution: HashMap::new(),
            next_var_idx: 0,
            bijection: BiMap::new(),
            functions_flattened: Vec::new(),
        }
    }

    pub fn flatten(prog: TypedProg<T>) -> FlatProg<T> {
        Self::new().flatten_program(prog)
    }

    /// Loads the code library
    fn load_corelib(&mut self) -> () {
        // Load type casting functions
        self.push_function(cast(&Type::Boolean, &Type::FieldElement));
        self.push_function(cast(&Type::FieldElement, &Type::Boolean));

        // Load IfElse helper
        let ie = TypedFunction {
            id: "_if_else_field".to_string(),
            arguments: vec![
                Parameter {
                    id: Variable {
                        id: "condition".to_string(),
                        _type: Type::Boolean,
                    },
                    private: true,
                },
                Parameter {
                    id: Variable {
                        id: "consequence".to_string(),
                        _type: Type::FieldElement,
                    },
                    private: true,
                },
                Parameter {
                    id: Variable {
                        id: "alternative".to_string(),
                        _type: Type::FieldElement,
                    },
                    private: true,
                },
            ],
            statements: vec![
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element("condition_as_field")),
                    FieldElementExpression::FunctionCall(
                        "_bool_to_field".to_string(),
                        vec![BooleanExpression::Identifier("condition".to_string()).into()],
                    )
                    .into(),
                ),
                TypedStatement::Return(vec![FieldElementExpression::Add(
                    box FieldElementExpression::Mult(
                        box FieldElementExpression::Identifier("condition_as_field".to_string()),
                        box FieldElementExpression::Identifier("consequence".to_string()),
                    ),
                    box FieldElementExpression::Mult(
                        box FieldElementExpression::Sub(
                            box FieldElementExpression::Number(T::one()),
                            box FieldElementExpression::Identifier(
                                "condition_as_field".to_string(),
                            ),
                        ),
                        box FieldElementExpression::Identifier("alternative".to_string()),
                    ),
                )
                .into()]),
            ],
            signature: Signature::new()
                .inputs(vec![Type::Boolean, Type::FieldElement, Type::FieldElement])
                .outputs(vec![Type::FieldElement]),
        };

        let ief = self.flatten_function(ie);
        self.push_function(ief);
    }

    fn flatten_function_call(
        &mut self,
        id: &String,
        return_types: Vec<Type>,
        param_expressions: Vec<TypedExpression<T>>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
    ) -> FlatExpressionList<T> {
        let passed_signature = Signature::new()
            .inputs(param_expressions.iter().map(|e| e.get_type()).collect())
            .outputs(return_types);

        let funct = self.get_function(passed_signature, id).clone();

        let mut replacement_map = HashMap::new();

        // Handle complex parameters and assign values:
        // Rename Parameters, assign them to values in call. Resolve complex expressions with definitions
        let params_flattened = param_expressions
            .into_iter()
            .map(|param_expr| self.flatten_expression(param_expr, statements_flattened))
            .into_iter()
            .flat_map(|x| x)
            .collect::<Vec<_>>();

        let params_flattened = params_flattened
            .into_iter()
            .map(|e| e.apply_recursive_substitution(&self.substitution))
            .collect::<Vec<_>>();

        for (concrete_argument, formal_argument) in
            params_flattened.into_iter().zip(funct.arguments)
        {
            let new_var = self.use_sym();
            statements_flattened.push(FlatStatement::Definition(new_var, concrete_argument));
            replacement_map.insert(formal_argument.id, new_var);
        }

        // Ensure Renaming and correct returns:
        // add all flattened statements, adapt return statement

        let (return_statements, statements): (Vec<_>, Vec<_>) =
            funct.statements.into_iter().partition(|s| match s {
                FlatStatement::Return(..) => true,
                _ => false,
            });

        let statements: Vec<_> = statements
            .into_iter()
            .map(|stat| match stat {
                // set return statements right sidreturne as expression result
                FlatStatement::Return(..) => unreachable!(),
                FlatStatement::Definition(var, rhs) => {
                    let new_var = self.issue_new_variable();
                    replacement_map.insert(var, new_var);
                    let new_rhs = rhs.apply_direct_substitution(&replacement_map);
                    FlatStatement::Definition(new_var, new_rhs)
                }
                FlatStatement::Condition(lhs, rhs) => {
                    let new_lhs = lhs.apply_direct_substitution(&replacement_map);
                    let new_rhs = rhs.apply_direct_substitution(&replacement_map);
                    FlatStatement::Condition(new_lhs, new_rhs)
                }
                FlatStatement::Directive(d) => {
                    let new_outputs = d
                        .outputs
                        .into_iter()
                        .map(|o| {
                            let new_o = self.issue_new_variable();
                            replacement_map.insert(o, new_o);
                            new_o
                        })
                        .collect();
                    let new_inputs = d
                        .inputs
                        .into_iter()
                        .map(|i| i.apply_direct_substitution(&replacement_map))
                        .collect();
                    FlatStatement::Directive(DirectiveStatement {
                        outputs: new_outputs,
                        helper: d.helper,
                        inputs: new_inputs,
                    })
                }
            })
            .collect();

        statements_flattened.extend(statements);

        match return_statements[0].clone() {
            FlatStatement::Return(list) => FlatExpressionList {
                expressions: list
                    .expressions
                    .into_iter()
                    .map(|x| x.apply_direct_substitution(&replacement_map))
                    .collect(),
            },
            _ => unreachable!(),
        }
    }

    fn flatten_expression(
        &mut self,
        expr: TypedExpression<T>,
        statements_flattened: &mut Vec<FlatStatement<T>>,
    ) -> Vec<FlatExpression<T>> {
        match expr {
            TypedExpression::FieldElement(e) => {
                vec![self.flatten_field_expression(e, statements_flattened)]
            }
            TypedExpression::Boolean(e) => {
                vec![self.flatten_boolean_expression(e, statements_flattened)]
            }
            TypedExpression::FieldElementArray(e) => {
                self.flatten_field_array_expression(e, statements_flattened)
            }
        }
    }

    fn flatten_statement(&mut self, stat: TypedStatement<T>) -> Vec<FlatStatement<T>> {
        let mut statements_flattened = vec![];

        let statements = match stat {
            TypedStatement::Return(exprs) => {
                let flat_expressions = exprs
                    .into_iter()
                    .map(|expr| self.flatten_expression(expr, &mut statements_flattened))
                    .flat_map(|x| x)
                    .collect::<Vec<_>>();

                let flat_expressions = flat_expressions
                    .into_iter()
                    .map(|e| e.apply_recursive_substitution(&self.substitution))
                    .collect();

                vec![FlatStatement::Return(FlatExpressionList {
                    expressions: flat_expressions,
                })]
            }
            TypedStatement::Declaration(_) => {
                // declarations have already been checked
                vec![]
            }
            TypedStatement::Definition(assignee, expr) => {
                // define n variables with n the number of primitive types for v_type
                // assign them to the n primitive types for expr

                match (&assignee, expr.get_type()) {
                    (TypedAssignee::ArrayElement(ref array, ref index), Type::FieldElement) => {

                                        let rhs = self.flatten_expression(expr.clone(), &mut statements_flattened)
                    .into_iter()
                    .map(|e| e.apply_recursive_substitution(&self.substitution))
                    .collect::<Vec<_>>();
                               let expr = match expr {
                                    TypedExpression::FieldElement(e) => e,
                                    _ => unreachable!()
                                };
                                match index {
                                    box FieldElementExpression::Number(n) => {
                                        match array {
                                            box TypedAssignee::Identifier(id) => {
                                                let debug_name = format!("{}_c{}", id.id, n);
                                                let var = self.use_variable(&debug_name);
                                                // handle return of function call
                                                let var_to_replace =
                                                    self.get_latest_var_substitution(&debug_name);
                                                if !(var == var_to_replace)
                                                    && !self
                                                        .substitution
                                                        .contains_key(&var_to_replace)
                                                {
                                                    self.substitution.insert(
                                                        var_to_replace.clone(),
                                                        var.clone(),
                                                    );
                                                }
                                                vec![FlatStatement::Definition(var, rhs[0].clone())]
                                            }
                                            _ => panic!("no multidimension array for now"),
                                        }
                                    }
                                    box e => {
                                        // we have array[e] with e an arbitrary expression
                                        // first we check that e is in 0..array.len(), so we check that sum(if e == i then 1 else 0) == 1
                                        // here depending on the size, we could use a proper range check based on bits
                                        let size = match array.get_type() {
                                            Type::FieldElementArray(n) => n,
                                            _ => panic!("checker should generate array element based on non array")
                                        };
                                        let range_check = (0..size)
                                            .map(|i| {
                                                FieldElementExpression::IfElse(
                                                    box BooleanExpression::Eq(
                                                        box e.clone(),
                                                        box FieldElementExpression::Number(
                                                            T::from(i),
                                                        ),
                                                    ),
                                                    box FieldElementExpression::Number(T::from(1)),
                                                    box FieldElementExpression::Number(T::from(0)),
                                                )
                                            })
                                            .fold(
                                                FieldElementExpression::Number(T::from(0)),
                                                |acc, e| {
                                                    FieldElementExpression::Add(box acc, box e)
                                                },
                                            );

                                        let range_check_statement = TypedStatement::Condition(
                                            FieldElementExpression::Number(T::from(1)).into(),
                                            range_check.into(),
                                        );

                                        let range_check = self.flatten_statement(
                                            range_check_statement,
                                        );

                                        // now we redefine the whole array, updating only the piece that changed
                                        // stat(array[i] = if e == i then `expr` else `array[i]`)
                                        let redefinitions: Vec<FlatStatement<_>> = (0..size).map(|i| {
                                            let rhs = FieldElementExpression::IfElse(
                                                box BooleanExpression::Eq(
                                                    box e.clone(),
                                                    box FieldElementExpression::Number(T::from(i)),
                                                ),
                                                box expr.clone(),
                                                box e.clone(),
                                            );

                                            let rhs_flattened = self.flatten_field_expression(
                                                rhs,
                                                &mut statements_flattened,
                                            );

                                            let var =
                                                self.use_variable(&format!("{}_c{}", array, i));

                                            FlatStatement::Definition(
                                                var,
                                                rhs_flattened,
                                            )
                                        }).collect();

                                        range_check.into_iter().chain(redefinitions).collect()
                                    }
                                }
                    },
                    (TypedAssignee::Identifier(ref v), ref t) => {
                                        let rhs = self.flatten_expression(expr, &mut statements_flattened)
                    .into_iter()
                    .map(|e| e.apply_recursive_substitution(&self.substitution))
                    .collect::<Vec<_>>();
                        match t.get_primitive_count() {
                            1 => {
                                let debug_name = v.clone().id;
                                let var = self.use_variable(&debug_name);
                                // handle return of function call
                                let var_to_replace = self.get_latest_var_substitution(&debug_name);
                                if !(var == var_to_replace)
                                    && !self.substitution.contains_key(&var_to_replace)
                                {
                                    self.substitution
                                        .insert(var_to_replace, var.clone());
                                }
                                vec![FlatStatement::Definition(var, rhs[0].clone())]
                            },
                            _ => {
                                rhs.into_iter().enumerate().map(|(index, r)| {
                                    let debug_name = match assignee {
                                        TypedAssignee::Identifier(ref v) => format!("{}_c{}", v.id, index),
                                        _ => unimplemented!(),
                                    };
                                    let var = self.use_variable(&debug_name);
                                    // handle return of function call
                                    let var_to_replace = self.get_latest_var_substitution(&debug_name);
                                    if !(var == var_to_replace)
                                        && !self.substitution.contains_key(&var_to_replace)
                                    {
                                        self.substitution
                                            .insert(var_to_replace, var.clone());
                                    }
                                    FlatStatement::Definition(var, r)
                                }).collect()
                            }
                        }
                    },
                    (TypedAssignee::ArrayElement(..), t) => unimplemented!("array of {} not supported, cannot assign element. Should have been caught at semantic phase", t)
                }
            }
            TypedStatement::Condition(expr1, expr2) => {
                // flatten expr1 and expr2 to n flattened expressions with n the number of primitive types for expr1
                // add n conditions to check equality of the n expressions

                match (expr1, expr2) {
                    (TypedExpression::FieldElement(e1), TypedExpression::FieldElement(e2)) => {
                        let (lhs, rhs) = (
                            self.flatten_field_expression(e1, &mut statements_flattened)
                                .apply_recursive_substitution(&self.substitution),
                            self.flatten_field_expression(e2, &mut statements_flattened)
                                .apply_recursive_substitution(&self.substitution),
                        );

                        let statement = if lhs.is_linear() {
                            FlatStatement::Condition(lhs, rhs)
                        } else if rhs.is_linear() {
                            // swap so that left side is linear
                            FlatStatement::Condition(rhs, lhs)
                        } else {
                            unimplemented!()
                        };

                        vec![statement]
                    }
                    (TypedExpression::Boolean(e1), TypedExpression::Boolean(e2)) => {
                        let (lhs, rhs) = (
                            self.flatten_boolean_expression(e1, &mut statements_flattened)
                                .apply_recursive_substitution(&self.substitution),
                            self.flatten_boolean_expression(e2, &mut statements_flattened)
                                .apply_recursive_substitution(&self.substitution),
                        );

                        let statement = if lhs.is_linear() {
                            FlatStatement::Condition(lhs, rhs)
                        } else if rhs.is_linear() {
                            // swap so that left side is linear
                            FlatStatement::Condition(rhs, lhs)
                        } else {
                            unimplemented!()
                        };

                        vec![statement]
                    }
                    (
                        TypedExpression::FieldElementArray(e1),
                        TypedExpression::FieldElementArray(e2),
                    ) => {
                        let (lhs, rhs) = (
                            self.flatten_field_array_expression(e1, &mut statements_flattened)
                                .into_iter()
                                .map(|e| e.apply_recursive_substitution(&self.substitution))
                                .collect::<Vec<_>>(),
                            self.flatten_field_array_expression(e2, &mut statements_flattened)
                                .into_iter()
                                .map(|e| e.apply_recursive_substitution(&self.substitution))
                                .collect::<Vec<_>>(),
                        );

                        assert_eq!(lhs.len(), rhs.len());

                        lhs.into_iter()
                            .zip(rhs.into_iter())
                            .map(|(l, r)| {
                                if l.is_linear() {
                                    FlatStatement::Condition(l, r)
                                } else if r.is_linear() {
                                    // swap so that left side is linear
                                    FlatStatement::Condition(r, l)
                                } else {
                                    unimplemented!()
                                }
                            })
                            .collect()
                    }
                    _ => panic!(
                        "non matching types in condition should have been caught at semantic stage"
                    ),
                }
            }
            TypedStatement::For(..) => unreachable!("for loops should already have been unrolled"),
            TypedStatement::MultipleDefinition(vars, rhs) => {
                // flatten the right side to p = sum(var_i.type.primitive_count) expressions
                // define p new variables to the right side expressions

                let var_types = vars.iter().map(|v| v.get_type()).collect();

                match rhs {
                    TypedExpressionList::FunctionCall(fun_id, exprs, _) => {
                        let rhs_flattened = self
                            .flatten_function_call(
                                &fun_id,
                                var_types,
                                exprs,
                                &mut statements_flattened,
                            )
                            .apply_recursive_substitution(&self.substitution);

                        let mut iterator = rhs_flattened.expressions.into_iter();

                        // take each new variable being assigned
                        let res = vars
                            .iter()
                            .flat_map(|v|
                            // determine how many field elements it carries
                            match v.get_type().get_primitive_count() {
                                1 => {
                                    let debug_name = &v.id;
                                    let var = self.use_variable(&debug_name);
                                    // handle return of function call
                                    let var_to_replace =
                                        self.get_latest_var_substitution(&debug_name);
                                    if !(var == var_to_replace)
                                        && !self.substitution.contains_key(&var_to_replace)
                                    {
                                        self.substitution
                                            .insert(var_to_replace, var.clone());
                                    }
                                    vec![FlatStatement::Definition(
                                        var,
                                        iterator.next().unwrap(),
                                    )]
                                }
                                size =>
                                    (0..size).map(|index| {
                                        let debug_name = format!("{}_c{}", v.id, index);
                                        let var = self.use_variable(&debug_name);
                                        // handle return of function call
                                        let var_to_replace =
                                            self.get_latest_var_substitution(&debug_name);
                                        if !(var == var_to_replace)
                                            && !self.substitution.contains_key(&var_to_replace)
                                        {
                                            self.substitution
                                                .insert(var_to_replace, var.clone());
                                        }
                                        FlatStatement::Definition(
                                            var,
                                            iterator.next().unwrap(),
                                        )
                                    }).collect()

                            })
                            .collect();
                        // we should have exhausted the return values
                        assert_eq!(iterator.next(), None);
                        res
                    }
                }
            }
        };

        statements_flattened
            .into_iter()
            .chain(statements.into_iter())
            .collect()
    }

    fn push_function(&mut self, f: FlatFunction<T>) -> () {
        self.functions_flattened.push(f);
    }

    fn reset_function_state(&mut self) -> () {
        self.substitution = HashMap::new();
        self.bijection = BiMap::new();
        self.next_var_idx = 0;
    }

    fn get_function(&self, s: Signature, id: &str) -> &FlatFunction<T> {
        self.functions_flattened
            .iter()
            .find(|f| f.id == id && f.signature == s)
            .unwrap()
    }

    /// Returns a flattened `TypedFunction` based on the given `funct`.
    ///
    /// # Arguments
    ///
    /// * `functions_flattened` - Vector where new flattened functions can be added.
    /// * `funct` - `TypedFunction` that will be flattened.
    fn flatten_function(&mut self, funct: TypedFunction<T>) -> FlatFunction<T> {
        self.reset_function_state();

        // push parameters
        let arguments_flattened: Vec<FlatParameter> = funct
            .arguments
            .iter()
            .flat_map(|arg| match arg.id.get_type().get_primitive_count() {
                1 => vec![FlatParameter::new(
                    self.use_variable(&arg.id.id),
                    arg.private,
                )],
                size => (0..size)
                    .map(|i| {
                        FlatParameter::new(
                            self.use_variable(&format!("{}_c{}", arg.id.id, i)),
                            arg.private,
                        )
                    })
                    .collect::<Vec<_>>(),
            })
            .collect();

        // flatten statements in functions and apply substitution
        let statements_flattened = funct
            .statements
            .into_iter()
            .flat_map(|s| self.flatten_statement(s))
            .collect();

        FlatFunction {
            id: funct.id,
            arguments: arguments_flattened,
            statements: statements_flattened,
            signature: funct.signature,
        }
    }

    /// Returns a flattened `Prog`ram based on the given `prog`.
    ///
    /// # Arguments
    ///
    /// * `prog` - `Prog`ram that will be flattened.
    fn flatten_program(mut self, prog: TypedProg<T>) -> FlatProg<T> {
        self.load_corelib();

        for func in prog.imported_functions {
            self.push_function(func);
        }

        for func in prog.functions {
            let flattened_func = self.flatten_function(func);
            self.push_function(flattened_func);
        }

        FlatProg {
            functions: self.functions_flattened,
        }
    }

    /// Checks if the given name is a not used variable and returns a fresh variable.
    /// # Arguments
    ///
    /// * `name` - a String that holds the name of the variable
    fn use_variable(&mut self, name: &String) -> FlatVariable {
        // issue the variable we'll use
        let var = self.issue_new_variable();

        self.bijection.insert(name.to_string(), var);
        var
    }

    fn issue_new_variable(&mut self) -> FlatVariable {
        let var = FlatVariable::new(self.next_var_idx);
        self.next_var_idx += 1;
        var
    }

    fn use_sym(&mut self) -> FlatVariable {
        let name = format!("sym_{}", self.next_var_idx);
        let var = self.issue_new_variable();
        self.bijection.insert(name, var);
        var
    }

    fn get_latest_var_substitution(&mut self, name: &String) -> FlatVariable {
        self.bijection.get_by_left(name).unwrap().clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use absy::variable::Variable;
    use field::FieldPrime;
    use helpers::{Helper, RustHelper};
    use ir::Prog;
    use types::Signature;
    use types::Type;

    impl<T: Field> Flattener<T> {
        fn with_functions(f: Vec<FlatFunction<T>>) -> Flattener<T> {
            let flattener = Flattener::new();
            Flattener {
                functions_flattened: f,
                ..flattener
            }
        }
    }

    #[test]
    fn multiple_definition() {
        // def foo()
        //     return 1, 2
        // def main()
        //     a, b = foo()

        let functions_flattened = vec![FlatFunction {
            id: "foo".to_string(),
            arguments: vec![],
            statements: vec![FlatStatement::Return(FlatExpressionList {
                expressions: vec![
                    FlatExpression::Number(FieldPrime::from(1)),
                    FlatExpression::Number(FieldPrime::from(2)),
                ],
            })],
            signature: Signature::new()
                .inputs(vec![])
                .outputs(vec![Type::FieldElement, Type::FieldElement]),
        }];
        let mut flattener = Flattener::with_functions(functions_flattened);

        let statement = TypedStatement::MultipleDefinition(
            vec![
                Variable::field_element("a".to_string()),
                Variable::field_element("b".to_string()),
            ],
            TypedExpressionList::FunctionCall(
                "foo".to_string(),
                vec![],
                vec![Type::FieldElement, Type::FieldElement],
            ),
        );

        let statements_flattened = flattener.flatten_statement(statement);

        let a = FlatVariable::new(0);

        assert_eq!(
            statements_flattened[0],
            FlatStatement::Definition(a, FlatExpression::Number(FieldPrime::from(1)))
        );
    }

    #[test]
    fn multiple_definition2() {
        // def dup(x)
        //     return x, x
        // def main()
        //     a, b = dup(2)

        let a = FlatVariable::new(0);

        let functions_flattened = vec![FlatFunction {
            id: "dup".to_string(),
            arguments: vec![FlatParameter {
                id: a,
                private: true,
            }],
            statements: vec![FlatStatement::Return(FlatExpressionList {
                expressions: vec![FlatExpression::Identifier(a), FlatExpression::Identifier(a)],
            })],
            signature: Signature::new()
                .inputs(vec![Type::FieldElement])
                .outputs(vec![Type::FieldElement, Type::FieldElement]),
        }];

        let mut flattener = Flattener::with_functions(functions_flattened);

        let statement = TypedStatement::MultipleDefinition(
            vec![
                Variable::field_element("a".to_string()),
                Variable::field_element("b".to_string()),
            ],
            TypedExpressionList::FunctionCall(
                "dup".to_string(),
                vec![TypedExpression::FieldElement(
                    FieldElementExpression::Number(FieldPrime::from(2)),
                )],
                vec![Type::FieldElement, Type::FieldElement],
            ),
        );

        let fun = TypedFunction {
            id: String::from("main"),
            arguments: vec![],
            statements: vec![statement],
            signature: Signature {
                inputs: vec![],
                outputs: vec![],
            },
        };

        let f = flattener.flatten_function(fun);

        let a = FlatVariable::new(0);

        assert_eq!(
            f.statements[0],
            FlatStatement::Definition(a, FlatExpression::Number(FieldPrime::from(2)))
        );
    }

    #[test]
    fn simple_definition() {
        // def foo()
        //     return 1
        // def main()
        //     a = foo()

        let functions_flattened = vec![FlatFunction {
            id: "foo".to_string(),
            arguments: vec![],
            statements: vec![FlatStatement::Return(FlatExpressionList {
                expressions: vec![FlatExpression::Number(FieldPrime::from(1))],
            })],
            signature: Signature::new()
                .inputs(vec![])
                .outputs(vec![Type::FieldElement]),
        }];

        let mut flattener = Flattener::with_functions(functions_flattened);

        let statement = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_element("a")),
            TypedExpression::FieldElement(FieldElementExpression::FunctionCall(
                "foo".to_string(),
                vec![],
            )),
        );

        let statements_flattened = flattener.flatten_statement(statement);

        let a = FlatVariable::new(0);

        assert_eq!(
            statements_flattened[0],
            FlatStatement::Definition(a, FlatExpression::Number(FieldPrime::from(1)))
        );
    }

    #[test]
    fn redefine_argument() {
        // def foo(a)
        //     a = a + 1
        //     return 1

        // should flatten to no redefinition
        // def foo(a)
        //     a_0 = a + 1
        //     return 1

        let mut flattener = Flattener::new();

        let funct = TypedFunction {
            id: "foo".to_string(),
            signature: Signature::new()
                .inputs(vec![Type::FieldElement])
                .outputs(vec![Type::FieldElement]),
            arguments: vec![Parameter {
                id: Variable::field_element("a"),
                private: true,
            }],
            statements: vec![
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element("a")),
                    FieldElementExpression::Add(
                        box FieldElementExpression::Identifier("a".to_string()),
                        box FieldElementExpression::Number(FieldPrime::from(1)),
                    )
                    .into(),
                ),
                TypedStatement::Return(vec![
                    FieldElementExpression::Number(FieldPrime::from(1)).into()
                ]),
            ],
        };

        let flat_funct = flattener.flatten_function(funct);

        let a = FlatVariable::new(0);
        let a_0 = FlatVariable::new(1);

        assert_eq!(
            flat_funct.statements[0],
            FlatStatement::Definition(
                a_0,
                FlatExpression::Add(
                    box FlatExpression::Identifier(a),
                    box FlatExpression::Number(FieldPrime::from(1))
                )
            )
        );
    }

    #[test]
    fn call_with_def() {
        // def foo():
        //     a = 3
        //     return a

        // def main():
        //     return foo()

        let foo = TypedFunction {
            id: String::from("foo"),
            arguments: vec![],
            statements: vec![
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element("a")),
                    FieldElementExpression::Number(FieldPrime::from(3)).into(),
                ),
                TypedStatement::Return(vec![
                    FieldElementExpression::Identifier(String::from("a")).into()
                ]),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![Type::FieldElement],
            },
        };

        let main = TypedFunction {
            id: String::from("main"),
            arguments: vec![],
            statements: vec![TypedStatement::Return(vec![
                FieldElementExpression::FunctionCall(String::from("foo"), vec![]).into(),
            ])],
            signature: Signature {
                inputs: vec![],
                outputs: vec![Type::FieldElement],
            },
        };

        let mut flattener = Flattener::new();

        let foo_flattened = flattener.flatten_function(foo);
        flattener.push_function(foo_flattened);

        let expected = FlatFunction {
            id: String::from("main"),
            arguments: vec![],
            statements: vec![
                FlatStatement::Definition(
                    FlatVariable::new(0),
                    FlatExpression::Number(FieldPrime::from(3)),
                ),
                FlatStatement::Return(FlatExpressionList {
                    expressions: vec![FlatExpression::Identifier(FlatVariable::new(0))],
                }),
            ],
            signature: Signature::new().outputs(vec![Type::FieldElement]),
        };

        let main_flattened = flattener.flatten_function(main);

        assert_eq!(main_flattened, expected);
    }

    #[test]
    fn powers() {
        // def main():
        //     field a = 7
        //     field b = a**4
        //     return b

        // def main():
        //     _0 = 7
        //     _1 = (_0 * _0)
        //     _2 = (_1 * _0)
        //     _3 = (_2 * _0)
        //     return _3

        let function = TypedFunction {
            id: String::from("main"),
            arguments: vec![],
            statements: vec![
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element("a")),
                    FieldElementExpression::Number(FieldPrime::from(7)).into(),
                ),
                TypedStatement::Definition(
                    TypedAssignee::Identifier(Variable::field_element("b")),
                    FieldElementExpression::Pow(
                        box FieldElementExpression::Identifier(String::from("a")),
                        box FieldElementExpression::Number(FieldPrime::from(4)),
                    )
                    .into(),
                ),
                TypedStatement::Return(vec![
                    FieldElementExpression::Identifier(String::from("b")).into()
                ]),
            ],
            signature: Signature {
                inputs: vec![],
                outputs: vec![Type::FieldElement],
            },
        };

        let mut flattener = Flattener::new();

        let expected = FlatFunction {
            id: String::from("main"),
            arguments: vec![],
            statements: vec![
                FlatStatement::Definition(
                    FlatVariable::new(0),
                    FlatExpression::Number(FieldPrime::from(7)),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(1),
                    FlatExpression::Mult(
                        box FlatExpression::Identifier(FlatVariable::new(0)),
                        box FlatExpression::Identifier(FlatVariable::new(0)),
                    ),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(2),
                    FlatExpression::Mult(
                        box FlatExpression::Identifier(FlatVariable::new(1)),
                        box FlatExpression::Identifier(FlatVariable::new(0)),
                    ),
                ),
                FlatStatement::Definition(
                    FlatVariable::new(3),
                    FlatExpression::Mult(
                        box FlatExpression::Identifier(FlatVariable::new(2)),
                        box FlatExpression::Identifier(FlatVariable::new(0)),
                    ),
                ),
                FlatStatement::Return(FlatExpressionList {
                    expressions: vec![FlatExpression::Identifier(FlatVariable::new(3))],
                }),
            ],
            signature: Signature::new().outputs(vec![Type::FieldElement]),
        };

        let flattened = flattener.flatten_function(function);

        assert_eq!(flattened, expected);
    }

    #[test]
    fn overload() {
        // def foo()
        //      return 1
        // def foo()
        //      return 1, 2
        // def main()
        //      a = foo()
        //      b, c = foo()
        //      return 1
        //
        //      should not panic
        //

        let flattener = Flattener::new();
        let functions = vec![
            TypedFunction {
                id: "foo".to_string(),
                arguments: vec![],
                statements: vec![TypedStatement::Return(vec![TypedExpression::FieldElement(
                    FieldElementExpression::Number(FieldPrime::from(1)),
                )])],
                signature: Signature::new()
                    .inputs(vec![])
                    .outputs(vec![Type::FieldElement]),
            },
            TypedFunction {
                id: "foo".to_string(),
                arguments: vec![],
                statements: vec![TypedStatement::Return(vec![
                    TypedExpression::FieldElement(FieldElementExpression::Number(
                        FieldPrime::from(1),
                    )),
                    TypedExpression::FieldElement(FieldElementExpression::Number(
                        FieldPrime::from(2),
                    )),
                ])],
                signature: Signature::new()
                    .inputs(vec![])
                    .outputs(vec![Type::FieldElement, Type::FieldElement]),
            },
            TypedFunction {
                id: "main".to_string(),
                arguments: vec![],
                statements: vec![
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::field_element("a")),
                        TypedExpression::FieldElement(FieldElementExpression::FunctionCall(
                            "foo".to_string(),
                            vec![],
                        )),
                    ),
                    TypedStatement::MultipleDefinition(
                        vec![
                            Variable::field_element("b".to_string()),
                            Variable::field_element("c".to_string()),
                        ],
                        TypedExpressionList::FunctionCall(
                            "foo".to_string(),
                            vec![],
                            vec![Type::FieldElement, Type::FieldElement],
                        ),
                    ),
                    TypedStatement::Return(vec![TypedExpression::FieldElement(
                        FieldElementExpression::Number(FieldPrime::from(1)),
                    )]),
                ],
                signature: Signature::new()
                    .inputs(vec![])
                    .outputs(vec![Type::FieldElement]),
            },
        ];

        flattener.flatten_program(TypedProg {
            functions: functions,
            imported_functions: vec![],
            imports: vec![],
        });

        // shouldn't panic
    }

    #[test]
    fn div() {
        // a = 5 / b / b
        let mut flattener = Flattener::new();

        let definition = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_element("b")),
            FieldElementExpression::Number(FieldPrime::from(42)).into(),
        );

        let statement = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_element("a")),
            FieldElementExpression::Div(
                box FieldElementExpression::Div(
                    box FieldElementExpression::Number(FieldPrime::from(5)),
                    box FieldElementExpression::Identifier(String::from("b")),
                ),
                box FieldElementExpression::Identifier(String::from("b")),
            )
            .into(),
        );

        let mut statements_flattened = vec![];

        statements_flattened.extend(flattener.flatten_statement(definition));

        statements_flattened.extend(flattener.flatten_statement(statement));

        // define b
        let b = FlatVariable::new(0);
        // define new wires for members of Div
        let five = FlatVariable::new(1);
        let b0 = FlatVariable::new(2);
        // Define inverse of denominator to prevent div by 0
        let invb0 = FlatVariable::new(3);
        // Define inverse
        let sym_0 = FlatVariable::new(4);
        // Define result, which is first member to next Div
        let sym_1 = FlatVariable::new(5);
        // Define second member
        let b1 = FlatVariable::new(6);
        // Define inverse of denominator to prevent div by 0
        let invb1 = FlatVariable::new(7);
        // Define inverse
        let sym_2 = FlatVariable::new(8);
        // Define left hand side
        let a = FlatVariable::new(9);

        assert_eq!(
            statements_flattened,
            vec![
                FlatStatement::Definition(b, FlatExpression::Number(FieldPrime::from(42))),
                // inputs to first div (5/b)
                FlatStatement::Definition(five, FlatExpression::Number(FieldPrime::from(5))),
                FlatStatement::Definition(b0, b.into()),
                // check div by 0
                FlatStatement::Directive(DirectiveStatement::new(
                    vec![invb0],
                    Helper::Rust(RustHelper::Div),
                    vec![FlatExpression::Number(FieldPrime::from(1)), b0.into()]
                )),
                FlatStatement::Condition(
                    FlatExpression::Number(FieldPrime::from(1)),
                    FlatExpression::Mult(box invb0.into(), box b0.into()),
                ),
                // execute div
                FlatStatement::Directive(DirectiveStatement::new(
                    vec![sym_0],
                    Helper::Rust(RustHelper::Div),
                    vec![five, b0]
                )),
                FlatStatement::Condition(
                    five.into(),
                    FlatExpression::Mult(box b0.into(), box sym_0.into()),
                ),
                // inputs to second div (res/b)
                FlatStatement::Definition(sym_1, sym_0.into()),
                FlatStatement::Definition(b1, b.into()),
                // check div by 0
                FlatStatement::Directive(DirectiveStatement::new(
                    vec![invb1],
                    Helper::Rust(RustHelper::Div),
                    vec![FlatExpression::Number(FieldPrime::from(1)), b1.into()]
                )),
                FlatStatement::Condition(
                    FlatExpression::Number(FieldPrime::from(1)),
                    FlatExpression::Mult(box invb1.into(), box b1.into()),
                ),
                // execute div
                FlatStatement::Directive(DirectiveStatement::new(
                    vec![sym_2],
                    Helper::Rust(RustHelper::Div),
                    vec![sym_1, b1]
                )),
                FlatStatement::Condition(
                    sym_1.into(),
                    FlatExpression::Mult(box b1.into(), box sym_2.into()),
                ),
                // result
                FlatStatement::Definition(a, sym_2.into()),
            ]
        );
    }

    #[test]
    fn field_array() {
        // foo = [ , , ]

        let mut flattener = Flattener::new();

        let statement = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_array("foo", 3)),
            FieldElementArrayExpression::Value(
                3,
                vec![
                    FieldElementExpression::Number(FieldPrime::from(1)),
                    FieldElementExpression::Number(FieldPrime::from(2)),
                    FieldElementExpression::Number(FieldPrime::from(3)),
                ],
            )
            .into(),
        );
        let expression = FieldElementArrayExpression::Identifier(3, String::from("foo"));

        let _statements = flattener.flatten_statement(statement);

        let expressions = flattener.flatten_field_array_expression(expression, &mut vec![]);

        assert_eq!(
            expressions,
            vec![
                FlatExpression::Identifier(FlatVariable::new(0)),
                FlatExpression::Identifier(FlatVariable::new(1)),
                FlatExpression::Identifier(FlatVariable::new(2)),
            ]
        );
    }

    #[test]
    fn array_definition() {
        // field[3] foo = [1, 2, 3]

        let mut flattener = Flattener::new();

        let statement = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_array("foo", 3)),
            FieldElementArrayExpression::Value(
                3,
                vec![
                    FieldElementExpression::Number(FieldPrime::from(1)),
                    FieldElementExpression::Number(FieldPrime::from(2)),
                    FieldElementExpression::Number(FieldPrime::from(3)),
                ],
            )
            .into(),
        );

        let statements_flattened = flattener.flatten_statement(statement);

        assert_eq!(
            statements_flattened,
            vec![
                FlatStatement::Definition(
                    FlatVariable::new(0),
                    FlatExpression::Number(FieldPrime::from(1))
                ),
                FlatStatement::Definition(
                    FlatVariable::new(1),
                    FlatExpression::Number(FieldPrime::from(2))
                ),
                FlatStatement::Definition(
                    FlatVariable::new(2),
                    FlatExpression::Number(FieldPrime::from(3))
                ),
            ]
        );
    }

    #[test]
    fn random_array_access() {
        // def main(field i) -> (field):
        //      field[2] foo = [1, 2]
        //      return foo[i]

        let flattener = Flattener::new();

        let program = TypedProg {
            functions: vec![TypedFunction {
                id: "main".to_string(),
                arguments: vec![Parameter::private(Variable::field_element("i"))],
                statements: vec![
                    TypedStatement::Definition(
                        TypedAssignee::Identifier(Variable::field_array("foo", 2)),
                        FieldElementArrayExpression::Value(
                            2,
                            vec![
                                FieldElementExpression::Number(FieldPrime::from(1)),
                                FieldElementExpression::Number(FieldPrime::from(2)),
                            ],
                        )
                        .into(),
                    ),
                    TypedStatement::Return(vec![FieldElementExpression::Select(
                        box FieldElementArrayExpression::Identifier(2, String::from("foo")),
                        box FieldElementExpression::Identifier(String::from("i")),
                    )
                    .into()]),
                ],
                signature: Signature::new()
                    .inputs(vec![Type::FieldElement])
                    .outputs(vec![Type::FieldElement]),
            }],
            imported_functions: vec![],
            imports: vec![],
        };

        let flat_prog = flattener.flatten_program(program);

        let ir_prog = Prog::from(flat_prog);

        // main(0) -> 1
        assert_eq!(
            ir_prog
                .execute(vec![FieldPrime::from(0)])
                .unwrap()
                .get(&FlatVariable::public(0)),
            Some(&FieldPrime::from(1))
        );

        // main(1) -> 2
        assert_eq!(
            ir_prog
                .execute(vec![FieldPrime::from(1)])
                .unwrap()
                .get(&FlatVariable::public(0)),
            Some(&FieldPrime::from(2))
        );

        // main(2) -> error
        assert!(ir_prog.execute(vec![FieldPrime::from(2)]).is_err());
    }

    #[test]
    fn array_sum() {
        // field[3] foo = [1, 2, 3]
        // bar = foo[0] + foo[1] + foo[2]
        // we don't optimise detecting constants, this will be done in an optimiser pass

        let mut flattener = Flattener::new();

        let def = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_array("foo", 3)),
            FieldElementArrayExpression::Value(
                3,
                vec![
                    FieldElementExpression::Number(FieldPrime::from(1)),
                    FieldElementExpression::Number(FieldPrime::from(2)),
                    FieldElementExpression::Number(FieldPrime::from(3)),
                ],
            )
            .into(),
        );

        let sum = TypedStatement::Definition(
            TypedAssignee::Identifier(Variable::field_element("bar")),
            FieldElementExpression::Add(
                box FieldElementExpression::Add(
                    box FieldElementExpression::Select(
                        box FieldElementArrayExpression::Identifier(3, String::from("foo")),
                        box FieldElementExpression::Number(FieldPrime::from(0)),
                    ),
                    box FieldElementExpression::Select(
                        box FieldElementArrayExpression::Identifier(3, String::from("foo")),
                        box FieldElementExpression::Number(FieldPrime::from(1)),
                    ),
                ),
                box FieldElementExpression::Select(
                    box FieldElementArrayExpression::Identifier(3, String::from("foo")),
                    box FieldElementExpression::Number(FieldPrime::from(2)),
                ),
            )
            .into(),
        );

        let mut statements_flattened = vec![];

        statements_flattened.extend(flattener.flatten_statement(def));

        statements_flattened.extend(flattener.flatten_statement(sum));

        assert_eq!(
            statements_flattened[3],
            FlatStatement::Definition(
                FlatVariable::new(3),
                FlatExpression::Add(
                    box FlatExpression::Add(
                        box FlatExpression::Identifier(FlatVariable::new(0)),
                        box FlatExpression::Identifier(FlatVariable::new(1)),
                    ),
                    box FlatExpression::Identifier(FlatVariable::new(2)),
                )
            )
        );
    }

    #[test]
    fn next_variable() {
        let mut flattener: Flattener<FieldPrime> = Flattener::new();
        assert_eq!(
            FlatVariable::new(0),
            flattener.use_variable(&String::from("a"))
        );
        assert_eq!(
            flattener.get_latest_var_substitution(&String::from("a")),
            FlatVariable::new(0)
        );
        assert_eq!(
            FlatVariable::new(1),
            flattener.use_variable(&String::from("a"))
        );
        assert_eq!(
            flattener.get_latest_var_substitution(&String::from("a")),
            FlatVariable::new(1)
        );
        assert_eq!(
            FlatVariable::new(2),
            flattener.use_variable(&String::from("a"))
        );
        assert_eq!(
            flattener.get_latest_var_substitution(&String::from("a")),
            FlatVariable::new(2)
        );
    }
}
