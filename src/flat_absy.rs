//! Module containing structs and enums to represent a program.
//!
//! @file absy.rs
//! @author Dennis Kuhnert <dennis.kuhnert@campus.tu-berlin.de>
//! @author Jacob Eberhardt <jacob.eberhardt@tu-berlin.de>
//! @date 2017

const BINARY_SEPARATOR: &str = "_b";

use absy::Expression;
use std::fmt;
use std::collections::{BTreeMap};
use field::Field;
use parameter::Parameter;
use substitution::Substitution;
use executable::{Executable, Sha256Libsnark};
use regex::Regex;
use standard;

#[derive(Serialize, Deserialize, Clone)]
pub struct FlatProg<T: Field> {
    /// FlatFunctions of the program
    pub functions: Vec<FlatFunction<T>>,
}


impl<T: Field> FlatProg<T> {
    // only main flattened function is relevant here, as all other functions are unrolled into it
    #[allow(dead_code)] // I don't want to remove this
    pub fn get_witness(&self, inputs: Vec<T>) -> BTreeMap<String, T> {
        let main = self.functions.iter().find(|x| x.id == "main").unwrap();
        assert!(main.arguments.len() == inputs.len());
        main.get_witness(inputs)
    }
}

impl<T: Field> fmt::Display for FlatProg<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            self.functions
                .iter()
                .map(|x| format!("{}", x))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

impl<T: Field> fmt::Debug for FlatProg<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "flat_program(functions: {}\t)",
            self.functions
                .iter()
                .map(|x| format!("\t{:?}", x))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

impl<T: Field> From<standard::R1CS> for FlatProg<T> {
    fn from(r1cs: standard::R1CS) -> Self {
        FlatProg {
            functions: vec![FlatFunction::from(r1cs)]
        }
    }
}


#[derive(Serialize, Deserialize, Clone, PartialEq)]
pub struct FlatFunction<T: Field> {
    /// Name of the program
    pub id: String,
    /// Arguments of the function
    pub arguments: Vec<Parameter>,
    /// Vector of statements that are executed when running the function
    pub statements: Vec<FlatStatement<T>>,
    /// number of returns
    pub return_count: usize,
}

impl<T: Field> FlatFunction<T> {
    pub fn get_witness(&self, inputs: Vec<T>) -> BTreeMap<String, T> {
        assert!(self.arguments.len() == inputs.len());
        let mut witness = BTreeMap::new();
        witness.insert("~one".to_string(), T::one());
        for (i, arg) in self.arguments.iter().enumerate() {
            witness.insert(arg.id.to_string(), inputs[i].clone());
        }
        for statement in &self.statements {
            match *statement {
                FlatStatement::Return(ref list) => {
                    for (i, val) in list.expressions.iter().enumerate() {
                        let s = val.solve(&mut witness);
                        witness.insert(format!("~out_{}", i).to_string(), s);
                    }
                }
                FlatStatement::Definition(ref id, ref expr) => {
                    let s = expr.solve(&mut witness);
                    witness.insert(id.to_string(), s);
                },
                FlatStatement::Compiler(ref id, ref expr) => {
                    let s = expr.solve(&mut witness);
                    witness.insert(id.to_string(), s);
                },
                FlatStatement::Condition(ref lhs, ref rhs) => {
                    assert_eq!(lhs.solve(&mut witness), rhs.solve(&mut witness))
                },
                FlatStatement::LibsnarkSha256Directive(ref outputs, ref inputs, _) => {
                    let res: Vec<T> = outputs.iter().map(|o| T::one()).collect();
                    for (i, o) in outputs.iter().enumerate() {
                        witness.insert(o.to_string(), res[i].clone());
                    }
                }
            }
        }
        witness
    }
}

impl<T: Field> fmt::Display for FlatFunction<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "def {}({}):\n{}",
            self.id,
            self.arguments
                .iter()
                .map(|x| format!("{}", x))
                .collect::<Vec<_>>()
                .join(","),
            self.statements
                .iter()
                .map(|x| format!("\t{}", x))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

impl<T: Field> fmt::Debug for FlatFunction<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "FlatFunction(id: {:?}, arguments: {:?}, ...):\n{}",
            self.id,
            self.arguments,
            self.statements
                .iter()
                .map(|x| format!("\t{:?}", x))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

/// Calculates a flattened function based on a R1CS (A, B, C) and returns that flattened function:
/// * The Rank 1 Constraint System (R1CS) is defined as:
/// * `<A,x>*<B,x> = <C,x>` for a witness `x`
/// * Since the matrices in R1CS are usually sparse, the following encoding is used:
/// * For each constraint (i.e., row in the R1CS), only non-zero values are supplied and encoded as a tuple (index, value).
///
/// # Arguments
///
/// * r1cs - R1CS in standard JSON data format

impl<T: Field> From<standard::R1CS> for FlatFunction<T> {
    fn from(r1cs: standard::R1CS) -> Self {
        // statements that constrains are translated to
        let mut statements: Vec<FlatStatement<T>> = Vec::new();
        let mut parameters: Vec<Parameter> = Vec::new();
        let mut intermediate_var_index = 1;

        let mut vars = vec![];

        for cons in r1cs.constraints {
            assert!(cons.len() == 3); // entries for a,b,c
            let mut lhs_a = FlatExpression::Number(T::from(0));
            let mut lhs_b = FlatExpression::Number(T::from(0));
            let mut rhs = FlatExpression::Number(T::from(0));

            let mut first = true;
            let regex = Regex::new(r"[^a-zA-Z0-9]").unwrap();

            for i in 0..cons.len() {
                for (var_offset, val) in &cons[i] {
                    let var_index = var_offset.parse::<usize>().unwrap();
                    let mut var;
                    // if var_index < r1cs.variables.len() {
                    //     var = r1cs.variables[var_index].clone(); // get variable name
                    //     var = String::from(regex.replace_all(var.as_str(), "").into_owned());
                    //     parameters.push(Parameter{id: var.clone(), private: false});
                    // } else {
                        var = format!("inter{}", intermediate_var_index);
                        //parameters.push(Parameter{id: var.clone(), private: true});
                        vars.push(var.clone());
                        intermediate_var_index+=1;
                    // }
                    let term = FlatExpression::Mult(box FlatExpression::Number(T::from(*val as i32)), box FlatExpression::Identifier(var));
                    if first {
                        lhs_a = term;
                        first = !first;
                    } else {
                        lhs_a = FlatExpression::Add(box lhs_a, box term);
                    }
                }
                first = true;
            }
            statements.push(FlatStatement::Condition(FlatExpression::Mult(box lhs_a, box lhs_b), rhs));
        }

        statements.insert(0, FlatStatement::LibsnarkSha256Directive(vars, vec![], Sha256Libsnark {}));

        statements.push(FlatStatement::Return(FlatExpressionList{expressions: vec!["inter3", "inter4", "inter5", "inter6", "inter7", "inter8", "inter9", "inter10", "inter11", "inter12", "inter13", "inter14", "inter15", "inter16", "inter17", "inter18", "inter19", "inter20", "inter21", "inter22", "inter23", "inter24", "inter25", "inter26", "inter27", "inter28", "inter29", "inter30", "inter31", "inter32", "inter33", "inter34", "inter35", "inter36", "inter37", "inter38", "inter39", "inter40", "inter41", "inter42", "inter43", "inter44", "inter45", "inter46", "inter47", "inter48", "inter49", "inter50", "inter51", "inter52", "inter53", "inter54", "inter55", "inter56", "inter57", "inter58", "inter59", "inter60", "inter61", "inter62", "inter63", "inter64", "inter65", "inter66", "inter67", "inter68", "inter69", "inter70", "inter71", "inter72", "inter73", "inter74", "inter75", "inter76", "inter77", "inter78", "inter79", "inter80", "inter81", "inter82", "inter83", "inter84", "inter85", "inter86", "inter87", "inter88", "inter89", "inter90", "inter91", "inter92", "inter93", "inter94", "inter95", "inter96", "inter97", "inter98", "inter99", "inter100", "inter101", "inter102", "inter103", "inter104", "inter105", "inter106", "inter107", "inter108", "inter109", "inter110", "inter111", "inter112", "inter113", "inter114", "inter115", "inter116", "inter117", "inter118", "inter119", "inter120", "inter121", "inter122", "inter123", "inter124", "inter125", "inter126", "inter127", "inter128", "inter129", "inter130", "inter131", "inter132", "inter133", "inter134", "inter135", "inter136", "inter137", "inter138", "inter139", "inter140", "inter141", "inter142", "inter143", "inter144", "inter145", "inter146", "inter147", "inter148", "inter149", "inter150", "inter151", "inter152", "inter153", "inter154", "inter155", "inter156", "inter157", "inter158", "inter159", "inter160", "inter161", "inter162", "inter163", "inter164", "inter165", "inter166", "inter167", "inter168", "inter169", "inter170", "inter171", "inter172", "inter173", "inter174", "inter175", "inter176", "inter177", "inter178", "inter179", "inter180", "inter181", "inter182", "inter183", "inter184", "inter185", "inter186", "inter187", "inter188", "inter189", "inter190", "inter191", "inter192", "inter193", "inter194", "inter195", "inter196", "inter197", "inter198", "inter199", "inter200", "inter201", "inter202", "inter203", "inter204", "inter205", "inter206", "inter207", "inter208", "inter209", "inter210", "inter211", "inter212", "inter213", "inter214", "inter215", "inter216", "inter217", "inter218", "inter219", "inter220", "inter221", "inter222", "inter223", "inter224", "inter225", "inter226", "inter227", "inter228", "inter229", "inter230", "inter231", "inter232", "inter233", "inter234", "inter235", "inter236", "inter237", "inter238", "inter239", "inter240", "inter241", "inter242", "inter243", "inter244", "inter245", "inter246", "inter247", "inter248", "inter249", "inter250", "inter251", "inter252", "inter253", "inter254", "inter255", 
            "inter256", "inter257", "inter258"].iter().map(|t| FlatExpression::Identifier(t.to_string())).collect()}));         //TODO: Fix me when inputs and outputs are clear from the json
        FlatFunction { 
            id: "main".to_owned(), 
            arguments: parameters , 
            statements: statements, 
            return_count: 256
        }
    } 
}

#[derive(Clone, Serialize, Deserialize, PartialEq)]
pub enum FlatStatement<T: Field> {
    Return(FlatExpressionList<T>),
    Condition(FlatExpression<T>, FlatExpression<T>),
    Compiler(String, Expression<T>),
    Definition(String, FlatExpression<T>),
    LibsnarkSha256Directive(Vec<String>, Vec<String>, Sha256Libsnark)
}

impl<T: Field> fmt::Display for FlatStatement<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FlatStatement::Definition(ref lhs, ref rhs) => write!(f, "{} = {}", lhs, rhs),
            FlatStatement::Return(ref expr) => write!(f, "return {}", expr),
            FlatStatement::Condition(ref lhs, ref rhs) => write!(f, "{} == {}", lhs, rhs),
            FlatStatement::Compiler(ref lhs, ref rhs) => write!(f, "# {} = {}", lhs, rhs),
            FlatStatement::LibsnarkSha256Directive(ref outputs, ref inputs, _) => write!(f, "# {} = Sha256Libsnark({})", outputs.join(", "), inputs.join(", ")),
        }
    }
}

impl<T: Field> fmt::Debug for FlatStatement<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FlatStatement::Definition(ref lhs, ref rhs) => write!(f, "{} = {}", lhs, rhs),
            FlatStatement::Return(ref expr) => write!(f, "FlatReturn({:?})", expr),
            FlatStatement::Condition(ref lhs, ref rhs) => write!(f, "FlatCondition({:?}, {:?})", lhs, rhs),
            FlatStatement::Compiler(ref lhs, ref rhs) => write!(f, "Compiler({:?}, {:?})", lhs, rhs),
            FlatStatement::LibsnarkSha256Directive(ref outputs, ref inputs, _) => write!(f, "Sha256Libsnark({:?}, {:?})", outputs, inputs),
        }
    }
}

impl<T: Field> FlatStatement<T> {
    pub fn apply_substitution(&self, substitution: &Substitution) -> FlatStatement<T> {
        match *self {
            FlatStatement::Definition(ref id, ref x) => FlatStatement::Definition(
                match substitution.get(id) { 
                    Some(z) => z.clone(), 
                    None => id.clone() 
                }, 
                x.apply_substitution(substitution)
            ),
            FlatStatement::Return(ref x) => FlatStatement::Return(x.apply_substitution(substitution)),
            FlatStatement::Compiler(ref lhs, ref rhs) => FlatStatement::Compiler(match substitution.get(lhs) { 
                    Some(z) => z.clone(), 
                    None => lhs.clone() 
                }, rhs.clone().apply_substitution(substitution)),
            FlatStatement::Condition(ref x, ref y) => {
                FlatStatement::Condition(x.apply_substitution(substitution), y.apply_substitution(substitution))
            },
            FlatStatement::LibsnarkSha256Directive(ref outputs, ref inputs, _) => {
                let new_outputs = outputs.iter().map(|o| match substitution.get(o) {
                    Some(z) => z.clone(),
                    None => o.clone()
                }).collect();
                let new_inputs = inputs.iter().map(|i| substitution.get(i).unwrap()).collect();
                FlatStatement::LibsnarkSha256Directive(new_outputs, new_inputs, Sha256Libsnark {})
            }
        }
    }
}

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub enum FlatExpression<T: Field> {
    Number(T),
    Identifier(String),
    Add(Box<FlatExpression<T>>, Box<FlatExpression<T>>),
    Sub(Box<FlatExpression<T>>, Box<FlatExpression<T>>),
    Div(Box<FlatExpression<T>>, Box<FlatExpression<T>>),
    Mult(Box<FlatExpression<T>>, Box<FlatExpression<T>>)
}

impl<T: Field> FlatExpression<T> {
    pub fn apply_substitution(&self, substitution: &Substitution) -> FlatExpression<T> {
        match *self {
            ref e @ FlatExpression::Number(_) => e.clone(),
            FlatExpression::Identifier(ref v) => {
                let mut new_name = v.to_string();
                loop {
                    match substitution.get(&new_name) {
                        Some(x) => new_name = x.to_string(),
                        None => return FlatExpression::Identifier(new_name),
                    }
                }
            }
            FlatExpression::Add(ref e1, ref e2) => FlatExpression::Add(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            FlatExpression::Sub(ref e1, ref e2) => FlatExpression::Sub(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            FlatExpression::Mult(ref e1, ref e2) => FlatExpression::Mult(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            ),
            FlatExpression::Div(ref e1, ref e2) => FlatExpression::Div(
                box e1.apply_substitution(substitution),
                box e2.apply_substitution(substitution),
            )

        }
    }

    fn solve(&self, inputs: &mut BTreeMap<String, T>) -> T {
        match *self {
            FlatExpression::Number(ref x) => x.clone(),
            FlatExpression::Identifier(ref var) => {
                if let None = inputs.get(var) {
                    if var.contains(BINARY_SEPARATOR) {
                        let var_name = var.split(BINARY_SEPARATOR).collect::<Vec<_>>()[0];
                        let mut num = inputs[var_name].clone();
                        let bits = T::get_required_bits();
                        for i in (0..bits).rev() {
                            if T::from(2).pow(i) <= num {
                                num = num - T::from(2).pow(i);
                                inputs.insert(format!("{}{}{}", &var_name, BINARY_SEPARATOR, i), T::one());
                            } else {
                                inputs.insert(format!("{}{}{}", &var_name, BINARY_SEPARATOR, i), T::zero());
                            }
                        }
                        assert_eq!(num, T::zero());
                    } else {
                        panic!(
                            "Variable {:?} is undeclared in inputs: {:?}",
                            var,
                            inputs
                        );
                    }
                }
                inputs[var].clone()
            }
            FlatExpression::Add(ref x, ref y) => x.solve(inputs) + y.solve(inputs),
            FlatExpression::Sub(ref x, ref y) => x.solve(inputs) - y.solve(inputs),
            FlatExpression::Mult(ref x, ref y) => x.solve(inputs) * y.solve(inputs),
            FlatExpression::Div(ref x, ref y) => x.solve(inputs) / y.solve(inputs),
        }
    }

    pub fn is_linear(&self) -> bool {
        match *self {
            FlatExpression::Number(_) | FlatExpression::Identifier(_) => true,
            FlatExpression::Add(ref x, ref y) | FlatExpression::Sub(ref x, ref y) => {
                x.is_linear() && y.is_linear()
            }
            FlatExpression::Mult(ref x, ref y) | FlatExpression::Div(ref x, ref y) => {
                match (x.clone(), y.clone()) {
                    (box FlatExpression::Number(_), box FlatExpression::Number(_)) |
                    (box FlatExpression::Number(_), box FlatExpression::Identifier(_)) |
                    (box FlatExpression::Identifier(_), box FlatExpression::Number(_)) => true,
                    _ => false,
                }
            }
        }
    }
}

impl<T: Field> fmt::Display for FlatExpression<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FlatExpression::Number(ref i) => write!(f, "{}", i),
            FlatExpression::Identifier(ref var) => write!(f, "{}", var),
            FlatExpression::Add(ref lhs, ref rhs) => write!(f, "({} + {})", lhs, rhs),
            FlatExpression::Sub(ref lhs, ref rhs) => write!(f, "({} - {})", lhs, rhs),
            FlatExpression::Mult(ref lhs, ref rhs) => write!(f, "({} * {})", lhs, rhs),
            FlatExpression::Div(ref lhs, ref rhs) => write!(f, "({} / {})", lhs, rhs),
        }
    }
}

impl<T: Field> fmt::Debug for FlatExpression<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            FlatExpression::Number(ref i) => write!(f, "Num({})", i),
            FlatExpression::Identifier(ref var) => write!(f, "Ide({})", var),
            FlatExpression::Add(ref lhs, ref rhs) => write!(f, "Add({:?}, {:?})", lhs, rhs),
            FlatExpression::Sub(ref lhs, ref rhs) => write!(f, "Sub({:?}, {:?})", lhs, rhs),
            FlatExpression::Mult(ref lhs, ref rhs) => write!(f, "Mult({:?}, {:?})", lhs, rhs),
            FlatExpression::Div(ref lhs, ref rhs) => write!(f, "Div({:?}, {:?})", lhs, rhs),
        }
    }
}

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub struct FlatExpressionList<T: Field> {
    pub expressions: Vec<FlatExpression<T>>
}

impl<T: Field> fmt::Display for FlatExpressionList<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, param) in self.expressions.iter().enumerate() {
            try!(write!(f, "{}", param));
            if i < self.expressions.len() - 1 {
                try!(write!(f, ", "));
            }
        }
        write!(f, "")
    }
}

impl<T: Field> FlatExpressionList<T> {
    pub fn apply_substitution(&self, substitution: &Substitution) -> FlatExpressionList<T> {
        let expressions: Vec<FlatExpression<T>> = self.expressions.iter().map(|e| e.apply_substitution(substitution)).collect();
        FlatExpressionList {
            expressions: expressions
        }
    }
}

impl<T: Field> fmt::Debug for FlatExpressionList<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ExpressionList({:?})", self.expressions)
    }
}
