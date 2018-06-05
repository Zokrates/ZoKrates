
use std::collections::BTreeMap;
use flat_absy::{FlatStatement, FlatExpression, FlatFunction, FlatExpressionList};
use field::Field;
use executable::Sha256Libsnark;

// for r1cs import, can be moved.
// r1cs data strucutre reflecting JSON standard format:
//{variables:["a","b", ... ],
//constraints:[
// [{offset_1:value_a1,offset2:value_a2,...},{offset1:value_b1,offset2:value_b2,...},{offset1:value_c1,offset2:value_c2,...}]
//]}
#[derive(Serialize, Deserialize, Debug)]
pub struct R1CS {
    pub constraints: Vec<Constraint>,
}

#[derive(Serialize, Deserialize, Debug)]
pub struct Witness {
    pub TestVariables: Vec<usize>
}

#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct Constraint {
	a: BTreeMap<String, isize>,
	b: BTreeMap<String, isize>,
	c: BTreeMap<String, isize>,
}

impl<T: Field> Into<FlatStatement<T>> for Constraint {
	fn into(self: Constraint) -> FlatStatement<T> {
		let lhs_a = self.a.iter()
			.map(|(key, val)| FlatExpression::Mult(box FlatExpression::Number(T::from(*val as i32)), box FlatExpression::Identifier(format!("inter{}",key.clone()))))
			.fold(FlatExpression::Number(T::zero()), |acc, e| FlatExpression::Add(box acc, box e));
		
		let lhs_b = self.b.iter()
			.map(|(key, val)| FlatExpression::Mult(box FlatExpression::Number(T::from(*val as i32)), box FlatExpression::Identifier(format!("inter{}",key.clone()))))
			.fold(FlatExpression::Number(T::zero()), |acc, e| FlatExpression::Add(box acc, box e));
		
		let rhs = self.c.iter()
			.map(|(key, val)| FlatExpression::Mult(box FlatExpression::Number(T::from(*val as i32)), box FlatExpression::Identifier(format!("inter{}",key.clone()))))
			.fold(FlatExpression::Number(T::zero()), |acc, e| FlatExpression::Add(box acc, box e));

		FlatStatement::Condition(FlatExpression::Mult(box lhs_a, box lhs_b), rhs)
	}
}

impl<T: Field> Into<FlatFunction<T>> for R1CS {
	fn into(self: R1CS) -> FlatFunction<T> {

        let mut statements: Vec<FlatStatement<T>> = self.constraints.into_iter().map(|c| c.into()).collect();

        let variables = vec![0; 50098].iter().enumerate().map(|(i, _)| format!("inter{}", i)).collect();

        statements.insert(0, FlatStatement::Directive(variables, vec![], Sha256Libsnark {}));

        statements.push(FlatStatement::Return(FlatExpressionList{expressions: vec!["inter3", "inter4", "inter5", "inter6", "inter7", "inter8", "inter9", "inter10", "inter11", "inter12", "inter13", "inter14", "inter15", "inter16", "inter17", "inter18", "inter19", "inter20", "inter21", "inter22", "inter23", "inter24", "inter25", "inter26", "inter27", "inter28", "inter29", "inter30", "inter31", "inter32", "inter33", "inter34", "inter35", "inter36", "inter37", "inter38", "inter39", "inter40", "inter41", "inter42", "inter43", "inter44", "inter45", "inter46", "inter47", "inter48", "inter49", "inter50", "inter51", "inter52", "inter53", "inter54", "inter55", "inter56", "inter57", "inter58", "inter59", "inter60", "inter61", "inter62", "inter63", "inter64", "inter65", "inter66", "inter67", "inter68", "inter69", "inter70", "inter71", "inter72", "inter73", "inter74", "inter75", "inter76", "inter77", "inter78", "inter79", "inter80", "inter81", "inter82", "inter83", "inter84", "inter85", "inter86", "inter87", "inter88", "inter89", "inter90", "inter91", "inter92", "inter93", "inter94", "inter95", "inter96", "inter97", "inter98", "inter99", "inter100", "inter101", "inter102", "inter103", "inter104", "inter105", "inter106", "inter107", "inter108", "inter109", "inter110", "inter111", "inter112", "inter113", "inter114", "inter115", "inter116", "inter117", "inter118", "inter119", "inter120", "inter121", "inter122", "inter123", "inter124", "inter125", "inter126", "inter127", "inter128", "inter129", "inter130", "inter131", "inter132", "inter133", "inter134", "inter135", "inter136", "inter137", "inter138", "inter139", "inter140", "inter141", "inter142", "inter143", "inter144", "inter145", "inter146", "inter147", "inter148", "inter149", "inter150", "inter151", "inter152", "inter153", "inter154", "inter155", "inter156", "inter157", "inter158", "inter159", "inter160", "inter161", "inter162", "inter163", "inter164", "inter165", "inter166", "inter167", "inter168", "inter169", "inter170", "inter171", "inter172", "inter173", "inter174", "inter175", "inter176", "inter177", "inter178", "inter179", "inter180", "inter181", "inter182", "inter183", "inter184", "inter185", "inter186", "inter187", "inter188", "inter189", "inter190", "inter191", "inter192", "inter193", "inter194", "inter195", "inter196", "inter197", "inter198", "inter199", "inter200", "inter201", "inter202", "inter203", "inter204", "inter205", "inter206", "inter207", "inter208", "inter209", "inter210", "inter211", "inter212", "inter213", "inter214", "inter215", "inter216", "inter217", "inter218", "inter219", "inter220", "inter221", "inter222", "inter223", "inter224", "inter225", "inter226", "inter227", "inter228", "inter229", "inter230", "inter231", "inter232", "inter233", "inter234", "inter235", "inter236", "inter237", "inter238", "inter239", "inter240", "inter241", "inter242", "inter243", "inter244", "inter245", "inter246", "inter247", "inter248", "inter249", "inter250", "inter251", "inter252", "inter253", "inter254", "inter255", 
            "inter256", "inter257", "inter258"].iter().map(|t| FlatExpression::Identifier(t.to_string())).collect()}));
        
        FlatFunction { 
            id: "main".to_owned(), 
            arguments: vec![], 
            statements: statements, 
            return_count: 256
        }
	}
} 

#[cfg(test)]
mod tests {
	use super::*;
	use field::FieldPrime;

	#[test]
	fn deserialize_constraint() {
		let constraint = r#"[{"2026": 1}, {"0": 1, "2026": -1}, {"0": 0}]"#;
		let c: Constraint = serde_json::from_str(constraint).unwrap();
	}

	#[test]
	fn constraint_into_flat_statement() {
		let constraint = r#"[{"2026": 1}, {"0": 1, "2026": -1}, {"0": 0}]"#;
		let c: Constraint = serde_json::from_str(constraint).unwrap();
		let statement: FlatStatement<FieldPrime> = c.into();
		println!("{}", statement);
	}
}

