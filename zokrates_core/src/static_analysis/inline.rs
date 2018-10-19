use std::collections::HashMap;
use field::Field;
use typed_absy::Folder;
use typed_absy::*;
use typed_absy::folder::*;
use types::{Type, Signature};

pub struct Inliner<T: Field> {
	functions: Vec<TypedFunction<T>>,
	statements_buffer: Vec<TypedStatement<T>>,
	context: Vec<(String, usize)>,
	call_count: HashMap<String, usize>
}

impl<T: Field> Inliner<T> {
    pub fn new() -> Self {
        Inliner {
        	functions: vec![],
        	statements_buffer: vec![],
        	context: vec![],
        	call_count: HashMap::new()
        }
    }

    fn should_inline(&self, _function: &TypedFunction<T>, _arguments: &Vec<TypedExpression<T>>) -> bool {
    	// we should define a heuristic here
    	// currently it doesn't seem like there's a tradeoff as everything gets inlined in flattening anyway
    	// however, using backends such as bellman, we could avoid flattening and "stream" the computation
    	// at proving time, the tradeoff becomes code size (not inlining keeps only one copy of each function) vs optimisation
    	// (inlining enables constant propagation through function calls, which cannot be achieved by our final optimiser in some cases) 
    	true
    }

    // inline a call to `function` taking `expressions` as inputs
    // this function mutates `self.call` by incrementing the counter for `function`, and mutates `self.context`
    fn inline_call(&mut self, function: &TypedFunction<T>, expressions: Vec<TypedExpression<T>>) -> Vec<TypedExpression<T>> {
		self.call_count.entry(function.to_slug()).and_modify(|i| *i += 1).or_insert(1);
		self.context.push((function.to_slug(), *self.call_count.get(&function.to_slug()).unwrap()));

		// add definitions for the inputs
		let mut inputs_bindings = function.arguments.iter().zip(expressions)
			.map(|(a, e)| 
				TypedStatement::Definition(
					TypedAssignee::Identifier(self.fold_variable(a.id.clone())),
					e
				)
			).collect();
		self.statements_buffer.append(&mut inputs_bindings);

		// filter out the return statement and keep it aside
		let (mut statements, ret) : (Vec<_>, Vec<_>) = function.statements.clone().into_iter().flat_map(|s| self.fold_statement(s)).partition(|s| match s {
			TypedStatement::Return(..) => false,
			_ => true
		});

		// add all statements to the buffer
		self.statements_buffer.append(&mut statements);

		// remove this call from the context
		self.context.pop();

		match ret[0].clone() {
			TypedStatement::Return(exprs) => exprs,
			_ => panic!("")
		}
    }

    pub fn inline(prog: TypedProg<T>) -> TypedProg<T> {
        Inliner::new().fold_program(prog)
    }
}

impl<T: Field> Folder<T> for Inliner<T> {
	// store the list of functions
	fn fold_program(&mut self, p: TypedProg<T>) -> TypedProg<T> {
		self.functions = p.functions.clone();
		fold_program(self, p)
	}

	// add extra statements before the modified statement
	fn fold_statement(&mut self, s: TypedStatement<T>) -> Vec<TypedStatement<T>> {
		let mut statements = match s {
	        TypedStatement::MultipleDefinition(variables, elist) => {
	        	match elist {
	        		TypedExpressionList::FunctionCall(id, exps, types) => {
	        			let exps: Vec<_> = exps.into_iter().map(|e| self.fold_expression(e)).collect();

						let passed_signature = Signature::new()
				            .inputs(exps.iter().map(|e| e.get_type()).collect())
				            .outputs(types.clone());

				        // find the function
		        		let function = self.functions.iter().find(|f| f.id == id && f.signature == passed_signature).expect("function should exist").clone();

		        		match self.should_inline(&function, &exps) {
		        			true => {
		        				let ret = self.inline_call(&function, exps);
		        				variables.into_iter().zip(ret.into_iter()).map(|(v, e)| TypedStatement::Definition(TypedAssignee::Identifier(v), e)).collect()
		        			},
		        			false => {
		        				vec![TypedStatement::MultipleDefinition(variables, TypedExpressionList::FunctionCall(id, exps, types))]
		        			}
		        		}
	        		}
	        	}
	        },
	        s => fold_statement(self, s)
	    };

		// add the result of folding to the buffer
	    self.statements_buffer.append(&mut statements);
	    // return the whole buffer
	    self.statements_buffer.drain(..).collect()
	}

	// prefix all names with the context
	fn fold_name(&mut self, n: String) -> String {
		match self.context.len() {
			0 => n,
			_ => format!("{}_{}", self
			.context
			.iter()
			.map(|(s, i)| 
				format!("{}_{}", s, i)
			)
			.collect::<Vec<_>>()
			.join("_"), n)
		}
	}

	// inline calls which return a field element
	fn fold_field_expression(&mut self, e: FieldElementExpression<T>) -> FieldElementExpression<T> {
        match e {
            FieldElementExpression::FunctionCall(id, exps) => {
                let exps: Vec<_> = exps.into_iter().map(|e| self.fold_expression(e)).collect();

		        let passed_signature = Signature::new()
		            .inputs(exps.iter().map(|e| e.get_type()).collect())
		            .outputs(vec![Type::FieldElement]);

		        // find the function
		        let function = self.functions.iter().find(|f| f.id == id && f.signature == passed_signature).expect("function should exist").clone();

                match self.should_inline(&function, &exps) {
                	true => {
                		let ret = self.inline_call(&function, exps);
                		// unwrap the result to return a field element
						match ret[0].clone() {
            				TypedExpression::FieldElement(e) => e,
            				_ => panic!("")
            			}
                	},
                	false => FieldElementExpression::FunctionCall(id, exps)
                }
            },
            // default
            e => fold_field_expression(self, e)
        }
	}
}