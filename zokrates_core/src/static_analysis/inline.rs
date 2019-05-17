// use crate::typed_absy::folder::*;
// use crate::typed_absy::Folder;
// use crate::typed_absy::*;
// use crate::types::{Signature, Type};
// use std::collections::HashMap;
// use zokrates_field::field::Field;

// #[derive(Debug)]
// pub struct Inliner<T: Field> {
//     functions: TypedFunctionSymbols<T>,
//     modules: TypedModules<T>,
//     statements_buffer: Vec<TypedStatement<T>>,
//     context: Vec<(String, usize)>,
//     call_count: HashMap<String, usize>,
// }

// impl<T: Field> Inliner<T> {
//     fn new() -> Self {
//         Inliner {
//             functions: HashMap::new(),
//             modules: HashMap::new(),
//             statements_buffer: vec![],
//             context: vec![],
//             call_count: HashMap::new(),
//         }
//     }

//     fn should_inline(
//         &self,
//         function: &Option<TypedFunctionSymbol<T>>,
//         arguments: &Vec<TypedExpression<T>>,
//     ) -> bool {
//         // we should define a heuristic here
//         // currently it doesn't seem like there's a tradeoff as everything gets inlined in flattening anyway (apart from compiling performance, as inlining
//         // in flattening should be faster and less memory intensive)
//         // however, using backends such as bellman, we could avoid flattening and "stream" the computation
//         // at proving time, the tradeoff becomes code size (not inlining keeps only one copy of each function) vs optimisation
//         // (inlining enables constant propagation through function calls, which cannot be achieved by our final optimiser in some cases)
//         // for now, we inline functions whose non-array parameters are constant, as this covers our main use case for inlining: propagation of
//         // constant array indices
//         // match function {
//         //     Some(..) => {
//         //         // check whether non-array arguments are constant
//         //         arguments.iter().all(|e| match e {
//         //             TypedExpression::FieldElementArray(..) => true,
//         //             TypedExpression::FieldElement(FieldElementExpression::Number(..)) => true,
//         //             TypedExpression::Boolean(BooleanExpression::Value(..)) => true,
//         //             _ => false,
//         //         })
//         //     }
//         //     None => false,
//         // }
//         true
//     }

//     // inline a call to `function` taking `expressions` as inputs
//     // this function mutates `self.call` by incrementing the counter for `function`, and mutates `self.context`
//     fn inline_call(
//         &mut self,
//         symbol: &TypedFunctionSymbol<T>,
//         expressions: Vec<TypedExpression<T>>,
//     ) -> Vec<TypedExpression<T>> {
//         match symbol {
//             TypedFunctionSymbol::Here(function) => {
//                 self.call_count
//                     .entry(function.to_slug())
//                     .and_modify(|i| *i += 1)
//                     .or_insert(1);
//                 self.context.push((
//                     function.to_slug(),
//                     *self.call_count.get(&function.to_slug()).unwrap(),
//                 ));

//                 // add definitions for the inputs
//                 let mut inputs_bindings = function
//                     .arguments
//                     .iter()
//                     .zip(expressions)
//                     .map(|(a, e)| {
//                         TypedStatement::Definition(
//                             TypedAssignee::Identifier(self.fold_variable(a.id.clone())),
//                             e,
//                         )
//                     })
//                     .collect();
//                 self.statements_buffer.append(&mut inputs_bindings);

//                 // filter out the return statement and keep it aside
//                 let (mut statements, ret): (Vec<_>, Vec<_>) = function
//                     .statements
//                     .clone()
//                     .into_iter()
//                     .flat_map(|s| self.fold_statement(s))
//                     .partition(|s| match s {
//                         TypedStatement::Return(..) => false,
//                         _ => true,
//                     });

//                 // add all statements to the buffer
//                 self.statements_buffer.append(&mut statements);

//                 // remove this call from the context
//                 self.context.pop();

//                 match ret[0].clone() {
//                     TypedStatement::Return(exprs) => exprs,
//                     _ => panic!(""),
//                 }
//             }
//             _ => unimplemented!(),
//         }
//     }

//     pub fn inline(prog: TypedProgram<T>) -> TypedProgram<T> {
//         Inliner::new().fold_program(prog)
//     }
// }

// impl<T: Field> Folder<T> for Inliner<T> {
//     fn fold_program(&mut self, p: TypedProgram<T>) -> TypedProgram<T> {
//         self.modules = p.modules;
//         let main = p.main;
//         self.functions = main.functions.clone();
//         TypedProgram {
//             main: TypedModule {
//                 imported_functions: vec![],
//                 imports: vec![],
//                 functions: main
//                     .functions
//                     .into_iter()
//                     .filter(|(k, v)| k.id == "main")
//                     .take(1)
//                     .map(|(k, v)| (k, self.fold_function_symbol(v)))
//                     .collect(),
//             },
//             modules: HashMap::new(),
//         }
//     }

//     fn fold_module(&mut self, m: TypedModule<T>) -> TypedModule<T> {
//         unreachable!("we don't want to inline modules, only functions!")
//     }

//     // prefix all names with the context
//     fn fold_name(&mut self, n: String) -> String {
//         match self.context.len() {
//             0 => n,
//             _ => format!(
//                 "{}_{}",
//                 self.context
//                     .iter()
//                     .map(|(s, i)| format!("{}_{}", s, i))
//                     .collect::<Vec<_>>()
//                     .join("_"),
//                 n
//             ),
//         }
//     }

//     fn fold_function_symbol(&mut self, s: TypedFunctionSymbol<T>) -> TypedFunctionSymbol<T> {
//         match s {
//             TypedFunctionSymbol::Here(function) => TypedFunctionSymbol::Here(self.fold_function(function)),
//             TypedFunctionSymbol::There(function_id, module_id) => {
//             	let mut inliner = Inliner::new();
//             	let module = self.modules.get(&module_id).unwrap();
//             	let function_symbol  = module.functions.get(&function_id).unwrap().clone();

//             	inliner.modules = self.modules.clone();
//             	inliner.functions = module.functions.clone();

// 				inliner.fold_function_symbol(function_symbol)
//             },
//         }
//     }

//     // inline calls which return a field element
//     fn fold_field_expression(&mut self, e: FieldElementExpression<T>) -> FieldElementExpression<T> {
//     	println!("{:#?}", self);

//         match e {
//             FieldElementExpression::FunctionCall(key, exps) => {
//                 let exps: Vec<_> = exps.into_iter().map(|e| self.fold_expression(e)).collect();

//                 let passed_signature = Signature::new()
//                     .inputs(exps.iter().map(|e| e.get_type()).collect())
//                     .outputs(vec![Type::FieldElement]);

//                 println!("{:?} {:?}", key, self.functions);

//                 // find the function
//                 let function = self.functions.get(&key).cloned();

//                 match self.should_inline(&function, &exps) {
//                     true => {
//                         let ret = self.inline_call(&function.unwrap(), exps);
//                         // unwrap the result to return a field element
//                         match ret[0].clone() {
//                             TypedExpression::FieldElement(e) => e,
//                             _ => panic!(""),
//                         }
//                     }
//                     false => FieldElementExpression::FunctionCall(key, exps),
//                 }
//             }
//             // default
//             e => fold_field_expression(self, e),
//         }
//     }
// }

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use zokrates_field::field::FieldPrime;

//     #[cfg(test)]
//     mod heuristics {
//         use super::*;

//         #[test]
//         fn inline_constant_field() {
//             let f: TypedFunction<FieldPrime> = TypedFunction {
//                 id: String::from("foo"),
//                 arguments: vec![
//                     Parameter::private(Variable::field_element("a")),
//                     Parameter::private(Variable::field_array("b", 3)),
//                 ],
//                 statements: vec![TypedStatement::Return(vec![
//                     FieldElementExpression::Select(
//                         box FieldElementArrayExpression::Identifier(3, String::from("b")),
//                         box FieldElementExpression::Identifier(String::from("a")),
//                     )
//                     .into(),
//                 ])],
//                 signature: Signature::new()
//                     .inputs(vec![Type::FieldElement, Type::FieldElementArray(3)])
//                     .outputs(vec![Type::FieldElement]),
//             };

//             let arguments = vec![
//                 FieldElementExpression::Number(FieldPrime::from(0)).into(),
//                 FieldElementArrayExpression::Identifier(3, String::from("random")).into(),
//             ];

//             let i = Inliner::new();

//             assert!(i.should_inline(&Some(f), &arguments));
//         }

//         #[test]
//         fn no_inline_non_constant_field() {
//             let f: TypedFunction<FieldPrime> = TypedFunction {
//                 id: String::from("foo"),
//                 arguments: vec![
//                     Parameter::private(Variable::field_element("a")),
//                     Parameter::private(Variable::field_array("b", 3)),
//                 ],
//                 statements: vec![TypedStatement::Return(vec![
//                     FieldElementExpression::Select(
//                         box FieldElementArrayExpression::Identifier(3, String::from("b")),
//                         box FieldElementExpression::Identifier(String::from("a")),
//                     )
//                     .into(),
//                 ])],
//                 signature: Signature::new()
//                     .inputs(vec![Type::FieldElement, Type::FieldElementArray(3)])
//                     .outputs(vec![Type::FieldElement]),
//             };

//             let arguments = vec![
//                 FieldElementExpression::Identifier(String::from("notconstant")).into(),
//                 FieldElementArrayExpression::Identifier(3, String::from("random")).into(),
//             ];

//             let i = Inliner::new();

//             assert!(!i.should_inline(&Some(f), &arguments));
//         }
//     }
// }
