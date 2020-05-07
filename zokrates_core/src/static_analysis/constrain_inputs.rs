// Add runtime boolean checks on user inputs

// Example:
// ```zokrates
// struct Foo {
//    bar: bool
// }

// def main(Foo f) -> ():
//    f.bar == f.bar && f.bar
//    return
// ```

// Becomes

// ```zokrates
// struct Foo {
//    bar: bool
// }

// def main(Foo f) -> ():
//    f.bar == f.bar && f.bar
//    return
// ```

// @file constrain_inputs.rs
// @author Thibaut Schaeffer <thibaut@schaeff.fr>
// @date 2019

use crate::zir::folder::Folder;
use crate::zir::types::Type;
use crate::zir::*;
use std::collections::HashSet;
use zokrates_field::Field;

pub struct InputConstrainer<'ast, T: Field> {
    uints: HashSet<Identifier<'ast>>,
    next_var_id: usize,
    constraints: Vec<ZirStatement<'ast, T>>,
}

impl<'ast, T: Field> InputConstrainer<'ast, T> {
    fn new() -> Self {
        InputConstrainer {
            uints: HashSet::new(),
            next_var_id: 0,
            constraints: vec![],
        }
    }

    pub fn constrain(p: ZirProgram<T>) -> ZirProgram<T> {
        InputConstrainer::new().fold_program(p)
    }

    fn constrain_bits(&mut self, u: UExpression<'ast, T>) {
        // let bitwidth = u.bitwidth;
        // let u = UExpression {
        //     metadata: Some(UMetadata {
        //         bitwidth: Some(bitwidth),
        //         should_reduce: Some(false)
        //     }),
        //     ..u
        // };
        // let bit_input = (self.next_var_id..self.next_var_id + bitwidth).map(|i| Variable::with_id_and_type(
        //     Identifier::Internal("bit_input_array", i),
        //     Type::FieldElement
        // )).collect();
        // self.next_var_id += bitwidth;
        // self.constraints.push(ZirStatement::MultipleDefinition(
        //     bit_input,
        //     ZirExpressionList::FunctionCall(
        //         match bitwidth {
        //             8 => crate::embed::FlatEmbed::CheckU8.key::<T>().into(),
        //             16 => crate::embed::FlatEmbed::CheckU16.key::<T>().into(),
        //             32 => crate::embed::FlatEmbed::CheckU32.key::<T>().into(),
        //             _ => unreachable!(),
        //         },
        //         vec![u.into()],
        //         vec![Type::FieldElement; bitwidth],
        //     ),
        // ));
    }

    fn constrain_expression(&mut self, e: ZirExpression<'ast, T>) {
        match e {
            ZirExpression::FieldElement(_) => {}
            ZirExpression::Boolean(b) => self.constraints.push(ZirStatement::Condition(
                b.clone().into(),
                BooleanExpression::And(box b.clone(), box b).into(),
            )),
            ZirExpression::Uint(u) => {
                self.constrain_bits(u);
            }
        }
    }
}

impl<'ast, T: Field> Folder<'ast, T> for InputConstrainer<'ast, T> {
    fn fold_parameter(&mut self, p: Parameter<'ast>) -> Parameter<'ast> {
        let v = p.id.clone();

        let e = match v.get_type() {
            Type::FieldElement => FieldElementExpression::Identifier(v.id).into(),
            Type::Boolean => BooleanExpression::Identifier(v.id).into(),
            Type::Uint(bitwidth) => {
                self.uints.insert(v.id.clone());
                UExpressionInner::Identifier(v.id).annotate(bitwidth).into()
            }
        };

        self.constrain_expression(e);

        p
    }

    fn fold_function(&mut self, f: ZirFunction<'ast, T>) -> ZirFunction<'ast, T> {
        let arguments: Vec<_> = f
            .arguments
            .into_iter()
            .map(|a| self.fold_parameter(a))
            .collect();
        let statements: Vec<_> = f
            .statements
            .into_iter()
            .flat_map(|s| self.fold_statement(s))
            .collect();

        ZirFunction {
            arguments,
            statements: self.constraints.drain(..).chain(statements).collect(),
            ..f
        }
    }
}
