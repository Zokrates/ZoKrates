use std::collections::HashMap;

use zokrates_ast::{
    common::{ModuleMap, Span},
    ir::{ProgIterator, Statement},
};

#[derive(Default, Debug)]
pub struct HeatMap {
    /// the total number of constraints
    count: usize,
    /// for each span, how many constraints are linked to it
    map: HashMap<Option<Span>, usize>,
}

impl HeatMap {
    pub fn display(&self, module_map: &ModuleMap) -> String {
        let count = self.count;

        let mut stats: Vec<_> = self.map.iter().collect();

        stats.sort_by(|a, b| b.1.partial_cmp(a.1).unwrap());

        stats
            .iter()
            .map(|(span, c)| {
                format!(
                    "{:>4.2}% : {}",
                    (**c as f64) / (count as f64) * 100.0,
                    span.map(|s| s.resolve(module_map).to_string())
                        .unwrap_or_else(|| String::from("???")),
                )
            })
            .collect::<Vec<_>>()
            .join("\n")
    }
}

pub fn profile<'ast, T, I: IntoIterator<Item = Statement<'ast, T>>>(
    prog: ProgIterator<'ast, T, I>,
) -> HeatMap {
    prog.statements
        .into_iter()
        .fold(HeatMap::default(), |mut heat_map, s| match s {
            Statement::Constraint(s) => {
                heat_map.count += 1;
                *heat_map.map.entry(s.span).or_default() += 1;
                heat_map
            }
            _ => heat_map,
        })
}
