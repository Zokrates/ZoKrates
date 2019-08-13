#[macro_use]
extern crate criterion;
extern crate zokrates_core;
extern crate zokrates_field;

use criterion::black_box;
use criterion::Criterion;
use zokrates_core::ir::folder::Folder;

use zokrates_core::ir;
use zokrates_core::optimizer::RedefinitionOptimizer;
use zokrates_field::field::FieldPrime;

fn bench_foo(c: &mut Criterion) {
    c.bench_function("reduce100", |b| {
        b.iter(|| {
            let f = ir::Function::<FieldPrime> {
                arguments: vec![],
                id: "main".to_string(),
                returns: vec![],
                statements: (0..100)
                    .map(|i| {
                        ir::Statement::definition(
                            ir::FlatVariable::new(i + 1),
                            ir::FlatVariable::new(i),
                        )
                    })
                    .collect(),
            };

            let mut optimizer = RedefinitionOptimizer::new();
            optimizer.fold_function(f);
        })
    });

    c.bench_function("reduce1000", |b| {
        b.iter(|| {
            let f = ir::Function::<FieldPrime> {
                arguments: vec![],
                id: "main".to_string(),
                returns: vec![],
                statements: (0..1000)
                    .map(|i| {
                        ir::Statement::definition(
                            ir::FlatVariable::new(i + 1),
                            ir::FlatVariable::new(i),
                        )
                    })
                    .collect(),
            };

            let mut optimizer = RedefinitionOptimizer::new();
            optimizer.fold_function(f);
        })
    });

    c.bench_function("reduce10000", |b| {
        b.iter(|| {
            let f = ir::Function::<FieldPrime> {
                arguments: vec![],
                id: "main".to_string(),
                returns: vec![],
                statements: (0..10000)
                    .map(|i| {
                        ir::Statement::definition(
                            ir::FlatVariable::new(i + 1),
                            ir::FlatVariable::new(i),
                        )
                    })
                    .collect(),
            };

            let mut optimizer = RedefinitionOptimizer::new();
            optimizer.fold_function(f);
        })
    });
}

criterion_group!(benches, bench_foo);
criterion_main!(benches);
