use criterion::{criterion_group, criterion_main, Criterion};
use pico_sat::*;

fn one_of_expression(count: usize) {
    let mut vars = Variables::new();
    let mut literals = Vec::new();
    for _ in 0..count {
        literals.push(lit(vars.create()))
    }
    let one_of_expr = one_of(literals);
    let count_vars = vars.count();
    let mut cnf = one_of_expr.to_cnf(&mut vars);
    let answers = solve_all(&mut cnf, count_vars);
    assert!(!answers.is_empty());
}

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("one_of 30", |b| b.iter(|| one_of_expression(30)));
    c.bench_function("one_of 60", |b| b.iter(|| one_of_expression(60)));
    c.bench_function("one_of 120", |b| b.iter(|| one_of_expression(120)));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
