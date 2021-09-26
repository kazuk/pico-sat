use std::collections::HashMap;

use criterion::{criterion_group, criterion_main, Criterion};
use pico_sat::{solver::solve_all_verbose, *};

fn n_queen_formula(vars: &mut Variables, size: usize) -> Node {
    let mut board = Vec::new();
    for _ in 0..size {
        let mut line = Vec::new();
        for _ in 0..size {
            line.push(lit(vars.create()));
        }
        board.push(line);
    }
    let mut formula = Vec::new();

    let mut right_down = HashMap::new();
    let mut left_down = HashMap::new();
    let mut row_group = HashMap::new();
    let mut col_group = HashMap::new();

    for row in 0..size {
        for col in 0..size {
            let group = row_group.entry(row).or_insert(Vec::new());
            group.push(board[row][col].clone());
            let group = col_group.entry(col).or_insert(Vec::new());
            group.push(board[row][col].clone());

            let group = right_down
                .entry(row as i32 - ((col as i32) + 1))
                .or_insert(Vec::new());
            group.push(board[row][col].clone());
            let group = left_down
                .entry(row as i32 + ((col as i32) + 1))
                .or_insert(Vec::new());
            group.push(board[row][col].clone());
        }
    }
    for (_, n) in row_group {
        formula.push(one_of(n));
    }
    for (_, n) in col_group {
        formula.push(one_of(n));
    }
    for (_, n) in right_down {
        if n.len() == 1 {
            continue;
        }
        formula.push(zero_or_one_of(n))
    }
    for (_, n) in left_down {
        if n.len() == 1 {
            continue;
        }
        formula.push(zero_or_one_of(n))
    }
    formula.sort_by(|l, r| format!("{}", l).partial_cmp(&format!("{}", r)).unwrap());
    and(formula.iter().collect())
}

fn build_cnf_and_solve(node: &Node, vars: &mut Variables) {
    let mut cnf = node.to_cnf(vars);
    let answer = solve_all_verbose(&mut cnf, 16);
    assert!(answer.len() > 0);
}

pub fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("4 queen all", |b| {
        let mut vars = Variables::new();
        let formula = n_queen_formula(&mut vars, 4);
        b.iter(|| build_cnf_and_solve(&formula, &mut vars))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
