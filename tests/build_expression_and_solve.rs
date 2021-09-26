use std::collections::HashMap;

use pico_sat::{
    and,
    dimacs::DimacsWriter,
    lit, one_of, solve_all,
    solver::{dpll_split, solve_all_verbose, Cnf},
    zero_or_one_of, Node, Variable, Variables,
};
use tracing::trace;
use tracing_test::traced_test;

#[test]
#[traced_test]
fn test_choose1_in_30() {
    trace!("start test_choose1_in_30");
    let mut vars = Variables::new();

    let mut items = Vec::new();
    for _i in 0..30 {
        items.push(lit(vars.create()))
    }
    let one = one_of(items);
    let count_vars = vars.count();
    trace!("build cnf");
    let mut solver_input = one.to_cnf(&mut vars);
    trace!("solve");
    let answers = solve_all(&mut solver_input, count_vars);
    assert_eq!(answers.len(), 30);

    for answer in answers {
        let mut true_count = 0;
        let mut false_count = 0;
        for lit in &answer {
            if lit.var().index() > 30 {
                continue;
            }
            if lit.value() {
                true_count += 1;
            } else {
                false_count += 1;
            }
        }
        assert_eq!(true_count, 1, "no 1 true in var 1..30 {:?}", answer);
        assert_eq!(false_count, 29, "no 29 false in var 1..30{:?}", answer);
    }
}

#[test]
fn nested_one_of() {
    let mut vars = Variables::new();
    let mut parents = Vec::new();
    for _i in 0..5 {
        let mut items = Vec::new();
        for _i in 0..5 {
            items.push(lit(vars.create()))
        }
        parents.push(one_of(items));
    }
    let one = one_of(parents);
    let count_vars = vars.count();
    let mut solver_input = one.to_cnf(&mut vars);
    eprintln!("solver_input={:?}", solver_input);
    trace!("solve");
    let answers = solve_all(&mut solver_input, count_vars);
    let mut hash = HashMap::new();

    for answer in answers {
        for answer_item in answer {
            if answer_item.var().index() <= 25 && answer_item.value() {
                let entry = hash.entry(answer_item.var().index()).or_insert(0);
                *entry += 1;
            }
        }
    }
    assert!(hash.len() == 25);
}

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

#[test]
fn n_queen_4_split() {
    fn dimacs_text(form: &Cnf) -> String {
        let mut buffer = Vec::new();
        let mut cursor = std::io::Cursor::new(&mut buffer);
        let writer = DimacsWriter::new(vec![]);
        writer.write(&mut cursor, &form).unwrap();
        String::from_utf8(buffer).unwrap()
    }

    let mut vars = Variables::new();
    let node = n_queen_formula(&mut vars, 4);
    assert_eq!( format!("{}",node), "((([12]&&[~15])||([~12]&&[15])||([~12]&&[~15]))&&(([13]&&[~14]&&[~15]&&[~16])||([~13]&&[14]&&[~15]&&[~16])||([~13]&&[~14]&&[15]&&[~16])||([~13]&&[~14]&&[~15]&&[16]))&&(([1]&&[~2]&&[~3]&&[~4])||([~1]&&[2]&&[~3]&&[~4])||([~1]&&[~2]&&[3]&&[~4])||([~1]&&[~2]&&[~3]&&[4]))&&(([1]&&[~5]&&[~9]&&[~13])||([~1]&&[5]&&[~9]&&[~13])||([~1]&&[~5]&&[9]&&[~13])||([~1]&&[~5]&&[~9]&&[13]))&&(([1]&&[~6]&&[~11]&&[~16])||([~1]&&[6]&&[~11]&&[~16])||([~1]&&[~6]&&[11]&&[~16])||([~1]&&[~6]&&[~11]&&[16])||([~1]&&[~6]&&[~11]&&[~16]))&&(([2]&&[~5])||([~2]&&[5])||([~2]&&[~5]))&&(([2]&&[~6]&&[~10]&&[~14])||([~2]&&[6]&&[~10]&&[~14])||([~2]&&[~6]&&[10]&&[~14])||([~2]&&[~6]&&[~10]&&[14]))&&(([2]&&[~7]&&[~12])||([~2]&&[7]&&[~12])||([~2]&&[~7]&&[12])||([~2]&&[~7]&&[~12]))&&(([3]&&[~6]&&[~9])||([~3]&&[6]&&[~9])||([~3]&&[~6]&&[9])||([~3]&&[~6]&&[~9]))&&(([3]&&[~7]&&[~11]&&[~15])||([~3]&&[7]&&[~11]&&[~15])||([~3]&&[~7]&&[11]&&[~15])||([~3]&&[~7]&&[~11]&&[15]))&&(([3]&&[~8])||([~3]&&[8])||([~3]&&[~8]))&&(([4]&&[~7]&&[~10]&&[~13])||([~4]&&[7]&&[~10]&&[~13])||([~4]&&[~7]&&[10]&&[~13])||([~4]&&[~7]&&[~10]&&[13])||([~4]&&[~7]&&[~10]&&[~13]))&&(([4]&&[~8]&&[~12]&&[~16])||([~4]&&[8]&&[~12]&&[~16])||([~4]&&[~8]&&[12]&&[~16])||([~4]&&[~8]&&[~12]&&[16]))&&(([5]&&[~10]&&[~15])||([~5]&&[10]&&[~15])||([~5]&&[~10]&&[15])||([~5]&&[~10]&&[~15]))&&(([5]&&[~6]&&[~7]&&[~8])||([~5]&&[6]&&[~7]&&[~8])||([~5]&&[~6]&&[7]&&[~8])||([~5]&&[~6]&&[~7]&&[8]))&&(([8]&&[~11]&&[~14])||([~8]&&[11]&&[~14])||([~8]&&[~11]&&[14])||([~8]&&[~11]&&[~14]))&&(([9]&&[~10]&&[~11]&&[~12])||([~9]&&[10]&&[~11]&&[~12])||([~9]&&[~10]&&[11]&&[~12])||([~9]&&[~10]&&[~11]&&[12]))&&(([9]&&[~14])||([~9]&&[14])||([~9]&&[~14])))");

    let mut form = node.to_cnf(&mut vars);
    let dimacs = String::from_utf8(include_bytes!("./data/nqueen_4.dimacs").to_vec()).unwrap();
    assert_eq!(dimacs_text(&form), dimacs);

    let (false_part, _, _) = dpll_split(&mut form, &Variable::from_index(2));

    let dimacs = String::from_utf8(include_bytes!("./data/nqueen_4_2_t.dimacs").to_vec()).unwrap();
    assert_eq!(dimacs_text(&form), dimacs);
    let dimacs = String::from_utf8(include_bytes!("./data/nqueen_4_2_f.dimacs").to_vec()).unwrap();
    assert_eq!(dimacs_text(&false_part), dimacs);
}

#[test]
fn n_queen_4_all() {
    let mut vars = Variables::new();
    let node = n_queen_formula(&mut vars, 4);
    let count_vars = vars.count();
    assert_eq!( format!("{}",node), "((([12]&&[~15])||([~12]&&[15])||([~12]&&[~15]))&&(([13]&&[~14]&&[~15]&&[~16])||([~13]&&[14]&&[~15]&&[~16])||([~13]&&[~14]&&[15]&&[~16])||([~13]&&[~14]&&[~15]&&[16]))&&(([1]&&[~2]&&[~3]&&[~4])||([~1]&&[2]&&[~3]&&[~4])||([~1]&&[~2]&&[3]&&[~4])||([~1]&&[~2]&&[~3]&&[4]))&&(([1]&&[~5]&&[~9]&&[~13])||([~1]&&[5]&&[~9]&&[~13])||([~1]&&[~5]&&[9]&&[~13])||([~1]&&[~5]&&[~9]&&[13]))&&(([1]&&[~6]&&[~11]&&[~16])||([~1]&&[6]&&[~11]&&[~16])||([~1]&&[~6]&&[11]&&[~16])||([~1]&&[~6]&&[~11]&&[16])||([~1]&&[~6]&&[~11]&&[~16]))&&(([2]&&[~5])||([~2]&&[5])||([~2]&&[~5]))&&(([2]&&[~6]&&[~10]&&[~14])||([~2]&&[6]&&[~10]&&[~14])||([~2]&&[~6]&&[10]&&[~14])||([~2]&&[~6]&&[~10]&&[14]))&&(([2]&&[~7]&&[~12])||([~2]&&[7]&&[~12])||([~2]&&[~7]&&[12])||([~2]&&[~7]&&[~12]))&&(([3]&&[~6]&&[~9])||([~3]&&[6]&&[~9])||([~3]&&[~6]&&[9])||([~3]&&[~6]&&[~9]))&&(([3]&&[~7]&&[~11]&&[~15])||([~3]&&[7]&&[~11]&&[~15])||([~3]&&[~7]&&[11]&&[~15])||([~3]&&[~7]&&[~11]&&[15]))&&(([3]&&[~8])||([~3]&&[8])||([~3]&&[~8]))&&(([4]&&[~7]&&[~10]&&[~13])||([~4]&&[7]&&[~10]&&[~13])||([~4]&&[~7]&&[10]&&[~13])||([~4]&&[~7]&&[~10]&&[13])||([~4]&&[~7]&&[~10]&&[~13]))&&(([4]&&[~8]&&[~12]&&[~16])||([~4]&&[8]&&[~12]&&[~16])||([~4]&&[~8]&&[12]&&[~16])||([~4]&&[~8]&&[~12]&&[16]))&&(([5]&&[~10]&&[~15])||([~5]&&[10]&&[~15])||([~5]&&[~10]&&[15])||([~5]&&[~10]&&[~15]))&&(([5]&&[~6]&&[~7]&&[~8])||([~5]&&[6]&&[~7]&&[~8])||([~5]&&[~6]&&[7]&&[~8])||([~5]&&[~6]&&[~7]&&[8]))&&(([8]&&[~11]&&[~14])||([~8]&&[11]&&[~14])||([~8]&&[~11]&&[14])||([~8]&&[~11]&&[~14]))&&(([9]&&[~10]&&[~11]&&[~12])||([~9]&&[10]&&[~11]&&[~12])||([~9]&&[~10]&&[11]&&[~12])||([~9]&&[~10]&&[~11]&&[12]))&&(([9]&&[~14])||([~9]&&[14])||([~9]&&[~14])))");

    let mut form = node.to_cnf(&mut vars);

    let result = solve_all_verbose(&mut form, count_vars);
    eprintln!("{:?}", result);
    assert_eq!(result.len(), 2);
}
