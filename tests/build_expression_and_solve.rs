use pico_sat::{lit, one_of, solve_all, Variables};
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
    trace!("build cnf");
    let mut solver_input = one.to_cnf(&mut vars);
    trace!("solve");
    let answers = solve_all(&mut solver_input);
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
    let mut solver_input = one.to_cnf(&mut vars);
    trace!("solve");
    let answers = solve_all(&mut solver_input);
    assert_eq!(answers.len(), 25);
}
