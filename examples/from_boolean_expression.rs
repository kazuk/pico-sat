use pico_sat::{heuristics::SplitOnMaxVars, lit, solve_all, xor2, Variables};

fn main() {
    println!("this example solves: 1 xor 2");
    let mut vars = Variables::new();
    let lit1 = lit(vars.create());
    let lit2 = lit(vars.create());
    let node = xor2(&lit1, &lit2);
    let count_vars = vars.count();
    let mut formular = node.to_cnf(&mut vars);
    let answers = solve_all(
        &mut formular,
        count_vars,
        &SplitOnMaxVars {
            count_vars: vars.count() as usize,
        },
    );

    for (i, answer) in answers.iter().enumerate() {
        println!("Solved answer {:}", i);
        for lit in answer {
            println!("{:} {:}", lit.var().index(), lit.value());
        }
    }
}
