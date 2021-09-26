use super::{
    dpll_split, find_max_used_variable, is_sat, is_unsat, solve_partial, Cnf, SolverAction,
};

use async_recursion::async_recursion;
use tokio::sync::mpsc::Sender;

#[async_recursion]
async fn solve_async_internal(
    prefix: &mut Vec<SolverAction>,
    input: &mut Cnf,
    tx_complete: Sender<Option<Vec<SolverAction>>>,
) {
    if tx_complete.is_closed() {
        return;
    };
    loop {
        let mut result = solve_partial(input);
        if is_unsat(input) {
            if tx_complete.is_closed() {
                return;
            };
            tx_complete.send(None).await.unwrap();
            return;
        }

        if tx_complete.is_closed() {
            return;
        };
        prefix.append(&mut result);
        if is_sat(input) {
            tx_complete.send(Some(result)).await.unwrap();
            return;
        }
        let split_point = find_max_used_variable(input).unwrap();
        let (mut false_part, _, _) = dpll_split(input, &split_point);
        if tx_complete.is_closed() {
            return;
        };

        let mut prefix_false = prefix.clone();
        let tx_complete_child = tx_complete.clone();
        tokio::spawn(async move {
            prefix_false.push(SolverAction::Split(split_point.f()));
            solve_async_internal(&mut prefix_false, &mut false_part, tx_complete_child).await;
        });
        prefix.push(SolverAction::Split(split_point.t()));
    }
}

/// async version of pico_sat::solver::solve_one
pub async fn solve_one_async(input: Cnf) -> Option<Vec<SolverAction>> {
    let (tx, mut rx) = tokio::sync::mpsc::channel(1);
    tokio::spawn(async move {
        solve_async_internal(&mut vec![], &mut input.clone(), tx);
    });
    // get first answer;
    let result = rx.recv().await.unwrap();
    rx.close(); // stops other worker
    result
}

/// async version of pico_sat::solver::solve_all
pub async fn solve_all_async(input: Cnf) -> Vec<Vec<SolverAction>> {
    let (tx, mut rx) = tokio::sync::mpsc::channel(1);
    tokio::spawn(async move {
        solve_async_internal(&mut vec![], &mut input.clone(), tx);
    });
    let mut answers = Vec::new();
    while let Some(result) = rx.recv().await {
        if let Some(single_answer) = result {
            answers.push(single_answer)
        } // else some branch reaches UNSAT
    }
    answers
}
