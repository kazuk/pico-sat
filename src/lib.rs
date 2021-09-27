#![warn(missing_docs)]

//! # crate `pico-sat`
//!
//! Minimal implementation of DPLL SAT Solver
//!
//! # How to use solver
//!
//! ```rust
//! use pico_sat::{Variables, solve_one, heuristics::SplitOnMaxVars };
//! let mut vars = Variables::new();
//! let o = vars.create();
//! let p = vars.create();
//! let q = vars.create();
//! let r = vars.create();
//! let mut f = vec![
//!    vec![ p.t(), q.t(), r.f() ],
//!    vec![ p.f(), r.f() ],
//!    vec![ r.t() ]
//! ];
//! match solve_one(&mut f, 3, &SplitOnMaxVars { count_vars: vars.count() as usize} ) {
//!     Some(answer) => {
//!         // SAT
//!         assert_eq!(answer.len(), 3);
//!         assert_eq!(answer[0], r.t(), "first R");
//!         assert_eq!(answer[1], p.f(), "second ~P");
//!         assert_eq!(answer[2], q.t(), "third Q");
//!         assert!( o.is_dontcare(&answer) );
//!         assert!( p.is_false(&answer) );
//!         assert!( q.is_true(&answer) );
//!         assert!( r.is_true(&answer) );
//!     }
//!     None => {
//!         panic!("UNSAT")
//!     }
//! }
//!
//! ```

mod boolean_expression;

/// DIMACS format support
pub mod dimacs;

/// module solver
///
/// DPLL SAT Solver and Solving step functions.
pub mod solver;

use std::cmp::Ordering;

pub use boolean_expression::*;
use solver::{Cnf, SolverHeuristics};
pub use solver::{Literal, Variable, Variables};

/// heuristic option for SAT solver
pub mod heuristics;

/// SAT solve and returns one result
///
/// # Arguments
///
/// * `input` - vector of vector of literal, outer vector is AND set, inner vector is OR set.
///
/// # Return Value
///
/// * `Option::Some(Vec<Literal>)` SAT answer
/// * `Option::None` UNSAT answer
///
/// # Examples
///
/// ```rust
/// use pico_sat::{Variables, solve_one, heuristics::SplitOnMaxVars};
/// let mut vars = Variables::new();
/// let o = vars.create();
/// let p = vars.create();
/// let q = vars.create();
/// let r = vars.create();
/// let mut f = vec![
///    vec![ p.t(), q.t(), r.f() ], //    ( P ||  Q || !R )
///    vec![ p.f(), r.f() ],        // && (!P || !R )
///    vec![ r.t() ]                // && ( R)
/// ];
/// match solve_one(&mut f, 4, &SplitOnMaxVars { count_vars: vars.count() as usize} ) {
///     Some(answer) => {
///         // SAT
///         assert_eq!(answer.len(), 3);
///         assert_eq!(answer[0], r.t(), "first R");
///         assert_eq!(answer[1], p.f(), "second ~P");
///         assert_eq!(answer[2], q.t(), "third Q");
///         assert!( o.is_dontcare(&answer) );
///         assert!( p.is_false(&answer) );
///         assert!( q.is_true(&answer) );
///         assert!( r.is_true(&answer) );
///     }
///     None => {
///         panic!("UNSAT")
///     }
/// }
/// ```
pub fn solve_one<S: SolverHeuristics>(
    input: &mut Vec<Vec<Literal>>,
    satisfy_vars: u32,
    heuristics: &S,
) -> Option<Vec<Literal>> {
    solver::solve_one(input, satisfy_vars, heuristics)
}

/// SAT solve and returns all result
pub fn solve_all<S: SolverHeuristics>(
    input: &mut Vec<Vec<Literal>>,
    satisfy_vars: u32,
    heuristics: &S,
) -> Vec<Vec<Literal>> {
    solver::solve_all(input, satisfy_vars, heuristics)
}

/// Async version of solve_one
#[cfg(feature = "async")]
pub async fn solve_one_async(input: Vec<Vec<Literal>>) -> Option<Vec<Literal>> {
    use crate::solver::SolverAction;

    let result = solver::async_solver::solve_one_async(input).await;
    result.map(|r| SolverAction::simplify_answer(&r))
}

/// Async version of solve_all
#[cfg(feature = "async")]
pub async fn solve_all_async(input: Vec<Vec<Literal>>) -> Vec<Vec<Literal>> {
    use solver::SolverAction;

    let results = solver::async_solver::solve_all_async(input).await;
    results
        .iter()
        .map(|r| SolverAction::simplify_answer(r))
        .collect()
}

#[allow(clippy::ptr_arg)]
fn node_compare(left: &Vec<Literal>, right: &Vec<Literal>) -> Ordering {
    match (left.len(), right.len()) {
        (x, y) if x < y => Ordering::Less,
        (x, y) if x > y => Ordering::Greater,
        _ => {
            for index in 0..left.len() {
                match left[index]
                    .var()
                    .index()
                    .partial_cmp(&right[index].var().index())
                    .unwrap()
                {
                    Ordering::Less => return Ordering::Less,
                    Ordering::Greater => return Ordering::Greater,
                    Ordering::Equal => {}
                }
            }
            Ordering::Equal
        }
    }
}

/// canonicalize cnf
///
/// Sort cnf nodes and items
pub fn canonicalize(input: Cnf) -> Cnf {
    let mut result: Cnf = input
        .iter()
        .map(|n| {
            let mut items = n.clone();
            items.sort_by(|left, right| {
                left.var()
                    .index()
                    .partial_cmp(&right.var().index())
                    .unwrap()
            });
            items
        })
        .collect();
    result.sort_by(node_compare);
    result
}
