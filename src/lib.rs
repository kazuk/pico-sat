#![warn(missing_docs)]

//! # crate `pico-sat`
//!
//! Minimal implementation of DPLL SAT Solver
//!
//! # How to use solver
//!
//! ```rust
//! use pico_sat::{Variables, solve_one};
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
//! match solve_one(&mut f) {
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
mod solver;

pub use boolean_expression::{Node, TreeBuilder};
pub use solver::{Literal, Variable, Variables};

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
/// use pico_sat::{Variables, solve_one};
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
/// match solve_one(&mut f) {
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
pub fn solve_one(input: &mut Vec<Vec<Literal>>) -> Option<Vec<Literal>> {
    solver::solve_one(input)
}

/// SAT solve and returns all result
pub fn solve_all(input: &mut Vec<Vec<Literal>>) -> Vec<Vec<Literal>> {
    solver::solve_all(input)
}

/// Async version of solve_one
#[cfg(feature = "async")]
pub async fn solve_one_async(input: Vec<Vec<Literal>>) -> Option<Vec<Literal>> {
    solver::async_solver::solve_one_async(input).await
}

/// Async version of solve_all
#[cfg(feature = "async")]
pub async fn solve_all_async(input: Vec<Vec<Literal>>) -> Vec<Vec<Literal>> {
    solver::async_solver::solve_all_async(input).await
}
