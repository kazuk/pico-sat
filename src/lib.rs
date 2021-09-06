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

pub use solver::{solve_all, solve_one, Variables};
