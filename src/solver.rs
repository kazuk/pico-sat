use arrayvec::ArrayVec;
use std::{
    cmp::Ordering,
    collections::{HashMap, HashSet},
    convert::TryInto,
    ops::Index,
};

/// async solvers
#[cfg(feature = "async")]
pub mod async_solver;

const SMALL_CAP: usize = 8;
/// Clause is literal vector
#[derive(Clone, Debug)]
pub enum Clause {
    /// Small clause, clause item less than 8
    Small(ArrayVec<Literal, SMALL_CAP>),
    /// Big clause, clause item more than 8
    Big(Vec<Literal>),
}

impl Clause {
    /// create small Clause
    pub fn new() -> Self {
        Clause::Small(ArrayVec::new())
    }

    /// create Clause contains one literal
    pub fn from_one(lit: Literal) -> Self {
        let mut result = Clause::new();
        result.push(lit);
        result
    }

    /// create Clause from litral vector
    pub fn from_vec(vec: Vec<Literal>) -> Self {
        if vec.len() > SMALL_CAP {
            Clause::Big(vec)
        } else {
            Clause::Small(vec.as_slice().try_into().unwrap())
        }
    }

    /// get clause length
    pub fn len(&self) -> usize {
        match self {
            Clause::Small(s) => s.len(),
            Clause::Big(b) => b.len(),
        }
    }

    /// true if clause is empty
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// check contains literal
    pub fn contains(&self, value: &Literal) -> bool {
        match self {
            Clause::Small(s) => s.contains(value),
            Clause::Big(b) => b.contains(value),
        }
    }

    /// get iterator
    pub fn iter(&self) -> std::slice::Iter<'_, Literal> {
        match self {
            Clause::Small(s) => s.iter(),
            Clause::Big(b) => b.iter(),
        }
    }

    /// retain literal
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: std::ops::FnMut(&Literal) -> bool,
    {
        match self {
            Clause::Small(s) => s.retain(|x| f(x)),
            Clause::Big(b) => {
                b.retain(|x| f(x));
                if b.len() <= SMALL_CAP {
                    *self = Clause::Small(b.as_slice().try_into().unwrap())
                }
            }
        }
    }

    /// sort by compare
    pub fn sort_by<F>(&mut self, compare: F)
    where
        F: FnMut(&Literal, &Literal) -> Ordering,
    {
        match self {
            Clause::Small(s) => s.sort_by(compare),
            Clause::Big(b) => b.sort_by(compare),
        }
    }

    /// append literal from other
    pub fn append(&mut self, other: &mut Clause) {
        // cap limit check and upgrade
        match self {
            Clause::Small(s) => {
                if s.len() + other.len() > SMALL_CAP {
                    let v = s.to_vec();
                    *self = Clause::Big(v);
                }
            }
            _ => {}
        }
        match (self, other) {
            (Clause::Small(s), Clause::Small(o)) => {
                for item in o.iter() {
                    s.push(*item);
                }
                o.clear();
            }
            (Clause::Small(s), Clause::Big(o)) => {
                for item in o.iter() {
                    s.push(*item);
                }
                o.clear();
            }
            (Clause::Big(s), Clause::Small(o)) => {
                for item in o.iter() {
                    s.push(*item);
                }
                o.clear();
            }
            (Clause::Big(s), Clause::Big(o)) => s.append(o),
        }
    }

    /// add literal to clause
    pub fn push(&mut self, value: Literal) {
        match self {
            Clause::Small(s) => {
                if s.len() >= SMALL_CAP {
                    let mut v = s.to_vec();
                    v.push(value);
                    *self = Clause::Big(s.to_vec())
                } else {
                    s.push(value)
                }
            }
            Clause::Big(v) => v.push(value),
        }
    }
}

impl Index<usize> for Clause {
    type Output = Literal;

    fn index(&self, index: usize) -> &Self::Output {
        match self {
            Clause::Small(s) => s.index(index),
            Clause::Big(b) => b.index(index),
        }
    }
}

/// Conjunctive normal form for SAT input
pub type Cnf = Vec<Clause>;

/// SAT variable
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct Variable(u32);

/// condition of satisfaction
#[derive(PartialEq)]
pub enum Satisfaction {
    /// require true for SAT
    True,
    /// require false for SAT
    False,
    /// don't care for SAT
    DontCare,
}

impl Variable {
    /// build valiable from index
    pub fn from_index(index: u32) -> Self {
        Self(index)
    }

    /// returns variable index value
    pub fn index(&self) -> u32 {
        self.0
    }

    /// create true Literal for this variable
    pub fn t(&self) -> Literal {
        Literal::new(true, *self)
    }

    /// create false literal for this variable
    pub fn f(&self) -> Literal {
        Literal::new(false, *self)
    }

    /// get Satisfaction for this variable
    pub fn satisfaction(&self, answer: &[Literal]) -> Satisfaction {
        for item in answer {
            if item.references(self) {
                return match item.value() {
                    true => Satisfaction::True,
                    false => Satisfaction::False,
                };
            }
        }
        Satisfaction::DontCare
    }

    /// shortcut for `self.satisfaction(answer) == Satisfaction::True`
    pub fn is_true(&self, answer: &[Literal]) -> bool {
        self.satisfaction(answer) == Satisfaction::True
    }

    /// shortcut for `self.satisfaction(answer) == Satisfaction::False`
    pub fn is_false(&self, answer: &[Literal]) -> bool {
        self.satisfaction(answer) == Satisfaction::False
    }

    /// shortcut for `self.satisfaction(answer) == Satisfaction::DontCare`
    pub fn is_dontcare(&self, answer: &[Literal]) -> bool {
        self.satisfaction(answer) == Satisfaction::DontCare
    }
}

#[derive(Debug)]
/// SAT variable factory
pub struct Variables {
    index: u32,
}

impl Variables {
    /// create factory
    pub fn new() -> Variables {
        Variables { index: 1 }
    }

    /// create SAT valiable
    pub fn create(&mut self) -> Variable {
        let result = Variable(self.index);
        self.index += 1;
        result
    }

    /// count of variables
    pub fn count(&self) -> u32 {
        self.index - 1
    }
}

impl Default for Variables {
    fn default() -> Self {
        Variables { index: 1 }
    }
}

/// SAT literal
#[derive(PartialEq, Clone, Copy, Debug)]
pub struct Literal(i32);

impl Literal {
    fn new(positive: bool, index: Variable) -> Self {
        let value = match positive {
            true => index.0 as i32,
            false => -(index.0 as i32),
        };
        Literal(value)
    }

    /// get variable from this literal
    pub fn var(&self) -> Variable {
        self.to_parts().1
    }

    /// value on this literal
    pub fn value(&self) -> bool {
        self.to_parts().0
    }

    fn references(&self, valiable: &Variable) -> bool {
        self.0.abs() == valiable.0 as i32
    }

    /// convert to value and valiable
    pub fn to_parts(&self) -> (bool, Variable) {
        (self.0 >= 0, Variable(self.0.abs() as u32))
    }

    fn not(&self) -> Self {
        Literal(-self.0)
    }
}

impl From<(bool, Variable)> for Literal {
    fn from(lit: (bool, Variable)) -> Self {
        Literal::new(lit.0, lit.1)
    }
}

#[derive(Clone, Copy, Debug)]
/// solver action
pub enum SolverAction {
    /// apply dpll_erase_one_literal
    EraseOneLiteral(Literal),
    /// apply dpll_erase_pure_literal
    ErasePureLiteral(Literal),
    /// apply dpll_split
    Split(Literal),
}

impl SolverAction {
    /// gets literal from this SolverAction
    pub fn to_literal(&self) -> Literal {
        match self {
            SolverAction::EraseOneLiteral(l)
            | SolverAction::ErasePureLiteral(l)
            | SolverAction::Split(l) => *l,
        }
    }

    /// verbose solver steps to literal list
    pub fn simplify_answer(answer: &[SolverAction]) -> Vec<Literal> {
        answer.iter().map(|i| i.to_literal()).collect()
    }
}

/// One literal rule : find erase-able literal from input
#[allow(clippy::ptr_arg)]
pub fn dpll_find_one_literal(input: &Cnf) -> Option<Literal> {
    if let Some(node) = input.iter().find(|f| f.len() == 1) {
        Some(node[0])
    } else {
        None
    }
}

/// One literal rule : erase literal from input
pub fn dpll_erase_one_literal(input: &mut Cnf, item: Literal) {
    let remove_item = item.not();
    input.retain(|n| !n.contains(&item));
    for node in input.iter_mut() {
        node.retain(|f| *f != remove_item);
    }
}

/// Pure literal rule : find erase-able literal from input
#[allow(clippy::ptr_arg)]
pub fn dpll_find_pure_literal(input: &Cnf) -> Option<Literal> {
    let mut positive_set = HashSet::new();
    let mut negative_set = HashSet::new();

    for node in input.iter() {
        for item in node.iter() {
            let (positive, index) = item.to_parts();
            if positive {
                positive_set.insert(index);
            } else {
                negative_set.insert(index);
            }
        }
    }
    for in_positive in positive_set.iter() {
        if !negative_set.contains(in_positive) {
            return Some((true, *in_positive).into());
        }
    }
    for in_negative in negative_set.iter() {
        if !positive_set.contains(in_negative) {
            return Some((false, *in_negative).into());
        }
    }
    None
}

/// Pure literal rule : erase literal from input
pub fn dpll_erase_pure_literal(input: &mut Cnf, item: Literal) {
    input.retain(|n| !n.contains(&item));
}

/// Split rule : Split input on point variable
pub fn dpll_split(input: &mut Cnf, point: &Variable) -> (Cnf, i32, i32) {
    let mut result1 = Vec::new();
    let mut result2 = Vec::new();
    let mut count1 = 0;
    let mut count2 = 0;
    while let Some(node) = input.pop() {
        if node.contains(&point.t()) {
            let mut items = node.clone();
            items.retain(|f| !f.references(point));
            count2 += items.len();
            result2.push(items);
        } else if node.contains(&point.f()) {
            let mut items = node.clone();
            items.retain(|f| !f.references(point));
            count1 += items.len();
            result1.push(items);
        } else {
            count1 += node.len();
            count2 += node.len();
            result1.push(node.clone());
            result2.push(node.clone());
        }
    }
    // write back to input
    while let Some(node) = result1.pop() {
        input.push(node);
    }
    (result2, count1 as i32, count2 as i32)
}

/// check input is SAT
#[allow(clippy::ptr_arg)]
pub fn is_sat(input: &Cnf) -> bool {
    input.is_empty()
}

/// check input is UNSAT
#[allow(clippy::ptr_arg)]
pub fn is_unsat(input: &Cnf) -> bool {
    for node in input.iter() {
        if node.is_empty() {
            return true;
        }
    }
    false
}

/// implement heuristics for solver process
pub trait SolverHeuristics {
    /// get variable for split
    fn find_split_point(&self, cnf: &Cnf, satisfy_vars: u32) -> Variable;
}

/// find variable used often in input
#[allow(clippy::ptr_arg)]
pub fn find_max_used_variable(input: &Cnf, count_vars: usize) -> Option<Variable> {
    let mut counts = HashMap::with_capacity(count_vars);
    let mut max_count = 0;
    let mut max_key = None;
    for node in input.iter() {
        for item in node.iter() {
            let (_, v) = item.to_parts();
            let count = counts.entry(v).or_insert(0);
            *count += 1;
            if *count > max_count {
                max_count = *count;
                max_key = Some(v);
            }
        }
    }
    max_key
}

/// repeating apply "erase one literal"
fn solve_partial(input: &mut Cnf) -> Vec<SolverAction> {
    let mut result = Vec::new();

    while let Some(lit) = dpll_find_one_literal(input) {
        // add lit to answer
        result.push(SolverAction::EraseOneLiteral(lit));
        // apply one literal rule
        dpll_erase_one_literal(input, lit);
    }
    result
}

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
/// use pico_sat::{Variables, solve_one, heuristics::SplitOnMaxVars,Clause };
/// let mut vars = Variables::new();
/// let o = vars.create();
/// let p = vars.create();
/// let q = vars.create();
/// let r = vars.create();
/// let mut f = vec![
///    Clause::from_vec(vec![ p.t(), q.t(), r.f() ]), //    ( P ||  Q || !R )
///    Clause::from_vec(vec![ p.f(), r.f() ]),        // && (!P || !R )
///    Clause::from_vec(vec![ r.t() ])                // && ( R)
/// ];
/// match solve_one(&mut f, 4, &SplitOnMaxVars { count_vars: vars.count() as usize } ) {
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

pub fn solve_one_verbose<S: SolverHeuristics>(
    input: &mut Cnf,
    satisfy_vars: u32,
    heuristics: &S,
) -> Option<Vec<SolverAction>> {
    let mut stack = Vec::new();

    stack.push((Vec::new(), input.clone()));
    while let Some((mut prefix, mut formula)) = stack.pop() {
        let mut partial_result = solve_partial(&mut formula);
        prefix.append(&mut partial_result);

        if is_unsat(&formula) {
            continue;
        }
        if is_sat(&formula) {
            return Some(prefix);
        }
        let split_point = heuristics.find_split_point(&formula, satisfy_vars);
        let (false_part, t_count, f_count) = dpll_split(&mut formula, &split_point);

        if t_count <= f_count {
            let mut false_prefix = prefix.clone();
            false_prefix.push(SolverAction::Split(split_point.f()));
            stack.push((false_prefix, false_part));

            let mut true_prefix = prefix.clone();
            true_prefix.push(SolverAction::Split(split_point.t()));
            stack.push((true_prefix, formula));
        } else {
            let mut true_prefix = prefix.clone();
            true_prefix.push(SolverAction::Split(split_point.t()));
            stack.push((true_prefix, formula));

            let mut false_prefix = prefix.clone();
            false_prefix.push(SolverAction::Split(split_point.f()));
            stack.push((false_prefix, false_part));
        }
    }
    None
}

/// solve input and results simple answer
pub fn solve_one<S: SolverHeuristics>(
    input: &mut Cnf,
    satisfy_vars: u32,
    heuristics: &S,
) -> Option<Vec<Literal>> {
    let result = solve_one_verbose(input, satisfy_vars, heuristics);
    result.map(|r| SolverAction::simplify_answer(&r))
}

// all SAT valiables contains in actions
fn satisfied_all(actions: &[SolverAction], satisfy_vars: u32) -> bool {
    for var_num in 1..=satisfy_vars {
        if !actions
            .iter()
            .any(|a| a.to_literal().var().index() == var_num)
        {
            return false;
        }
    }
    true
}

fn continue_solve<S: SolverHeuristics>(
    prefix: Vec<SolverAction>,
    input: &mut Cnf,
    satisfy_vars: u32,
    heuristics: &S,
) -> Vec<Vec<SolverAction>> {
    let mut result = Vec::new();
    let mut stack = Vec::new();
    stack.push((prefix, input.clone()));
    while let Some((prefix, mut formula)) = stack.pop() {
        let partial_result = solve_partial(&mut formula);
        let prefix = [prefix, partial_result].concat();
        if is_unsat(&formula) {
            continue;
        }
        if is_sat(&formula) {
            result.push(prefix);
            continue;
        }
        let split_point = heuristics.find_split_point(&formula, satisfy_vars);
        let (mut false_part, _, _) = dpll_split(&mut formula, &split_point);

        let mut true_prefix = prefix.clone();
        true_prefix.push(SolverAction::Split(split_point.t()));

        if satisfied_all(&true_prefix, satisfy_vars) {
            if let Some(mut one_result) = solve_one_verbose(&mut formula, satisfy_vars, heuristics)
            {
                true_prefix.append(&mut one_result);
                result.push(true_prefix);
            } else {
                if let Some(mut one_result) =
                    solve_one_verbose(&mut false_part, satisfy_vars, heuristics)
                {
                    let mut false_prefix = prefix.clone();
                    false_prefix.push(SolverAction::Split(split_point.f()));
                    false_prefix.append(&mut one_result);
                    result.push(false_prefix);
                }
            }
        } else {
            stack.push((true_prefix, formula));

            let mut false_prefix = prefix.clone();
            false_prefix.push(SolverAction::Split(split_point.f()));
            stack.push((false_prefix, false_part));
        }
    }
    result
}

/// solve input and results all result
pub fn solve_all_verbose<S: SolverHeuristics>(
    input: &mut Cnf,
    satisfy_vars: u32,
    heuristics: &S,
) -> Vec<Vec<SolverAction>> {
    continue_solve(vec![], input, satisfy_vars, heuristics)
}

/// SAT solve and returns all result
pub fn solve_all<S: SolverHeuristics>(
    input: &mut Cnf,
    satisfy_vars: u32,
    heuristics: &S,
) -> Vec<Vec<Literal>> {
    let verbose_result = continue_solve(vec![], input, satisfy_vars, heuristics);
    verbose_result
        .iter()
        .map(|r| SolverAction::simplify_answer(r))
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::{
        heuristics::SplitOnMaxVars,
        solver::{
            dpll_erase_one_literal, dpll_erase_pure_literal, dpll_find_one_literal,
            dpll_find_pure_literal, dpll_split, solve_all, solve_one, Clause, Variables,
        },
    };

    #[test]
    fn test_find_pure_literal_and_erase() {
        let mut vars = Variables::new();
        let var1 = vars.create();
        let var2 = vars.create();
        let mut f = vec![
            Clause::from_vec(vec![var1.t(), var2.f()]),
            Clause::from_vec(vec![var1.f()]),
        ];
        assert_eq!(dpll_find_pure_literal(&f), Some(var2.f()));
        dpll_erase_pure_literal(&mut f, var2.f());
        assert_eq!(f.len(), 1);
        assert_eq!(f[0].len(), 1);
        assert_eq!(f[0][0], var1.f());
    }

    #[test]
    fn test_find_one_literal_and_erase() {
        let mut vars = Variables::new();
        let var1 = vars.create();
        let var2 = vars.create();
        let mut f = vec![
            Clause::from_vec(vec![var1.t(), var2.f()]),
            Clause::from_vec(vec![var1.f()]),
        ];
        assert_eq!(dpll_find_one_literal(&f), Some(var1.f()));
        dpll_erase_one_literal(&mut f, var1.f());
        assert_eq!(f.len(), 1);
        assert_eq!(f[0].len(), 1);
        assert_eq!(f[0][0], var2.f());
    }

    #[test]
    fn test_split_and_result() {
        let mut vars = Variables::new();
        let p = vars.create();
        let q = vars.create();
        let r = vars.create();
        let mut f = vec![
            Clause::from_vec(vec![p.t(), q.f()]),
            Clause::from_vec(vec![p.f(), r.t()]),
            Clause::from_vec(vec![q.t()]),
        ];
        eprintln!("input formula: {:?}", f);
        eprintln!("spilt P: {:?}", p);
        let (_fpart, _tcnt, _fcnt) = dpll_split(&mut f, &p);
        eprintln!("when P: {:?}", f);
        assert_eq!(f.len(), 2);
        assert_eq!(f[0].len(), 1);
        assert_eq!(f[0][0], r.t());
        assert_eq!(f[1].len(), 1);
        assert_eq!(f[1][0], q.t());
    }

    #[test]
    fn test_find_one_unsat() {
        // this sample come from https://ja.wikipedia.org/wiki/DPLL%E3%82%A2%E3%83%AB%E3%82%B4%E3%83%AA%E3%82%BA%E3%83%A0#%E5%85%85%E8%B6%B3%E4%B8%8D%E8%83%BD%E3%81%AA%E8%AB%96%E7%90%86%E5%BC%8F
        let mut vars = Variables::new();
        let p = vars.create();
        let q = vars.create();
        let r = vars.create();
        let mut f = vec![
            Clause::from_vec(vec![p.t(), q.t(), r.f()]),
            Clause::from_vec(vec![q.f(), p.t()]),
            Clause::from_vec(vec![p.f()]),
            Clause::from_vec(vec![r.t(), q.t()]),
        ];
        let one_lit = dpll_find_one_literal(&f);
        assert_eq!(one_lit, Some(p.f()));
        dpll_erase_one_literal(&mut f, one_lit.unwrap());
        assert_eq!(f.len(), 3);
        assert_eq!(f[0].len(), 2);
        assert_eq!(f[0][0], q.t());
        assert_eq!(f[0][1], r.f());
        assert_eq!(f[1].len(), 1);
        assert_eq!(f[1][0], q.f());
        assert_eq!(f[2].len(), 2);
        assert_eq!(f[2][0], r.t());
        assert_eq!(f[2][1], q.t());

        let one_lit = dpll_find_one_literal(&f);
        assert_eq!(one_lit, Some(q.f()));
        dpll_erase_one_literal(&mut f, one_lit.unwrap());
        assert_eq!(f.len(), 2);
        assert_eq!(f[0].len(), 1);
        assert_eq!(f[0][0], r.f());
        assert_eq!(f[1].len(), 1);
        assert_eq!(f[1][0], r.t());

        let one_lit = dpll_find_one_literal(&f);
        assert_eq!(one_lit, Some(r.f()));
        dpll_erase_one_literal(&mut f, one_lit.unwrap());
        assert_eq!(f.len(), 1);
        assert_eq!(f[0].len(), 0); // f[0].len==0  -> UNSAT
    }

    #[test]
    fn test_pure_split_one_sat() {
        let mut vars = Variables::new();
        let s = vars.create();
        let t = vars.create();
        let p = vars.create();
        let u = vars.create();

        let mut f = vec![
            Clause::from_vec(vec![s.t(), t.t()]),
            Clause::from_vec(vec![s.f(), t.f()]),
            Clause::from_vec(vec![p.t(), u.t()]),
            Clause::from_vec(vec![p.f(), u.t()]),
        ];
        let pure_lit = dpll_find_pure_literal(&f);
        assert_eq!(pure_lit, Some(u.t()));
        dpll_erase_pure_literal(&mut f, pure_lit.unwrap());
        assert_eq!(f.len(), 2);
        assert_eq!(f[0].len(), 2);
        assert_eq!(f[0][0], s.t());
        assert_eq!(f[0][1], t.t());
        assert_eq!(f[1].len(), 2);
        assert_eq!(f[1][0], s.f());
        assert_eq!(f[1][1], t.f());
        let pure_lit = dpll_find_pure_literal(&f);
        assert_eq!(pure_lit, None);
        let one_lit = dpll_find_one_literal(&f);
        assert_eq!(one_lit, None);
        let (mut f_part, c1, c2) = dpll_split(&mut f, &s);
        let mut t_part = f;
        assert_eq!(c1, 1);
        assert_eq!(c2, 1);
        assert_eq!(t_part.len(), 1);
        assert_eq!(t_part[0].len(), 1);
        assert_eq!(t_part[0][0], t.f());
        assert_eq!(f_part.len(), 1);
        assert_eq!(f_part[0].len(), 1);
        assert_eq!(f_part[0][0], t.t());

        let one_lit = dpll_find_one_literal(&t_part);
        assert_eq!(one_lit, Some(t.f()));
        dpll_erase_one_literal(&mut t_part, one_lit.unwrap());
        assert_eq!(t_part.len(), 0); // SAT

        let one_lit = dpll_find_one_literal(&f_part);
        assert_eq!(one_lit, Some(t.t()));
        dpll_erase_one_literal(&mut f_part, one_lit.unwrap());
        assert_eq!(f_part.len(), 0); // SAT
    }

    #[test]
    fn test_solve_one() {
        let mut vars = Variables::new();
        let p = vars.create();
        let q = vars.create();
        let r = vars.create();
        let mut f = vec![
            Clause::from_vec(vec![p.t(), q.t(), r.f()]),
            Clause::from_vec(vec![p.f(), r.f()]),
            Clause::from_vec(vec![r.t()]),
        ];
        match solve_one(
            &mut f,
            3,
            &SplitOnMaxVars {
                count_vars: vars.count() as usize,
            },
        ) {
            Some(answer) => {
                // Some means SAT
                assert_eq!(answer.len(), 3);
                assert_eq!(answer[0], r.t(), "first R");
                assert_eq!(answer[1], p.f(), "second ~P");
                assert_eq!(answer[2], q.t(), "third Q");
            }
            None => {
                panic!("UNSAT")
            }
        }
    }

    #[test]
    fn test_solve_all_split_max_vars() {
        let mut vars = Variables::new();
        let s = vars.create();
        let t = vars.create();

        let mut f = vec![
            Clause::from_vec(vec![s.t(), t.t()]),
            Clause::from_vec(vec![s.f(), t.f()]),
        ];
        let results = solve_all(
            &mut f,
            2,
            &SplitOnMaxVars {
                count_vars: vars.count() as usize,
            },
        );
        assert!(!results.is_empty());
        assert_eq!(results.len(), 2);
        assert_eq!(results[0].len(), 2);
        assert_eq!(results[0][0], s.f());
        assert_eq!(results[0][1], t.t());
        assert_eq!(results[1].len(), 2);
        assert_eq!(results[1][0], s.t());
        assert_eq!(results[1][1], t.f());
    }
}
