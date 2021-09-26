use std::collections::{HashMap, HashSet};

/// async solvers
#[cfg(feature = "async")]
pub mod async_solver;

/// Conjunctive normal form for SAT input
pub type Cnf = Vec<Vec<Literal>>;

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
    for node in input.iter() {
        if node.len() == 1 {
            return Some(node[0]);
        }
    }
    None
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
            let mut items = Vec::new();
            for item in node.iter() {
                if !item.references(point) {
                    items.push(*item);
                    count1 += 1;
                }
            }
            result2.push(items);
        } else if node.contains(&point.f()) {
            let mut items = Vec::new();
            for item in node.iter() {
                if !item.references(point) {
                    items.push(*item);
                    count2 += 1;
                }
            }
            result1.push(items);
        } else {
            count1 += node.len() as i32;
            count2 += node.len() as i32;
            result1.push(node.clone());
            result2.push(node.clone());
        }
    }
    // write back to input
    while let Some(node) = result1.pop() {
        input.push(node);
    }
    (result2, count1, count2)
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

/// find variable used often in input
#[allow(clippy::ptr_arg)]
pub fn find_max_used_variable(input: &Cnf) -> Option<Variable> {
    let mut counts = HashMap::new();
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
fn solve_partial(input: &mut Cnf) -> Option<Vec<SolverAction>> {
    let mut result = Vec::new();

    while let Some(lit) = dpll_find_one_literal(input) {
        // add lit to answer
        result.push(SolverAction::ErasePureLiteral(lit));
        // apply one literal rule
        dpll_erase_one_literal(input, lit);
    }
    Some(result)
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

pub fn solve_one_verbose(input: &mut Cnf) -> Option<Vec<SolverAction>> {
    let partial_result = solve_partial(input);
    if is_unsat(input) {
        return None;
    }
    if let Some(mut result) = partial_result {
        if is_sat(input) {
            return Some(result);
        }
        let split_point = find_max_used_variable(input).unwrap();
        let (mut false_part, t_count, f_count) = dpll_split(input, &split_point);
        if t_count <= f_count {
            if let Some(child_result) = solve_one_verbose(input) {
                result.push(SolverAction::Split(split_point.t()));
                return Some([result, child_result].concat());
            }
            if let Some(child_result) = solve_one_verbose(&mut false_part) {
                result.push(SolverAction::Split(split_point.f()));
                return Some([result, child_result].concat());
            }
        } else {
            if let Some(child_result) = solve_one_verbose(&mut false_part) {
                result.push(SolverAction::Split(split_point.f()));
                return Some([result, child_result].concat());
            }
            if let Some(child_result) = solve_one_verbose(input) {
                result.push(SolverAction::Split(split_point.t()));
                return Some([result, child_result].concat());
            }
        }
    }
    None
}

/// solve input and results simple answer
pub fn solve_one(input: &mut Cnf) -> Option<Vec<Literal>> {
    let result = solve_one_verbose(input);
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

fn continue_solve(
    prefix: Vec<SolverAction>,
    input: &mut Cnf,
    satisfy_vars: u32,
) -> Vec<Vec<SolverAction>> {
    let partial_result = solve_partial(input);
    let prefix = [prefix, partial_result.unwrap()].concat();
    if is_unsat(input) {
        return vec![];
    }
    if is_sat(input) {
        return vec![prefix];
    }
    let split_point = find_max_used_variable(input).unwrap();

    let (mut false_part, _, _) = dpll_split(input, &split_point);

    let mut true_prefix = prefix.clone();
    true_prefix.push(SolverAction::Split(split_point.t()));
    if satisfied_all(&true_prefix, satisfy_vars) {
        let true_result = solve_one_verbose(input);
        if let Some(mut sat_ans) = true_result {
            true_prefix.append(&mut sat_ans);
            return vec![true_prefix];
        } else {
            let mut false_prefix = prefix;
            false_prefix.push(SolverAction::Split(split_point.f()));
            let false_result = solve_one_verbose(&mut false_part);
            if let Some(mut sat_ans) = false_result {
                false_prefix.append(&mut sat_ans);
                return vec![false_prefix];
            }
            return vec![];
        }
    } else {
        let true_result = continue_solve(true_prefix, input, satisfy_vars);

        let mut false_prefix = prefix;
        false_prefix.push(SolverAction::Split(split_point.f()));
        let false_result = continue_solve(false_prefix, &mut false_part, satisfy_vars);

        [true_result, false_result].concat()
    }
}

/// solve input and results all result
pub fn solve_all_verbose(input: &mut Cnf, satisfy_vars: u32) -> Vec<Vec<SolverAction>> {
    continue_solve(vec![], input, satisfy_vars)
}

/// SAT solve and returns all result
pub fn solve_all(input: &mut Cnf, satisfy_vars: u32) -> Vec<Vec<Literal>> {
    let verbose_result = continue_solve(vec![], input, satisfy_vars);
    verbose_result
        .iter()
        .map(|r| SolverAction::simplify_answer(r))
        .collect()
}

#[cfg(test)]
mod tests {
    use crate::solver::{
        dpll_erase_one_literal, dpll_erase_pure_literal, dpll_find_one_literal,
        dpll_find_pure_literal, dpll_split, solve_all, solve_one, Variables,
    };

    #[test]
    fn test_find_pure_literal_and_erase() {
        let mut vars = Variables::new();
        let var1 = vars.create();
        let var2 = vars.create();
        let mut f = vec![vec![var1.t(), var2.f()], vec![var1.f()]];
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
        let mut f = vec![vec![var1.t(), var2.f()], vec![var1.f()]];
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
        let mut f = vec![vec![p.t(), q.f()], vec![p.f(), r.t()], vec![q.t()]];
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
            vec![p.t(), q.t(), r.f()],
            vec![q.f(), p.t()],
            vec![p.f()],
            vec![r.t(), q.t()],
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
            vec![s.t(), t.t()],
            vec![s.f(), t.f()],
            vec![p.t(), u.t()],
            vec![p.f(), u.t()],
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
        let mut f = vec![vec![p.t(), q.t(), r.f()], vec![p.f(), r.f()], vec![r.t()]];
        match solve_one(&mut f) {
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
    fn test_solve_all() {
        let mut vars = Variables::new();
        let s = vars.create();
        let t = vars.create();

        let mut f = vec![vec![s.t(), t.t()], vec![s.f(), t.f()]];
        let results = solve_all(&mut f, 2);
        assert!(!results.is_empty());
        assert_eq!(results.len(), 2);
        assert_eq!(results[0].len(), 2);
        assert_eq!(results[0][0], s.t());
        assert_eq!(results[0][1], t.f());
        assert_eq!(results[1].len(), 2);
        assert_eq!(results[1][0], s.f());
        assert_eq!(results[1][1], t.t());
    }
}
