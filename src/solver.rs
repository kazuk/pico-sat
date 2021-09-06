use std::collections::{HashMap, HashSet};

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

    fn to_parts(self) -> (bool, Variable) {
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
            result1.push(items);
        }
        if node.contains(&point.f()) {
            let mut items = Vec::new();
            for item in node.iter() {
                if !item.references(point) {
                    items.push(*item);
                    count2 += 1;
                }
            }
            result2.push(items);
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
fn is_unsat(input: &Cnf) -> bool {
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

/// repeating apply "erase one literal", and "erase pure literal"
fn solve_partial(input: &mut Cnf) -> Option<Vec<Literal>> {
    let mut result = Vec::new();

    // erase one literal / erase pure literal
    while dpll_find_one_literal(input).is_some() || dpll_find_pure_literal(input).is_some() {
        // can I apply "one literal rule" ?
        while let Some(lit) = dpll_find_one_literal(input) {
            // add lit to answer
            result.push(lit);
            // apply one literal rule
            dpll_erase_one_literal(input, lit);
            // is SAT? (SAT check is very fast , then use to shortcat)
            if is_sat(input) {
                return Some(result);
            }
        }
        // On now, "one literal rule" can't apply.
        // can I apply "pure literal rule"?
        if let Some(lit) = dpll_find_pure_literal(input) {
            // add lit to answer
            result.push(lit);
            // apply pure literal rule
            dpll_erase_pure_literal(input, lit);
            // is SAT? (SAT check is very fast , then use to shortcat)
            if is_sat(input) {
                return Some(result);
            }
        }
        // On now, sometime Can "one literal rule" , check on while block.
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

pub fn solve_one(input: &mut Cnf) -> Option<Vec<Literal>> {
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
            if let Some(child_result) = solve_one(input) {
                result.push(split_point.t());
                return Some([result, child_result].concat());
            }
            if let Some(child_result) = solve_one(&mut false_part) {
                result.push(split_point.f());
                return Some([result, child_result].concat());
            }
        } else {
            if let Some(child_result) = solve_one(&mut false_part) {
                result.push(split_point.f());
                return Some([result, child_result].concat());
            }
            if let Some(child_result) = solve_one(input) {
                result.push(split_point.t());
                return Some([result, child_result].concat());
            }
        }
    }
    None
}

fn continue_solve(prefix: Vec<Literal>, input: &mut Cnf) -> Vec<Vec<Literal>> {
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
    true_prefix.push(split_point.t());
    let true_result = continue_solve(true_prefix, input);

    let mut false_prefix = prefix;
    false_prefix.push(split_point.f());
    let false_result = continue_solve(false_prefix, &mut false_part);

    [true_result, false_result].concat()
}

/// SAT solve and returns all result
pub fn solve_all(input: &mut Cnf) -> Vec<Vec<Literal>> {
    continue_solve(vec![], input)
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
        assert_eq!(t_part[0][0], t.t());
        assert_eq!(f_part.len(), 1);
        assert_eq!(f_part[0].len(), 1);
        assert_eq!(f_part[0][0], t.f());

        let one_lit = dpll_find_one_literal(&t_part);
        assert_eq!(one_lit, Some(t.t()));
        dpll_erase_one_literal(&mut t_part, one_lit.unwrap());
        assert_eq!(t_part.len(), 0); // SAT

        let one_lit = dpll_find_one_literal(&f_part);
        assert_eq!(one_lit, Some(t.f()));
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
        let p = vars.create();
        let u = vars.create();

        let mut f = vec![
            vec![s.t(), t.t()],
            vec![s.f(), t.f()],
            vec![p.t(), u.t()],
            vec![p.f(), u.t()],
        ];
        let results = solve_all(&mut f);
        assert!(!results.is_empty());
        assert_eq!(results.len(), 2);
        assert_eq!(results[0].len(), 3);
        assert_eq!(results[0][0], u.t());
        assert_eq!(results[0][1], s.t());
        assert_eq!(results[0][2], t.t());
        assert_eq!(results[1].len(), 3);
        assert_eq!(results[1][0], u.t());
        assert_eq!(results[1][1], s.f());
        assert_eq!(results[1][2], t.f());
    }
}
