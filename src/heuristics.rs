use crate::solver::SolverHeuristics;

/// split on max used variable
pub struct SplitOnMaxVars {
    pub count_vars: usize,
}

impl SolverHeuristics for SplitOnMaxVars {
    fn find_split_point(&self, cnf: &crate::solver::Cnf, _satisfy_vars: u32) -> crate::Variable {
        crate::solver::find_max_used_variable(cnf, self.count_vars).unwrap()
    }
}
