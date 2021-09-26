use std::io::Write;

use crate::solver::Cnf;

/// DIMACS file writer
pub struct DimacsWriter {
    comment_lines: Vec<String>,
}

impl DimacsWriter {
    /// create DimacsWriter instance
    pub fn new(comment_lines: Vec<String>) -> Self {
        Self { comment_lines }
    }

    /// write CNF to DIMACS
    #[allow(clippy::ptr_arg)]
    pub fn write<W: Write>(&self, file: &mut W, cnf: &Cnf) -> Result<(), std::io::Error> {
        for comment in self.comment_lines.iter() {
            writeln!(file, "c {}", comment)?;
        }
        let max_var = cnf
            .iter()
            .map(|n| n.iter().map(|l| l.var().index()).max().unwrap_or_default())
            .max()
            .unwrap_or_default();
        writeln!(file, "p cnf {} {}", max_var, cnf.len())?;
        for node in cnf {
            for lit in node {
                match lit.value() {
                    true => write!(file, "{} ", &lit.var().index())?,
                    false => write!(file, "-{} ", &lit.var().index())?,
                }
            }
            writeln!(file, "0")?;
        }
        Ok(())
    }
}
