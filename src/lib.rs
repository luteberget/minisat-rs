//! [MiniSat](http://minisat.se) Rust interface.
//! Solves a boolean satisfiability problem given in conjunctive normal form.
//!
//! ```rust
//! extern crate minisat;
//! use std::iter::once;
//! fn main() {
//!     let mut sat = minisat::Solver::new();
//!     let a = sat.new_lit();
//!     let b = sat.new_lit();
//!
//!     // Solves ((a OR not b) AND b)
//!     sat.add_clause(vec![a, !b]);
//!     sat.add_clause(vec![b]);
//!
//!     match sat.solve() {
//!         Ok(m) => {
//!             assert_eq!(m.lit_value(&a), true);
//!             assert_eq!(m.lit_value(&b), true);
//!         },
//!         Err(()) => panic!("UNSAT"),
//!     }
//! }
//! ```
//!
//! This crate compiles the MiniSat sources directly and binds through
//! the [minisat-c-bindings](https://github.com/niklasso/minisat-c-bindings) interface.
//! The low-level C bindings are available through the [`sys`](sys/index.html) module.

#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

/// The FFI interface to MiniSat (imported from
/// [minisat-c-bindings](https://github.com/niklasso/minisat-c-bindings)).
pub mod sys {
    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
}

use sys::*;

/// Solver object representing an instance of the boolean satisfiability problem.
pub struct Solver {
    ptr: *mut minisat_solver_t,
}

/// A literal is a boolean variable or its negation.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Lit(minisat_Lit);

/// A MiniSAT variable.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Var(minisat_Var);

impl Lit {
    pub fn var(self) -> (Var, bool) {
        (
            Var(unsafe { minisat_var(self.0) }),
            unsafe { minisat_sign(self.0) } > 0,
        )
    }

    pub fn from_var_sign(var: Var, neg: bool) -> Lit {
        let mut l = unsafe { minisat_mkLit(var.0) };
        if neg {
            l = unsafe { minisat_negate(l) };
        }
        Lit(l)
    }
}

impl std::ops::Not for Lit {
    type Output = Lit;
    fn not(self) -> Lit {
        Lit(unsafe { minisat_negate(self.0) })
    }
}

impl Solver {
    /// Create a new SAT solver instance.
    pub fn new() -> Self {
        let ptr = unsafe { minisat_new() };

        // "normal solver"??? (cfr. haskell minisat-0.1.2 newSolver)
        unsafe { minisat_eliminate(ptr, 1 as i32) };

        Solver { ptr }
    }

    /// Create a fresh boolean variable.
    pub fn new_lit(&mut self) -> Lit {
        Lit(unsafe { minisat_newLit(self.ptr) })
    }

    /// Add a clause to the SAT instance (assert the disjunction of the given literals).
    pub fn add_clause<I: IntoIterator<Item = Lit>>(&mut self, lits: I) {
        unsafe { minisat_addClause_begin(self.ptr) };
        for lit in lits {
            unsafe {
                minisat_addClause_addLit(self.ptr, lit.0);
            }
        }
        unsafe { minisat_addClause_commit(self.ptr) };
    }

    /// Solve the SAT instance, returning a solution (`Model`) if the
    /// instance is satisfiable, or returning an `Err(())` if the problem
    /// is unsatisfiable.
    pub fn solve<'a>(&'a mut self) -> Result<Model<'a>, ()> {
        self.solve_under_assumptions(std::iter::empty())
    }

    /// Solve the SAT instance under given assumptions, returning a solution (`Model`) if the
    /// instance is satisfiable, or returning an `Err(())` if the problem
    /// is unsatisfiable.
    ///
    /// The conjunction of the given literals are temporarily added to the SAT instance,
    /// so the result is the same as if each literal was added as a clause, but
    /// the solver object can be re-used afterwards and does then not contain these assumptions.
    /// This interface can be used to build SAT instances incrementally.
    pub fn solve_under_assumptions<'a, I: IntoIterator<Item = Lit>>(
        &'a mut self,
        lits: I,
    ) -> Result<Model<'a>, ()> {
        unsafe {
            minisat_solve_begin(self.ptr);
        }
        for lit in lits {
            unsafe {
                minisat_solve_addLit(self.ptr, lit.0);
            }
        }
        let sat = unsafe { minisat_solve_commit(self.ptr) } > 0;
        if sat {
            Ok(Model(self))
        } else {
            Err(())
        }
    }

    /// Return the number of assignments to variables made in the solver instance.
    pub fn num_assigns(&self) -> isize {
        unsafe { minisat_num_assigns(self.ptr) as isize }
    }

    /// Return the number of clauses in the solver instance.
    pub fn num_clauses(&self) -> isize {
        unsafe { minisat_num_clauses(self.ptr) as isize }
    }

    /// Return the number of learnt clauses in the solver instance.
    pub fn num_learnts(&self) -> isize {
        unsafe { minisat_num_learnts(self.ptr) as isize }
    }

    /// Return the number of variables in the solver instance.
    pub fn num_vars(&self) -> isize {
        unsafe { minisat_num_vars(self.ptr) as isize }
    }

    /// Return the number of free variables  in the solver instance.
    pub fn num_free_vars(&self) -> isize {
        unsafe { minisat_num_freeVars(self.ptr) as isize }
    }

    /// Name and version of SAT solver.
    pub fn solver_name(&self) -> &'static str {
        if cfg!(feature = "glucose") {
            "Glucose v4.1"
        // https://www.labri.fr/perso/lsimon/glucose/
        } else {
            "MiniSAT v2.1.0"
            // http://minisat.se/
        }
    }
}

impl Drop for Solver {
    fn drop(&mut self) {
        unsafe {
            minisat_delete(self.ptr);
        }
    }
}

use std::fmt;
impl fmt::Debug for Solver {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "SAT instance ({}) {{ variables: {}, clauses: {} }}",
            self.solver_name(),
            self.num_vars(),
            self.num_clauses()
        )
    }
}

/// A model of a satisfiable instance, i.e. assignments to variables in the problem satisfying
/// the asserted constraints.
pub struct Model<'a>(&'a mut Solver);

impl<'a> Model<'a> {
    pub fn lit_value(&self, l: &Lit) -> bool {
        let lbool = unsafe { minisat_modelValue_Lit(self.0.ptr, l.0) };
        if unsafe { minisat_get_l_True() } == lbool {
            true
        } else if unsafe { minisat_get_l_False() } == lbool {
            false
        } else {
            unreachable!()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::iter::once;

    #[test]
    fn sat() {
        let mut sat = Solver::new();
        let a = sat.new_lit();
        let b = sat.new_lit();
        // sat.add_clause(&[a,b]);
        sat.add_clause(once(a).chain(once(b)));
        match sat.solve() {
            Ok(m) => {
                println!("a: {:?}", m.lit_value(&a));
                println!("b: {:?}", m.lit_value(&b));
            }
            Err(_) => panic!(),
        };
    }

    #[test]
    fn unsat() {
        let mut sat = Solver::new();
        let a = sat.new_lit();
        let b = sat.new_lit();
        // sat.add_clause(&[a]);
        // sat.add_clause(&[b]);
        // sat.add_clause(&[!b]);
        sat.add_clause(once(a));
        sat.add_clause(once(b));
        sat.add_clause(once(!b));
        let sol = sat.solve();
        assert_eq!(sol.is_err(), true);
    }

    #[test]
    fn unsat2() {
        use std::iter::empty;
        let mut sat = Solver::new();
        sat.add_clause(empty());
        assert_eq!(sat.solve().is_err(), true);
    }

    #[test]
    fn sat2() {
        let mut sat = Solver::new();
        let a = sat.new_lit();
        assert_eq!(sat.solve().is_err(), false);
        assert_eq!(sat.solve_under_assumptions(vec![!a]).is_err(), false);
        sat.add_clause(once(a));
        assert_eq!(sat.solve().is_err(), false);
        assert_eq!(sat.solve_under_assumptions(vec![!a]).is_err(), true);
        sat.add_clause(vec![!a]);
        assert_eq!(sat.solve().is_err(), true);
    }
}
