//! SAT solver using [MiniSat](http://minisat.se).
//! Solves a boolean satisfiability problem given in conjunctive normal form.

#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

pub mod sys {
    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
}

use sys::*;

use std::convert::From;
use std::ops::Not;

/// The SAT problem instance (also called solver instance).
pub struct Sat {
    ptr: *mut minisat_solver_t,
}

/// Boolean value, either a constant (`Value::Bool`) or
/// a literal (`Value::Lit`).  Create values by creating new 
/// variables (`Sat::new_lit()`) or from a constant boolean (`true.into()`).
#[derive(Debug, Copy, Clone)]
pub enum Value {
  Bool(bool),
  Lit(Lit),
}

/// A literal is a boolean variable or its negation.
#[derive(Debug, Copy, Clone)]
pub struct Lit(*mut minisat_solver_t, minisat_Lit);

impl From<bool> for Value {
    fn from(item :bool) -> Self {
        Value::Bool(item)
    }
}

impl Not for Value {
    type Output = Value;
    fn not(self) -> Value {
        match self {
            Value::Bool(b) => Value::Bool(!b),
            Value::Lit(l) => Value::Lit(!l),
        }
    }
}

impl Not for Lit {
    type Output = Lit;
    fn not(self) -> Lit {
        Lit(self.0, unsafe { minisat_negate(self.1) })
    }
}

impl Sat {
    /// Create a new SAT instance.
    pub fn new() -> Self {
        let ptr = unsafe { minisat_new() };

        // "normal solver"??? (cfr. haskell minisat-0.1.2 newSolver)
        unsafe { minisat_eliminate(ptr, 1 as i32) }; 

        Sat { ptr }
    }

    /// Create a new variable.
    pub fn new_lit(&mut self) -> Value {
        Value::Lit(Lit(self.ptr, unsafe { minisat_newLit(self.ptr) }))
    }

    /// Add a clause to the SAT instance (assert the disjunction of the given literals).
    pub fn add_clause(&mut self, lits :&[Value]) {
        unsafe { minisat_addClause_begin(self.ptr) };
        for lit in lits {
            match lit {
                Value::Bool(true) => return,
                Value::Bool(false) => {}, 
                Value::Lit(Lit(ptr, l)) => {
                    assert_eq!(*ptr, self.ptr);
                    unsafe { minisat_addClause_addLit(*ptr, *l); }
                }
            }
        }
        unsafe { minisat_addClause_commit(self.ptr) };
    }

    /// Solve the SAT instance, returning a solution (`Model`) if the 
    /// instance is satisfiable, or returning an `Err(())` if the problem
    /// is unsatisfiable.
    pub fn solve<'a>(&'a mut self) -> Result<Model<'a>, ()> {
        self.solve_under_assumptions(&[])
    }

    /// Solve the SAT instance under given assumptions, returning a solution (`Model`) if the 
    /// instance is satisfiable, or returning an `Err(())` if the problem
    /// is unsatisfiable.
    ///
    /// The conjunction of the given literals are temporarily added to the SAT instance,
    /// so the result is the same as if each literal was added as a clause, but 
    /// the solver object can be re-used afterwards and does then not contain these assumptions.
    /// This interface can be used to build SAT instances incrementally.
    pub fn solve_under_assumptions<'a>(&'a mut self, lits :&[Value]) -> Result<Model<'a>, ()> {
        unsafe { minisat_solve_begin(self.ptr); }
        for lit in lits {
            match lit {
                Value::Bool(false) => return Err(()),
                Value::Bool(true) => {},
                Value::Lit(Lit(ptr, l)) => {
                    assert_eq!(*ptr, self.ptr);
                    unsafe { minisat_solve_addLit(*ptr, *l); }
                }
            }
        }
        let sat = unsafe { minisat_solve_commit(self.ptr) } > 0;
        if sat {
            Ok(Model(self))
        } else {
            Err(())
        }
    }
}

impl Drop for Sat {
    fn drop(&mut self) {
        unsafe { minisat_delete(self.ptr); }
    }
}

/// A model, in the logic sense, contains and assignments to each variable
/// in the SAT instance which satisfies the clauses added to the problem.
pub struct Model<'a>(&'a mut Sat);

impl<'a> Model<'a> {
    /// Get the value of a literal. The returned value is either a boolean value,
    /// or the `None` value, which can be given if the problem is satisfied independently 
    /// of this value (however there are no guarantees that `None` will be returned).
    pub fn get(&self, p :&Value) -> Option<bool> {
        match p {
            Value::Bool(b) => Some(*b),
            Value::Lit(Lit(s,l)) => {
                assert_eq!(self.0.ptr, *s);
                let lbool = unsafe { minisat_modelValue_Lit(*s,*l) };
                if unsafe { minisat_get_l_True() } == lbool {
                    Some(true)
                } else if unsafe { minisat_get_l_False() } == lbool {
                    Some(false)
                } else {
                    None
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sat() {
        let mut sat = Sat::new();
        let a = sat.new_lit();
        let b = sat.new_lit();
        sat.add_clause(&[a,b]);
        match sat.solve() {
            Ok(m) => {
                println!("a: {:?}", m.get(&a));
                println!("b: {:?}", m.get(&b));
            }
            Err(_) => panic!(),
        };
    }

    #[test]
    fn unsat() {
        let mut sat = Sat::new();
        let a = sat.new_lit();
        let b = sat.new_lit();
        sat.add_clause(&[a]);
        sat.add_clause(&[b]);
        sat.add_clause(&[!b]);
        let sol = sat.solve();
        assert_eq!(sol.is_err(), true);
    }

    #[test]
    fn unsat2() {
        let mut sat = Sat::new();
        sat.add_clause(&[]);
        assert_eq!(sat.solve().is_err(), true);
    }

    #[test]
    fn sat2() {
        let mut sat = Sat::new();
        let a = sat.new_lit();
        assert_eq!(sat.solve().is_err(), false);
        assert_eq!(sat.solve_under_assumptions(&[!a]).is_err(), false);
        sat.add_clause(&[a]);
        assert_eq!(sat.solve().is_err(), false);
        assert_eq!(sat.solve_under_assumptions(&[!a]).is_err(), true);
        sat.add_clause(&[!a]);
        assert_eq!(sat.solve().is_err(), true);
    }
}
