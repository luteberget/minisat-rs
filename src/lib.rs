#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

use std::convert::From;
use std::ops::Not;

pub struct Sat {
    ptr: *mut minisat_solver_t,
}

#[derive(Debug, Copy, Clone)]
pub enum Lit {
  Lit(*mut minisat_solver_t, minisat_Lit),
  Bool(bool)
}

impl From<bool> for Lit {
    fn from(item :bool) -> Self {
        Lit::Bool(item)
    }
}

impl Not for Lit {
    type Output = Lit;
    fn not(self) -> Lit {
        match self {
            Lit::Bool(b) => Lit::Bool(!b),
            Lit::Lit(s,l) => Lit::Lit(s, unsafe { minisat_negate(l) })
        }
    }
}

impl Sat {
    pub fn new() -> Self {
        let ptr = unsafe { minisat_new() };

        // "normal solver"??? (cfr. haskell minisat-0.1.2 newSolver)
        unsafe { minisat_eliminate(ptr, 1 as i32) }; 

        Sat { ptr }
    }

    pub fn new_lit(&mut self) -> Lit {
        Lit::Lit(self.ptr, unsafe { minisat_newLit(self.ptr) })
    }

    pub fn add_clause(&mut self, lits :&[Lit]) {
        unsafe { minisat_addClause_begin(self.ptr) };
        for lit in lits {
            match lit {
                Lit::Bool(true) => return,
                Lit::Bool(false) => {}, 
                Lit::Lit(ptr, l) => {
                    assert_eq!(*ptr, self.ptr);
                    unsafe { minisat_addClause_addLit(*ptr, *l); }
                }
            }
        }
        unsafe { minisat_addClause_commit(self.ptr) };
    }

    pub fn solve<'a>(&'a mut self) -> Result<Model<'a>, ()> {
        self.solve_under_assumptions(&[])
    }

    pub fn solve_under_assumptions<'a>(&'a mut self, lits :&[Lit]) -> Result<Model<'a>, ()> {
        unsafe { minisat_solve_begin(self.ptr); }
        for lit in lits {
            match lit {
                Lit::Bool(false) => return Err(()),
                Lit::Bool(true) => {},
                Lit::Lit(ptr, l) => {
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

pub struct Model<'a>(&'a mut Sat);

impl<'a> Model<'a> {
    pub fn get(&self, p :&Lit) -> Option<bool> {
        match p {
            Lit::Bool(b) => Some(*b),
            Lit::Lit(s,l) => {
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
