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
//!             assert_eq!(m.value(&a), true);
//!             assert_eq!(m.value(&b), true);
//!         },
//!         Err(()) => panic!("UNSAT"),
//!     }
//! }
//! ```
//!
//! This crate compiles the MiniSat sources directly and binds through
//! the [minisat-c-bindings](https://github.com/niklasso/minisat-c-bindings) interface.
//! The low-level C bindings are available through the [`sys`](sys/index.html) module. 
//! 
//! High-level features ported from [satplus](https://github.com/koengit/satplus):
//!  * Traits for representing non-boolean values in the SAT problem:
//!     * Value trait (`ModelValue`)
//!     * Equality trait (`ModelEq`)
//!     * Ordering trait (`ModelOrd`)
//!  * Symbolic values (`Symbolic<V>`)
//!  * Non-negative integers with unary encoding (`Unary`)
//!  * Non-negative integers with binary encoding (`Binary`)
//!
//! Graph coloring example:
//! ```rust
//! extern crate minisat;
//! use std::iter::once;
//! use minisat::symbolic::*;
//! fn main() {
//!     let mut coloring = minisat::Solver::new();
//!
//!     #[derive(PartialEq, Eq, Debug, PartialOrd, Ord)]
//!     enum Color { Red, Green, Blue };
//!
//!     let n_nodes = 5;
//!     let edges = vec![(0,1),(1,2),(2,3),(3,4),(3,1),(4,0),(4,2)];
//!     let colors = (0..n_nodes)
//!         .map(|_| Symbolic::new(&mut coloring, vec![Color::Red, Color::Green, Color::Blue]))
//!         .collect::<Vec<_>>();
//!     for (n1,n2) in edges {
//!         coloring.not_equal(&colors[n1],&colors[n2]);
//!     }
//!     match coloring.solve() {
//!         Ok(model) => {
//!             for i in 0..n_nodes {
//!                 println!("Node {}: {:?}", i, model.value(&colors[i]));
//!             }
//!         },
//!         Err(()) => {
//!             println!("No solution.");
//!         }
//!     }
//! }
//! ```
//!
//! Factorization example:
//! ```rust
//! extern crate minisat;
//! use minisat::{*, binary::*};
//!
//! fn main() {
//!     let mut sat = Solver::new();
//!     let a = Binary::new(&mut sat, 1000);
//!     let b = Binary::new(&mut sat, 1000);
//!     let c = a.mul(&mut sat, &b);
//!     sat.equal(&c, &Binary::constant(36863));
//!
//!     match sat.solve() {
//!         Ok(model) => {
//!             println!("{}*{}=36863", model.value(&a), model.value(&b));
//!         },
//!         Err(()) => {
//!             println!("No solution.");
//!         }
//!     }
//! }
//! ```



#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

//  #![cfg_attr(test, feature(plugin))]
 //#![cfg_attr(test, plugin(quickcheck_macros))]

#[cfg(test)]
#[macro_use]
extern crate quickcheck;


extern crate itertools;

/// The FFI interface to MiniSat (imported from 
/// [minisat-c-bindings](https://github.com/niklasso/minisat-c-bindings)).
pub mod sys {
    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
}

use sys::*;

mod model_eq;
mod model_ord;

pub use model_eq::*;
pub use model_ord::*;

/// Unary encoding of non-negative integers (see `Unary`).
pub mod unary;
///
/// Binary encoding of non-negative integers (see `Binary`).
pub mod binary;

/// Symbolic values (see the struct `Symbolic<V>`).
pub mod symbolic;

use std::convert::From;
use std::ops::Not;

/// The SAT problem instance (also called solver instance).
pub struct Solver {
    ptr: *mut minisat_solver_t,
}

/// Boolean value, either a constant (`Bool::Const`) or
/// a literal (`Bool::Lit`).  Create values by creating new 
/// variables (`Solver::new_lit()`) or from a constant boolean (`true.into()`).
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Bool {
  Const(bool),
  Lit(Lit),
}

/// A literal is a boolean variable or its negation.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Lit(*mut minisat_solver_t, minisat_Lit);

impl Lit {
    fn into_var(self) -> (minisat_Var, bool) {
        ( unsafe { minisat_var(self.1) },
          unsafe { minisat_sign(self.1) } > 0 )
    }

    fn from_var_sign(s :*mut minisat_solver_t, var :minisat_Var, neg :bool) -> Lit {
        let mut l = unsafe { minisat_mkLit(var) };
        if neg { l = unsafe { minisat_negate(l) }; }
        Lit(s, l)
    }
}

impl From<bool> for Bool {
    fn from(item :bool) -> Self {
        Bool::Const(item)
    }
}

impl Not for Bool {
    type Output = Bool;
    fn not(self) -> Bool {
        match self {
            Bool::Const(b) => Bool::Const(!b),
            Bool::Lit(l) => Bool::Lit(!l),
        }
    }
}

impl Not for Lit {
    type Output = Lit;
    fn not(self) -> Lit {
        Lit(self.0, unsafe { minisat_negate(self.1) })
    }
}




impl Solver {
    /// Create a new SAT instance.
    pub fn new() -> Self {
        let ptr = unsafe { minisat_new() };

        // "normal solver"??? (cfr. haskell minisat-0.1.2 newSolver)
        unsafe { minisat_eliminate(ptr, 1 as i32) }; 

        Solver { ptr }
    }

    /// Create a new variable.
    pub fn new_lit(&mut self) -> Bool {
        Bool::Lit(Lit(self.ptr, unsafe { minisat_newLit(self.ptr) }))
    }

    /// Add a clause to the SAT instance (assert the disjunction of the given literals).
    pub fn add_clause<I: IntoIterator<Item = Bool>>(&mut self, lits :I) {
        unsafe { minisat_addClause_begin(self.ptr) };
        for lit in lits {
            match lit {
                Bool::Const(true) => return,
                Bool::Const(false) => {}, 
                Bool::Lit(Lit(ptr, l)) => {
                    assert_eq!(ptr, self.ptr);
                    unsafe { minisat_addClause_addLit(ptr, l); }
                }
            }
        }
        unsafe { minisat_addClause_commit(self.ptr) };
    }

    /// Solve the SAT instance, returning a solution (`Model`) if the 
    /// instance is satisfiable, or returning an `Err(())` if the problem
    /// is unsatisfiable.
    pub fn solve<'a>(&'a mut self) -> Result<Model<'a>, ()> {
        self.solve_under_assumptions(empty())
    }

    /// Solve the SAT instance under given assumptions, returning a solution (`Model`) if the 
    /// instance is satisfiable, or returning an `Err(())` if the problem
    /// is unsatisfiable.
    ///
    /// The conjunction of the given literals are temporarily added to the SAT instance,
    /// so the result is the same as if each literal was added as a clause, but 
    /// the solver object can be re-used afterwards and does then not contain these assumptions.
    /// This interface can be used to build SAT instances incrementally.
    pub fn solve_under_assumptions<'a, I:IntoIterator<Item = Bool>>(&'a mut self, lits :I) -> Result<Model<'a>, ()> {
        unsafe { minisat_solve_begin(self.ptr); }
        for lit in lits {
            match lit {
                Bool::Const(false) => return Err(()),
                Bool::Const(true) => {},
                Bool::Lit(Lit(ptr, l)) => {
                    assert_eq!(ptr, self.ptr);
                    unsafe { minisat_solve_addLit(ptr, l); }
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

    pub fn and_literal<I:IntoIterator<Item = Bool>>(&mut self, xs :I) -> Bool {
        use std::collections::HashSet;
        let mut lits = Vec::new();
        let mut posneg = [HashSet::new(), HashSet::new()];
        for v in xs {
            match v {
                Bool::Const(false) => return false.into(),
                Bool::Const(true) => {},
                Bool::Lit(l) => {
                    let (var,s) = l.into_var();
                    if posneg[s as usize].contains(&var) { 
                        return false.into(); 
                    }
                    if posneg[(s as usize+1) % 2].insert(var) {
                        lits.push(l);
                    }
                }
            }
        }

        if lits.len() == 0 {
            return true.into(); 
        }
        if lits.len() == 1 {
            return Bool::Lit(lits[0]);
        }

        let y = self.new_lit();
        for x in &mut lits {
            self.add_clause(once(!y).chain(once(Bool::Lit(*x))));
        }
        let mut lits = lits.into_iter().map(|x| ! Bool::Lit(x)).collect::<Vec<_>>();
        lits.push(y);
        self.add_clause(lits.into_iter());
        y
    }

    pub fn or_literal<I:IntoIterator<Item = Bool>>(&mut self, xs :I) -> Bool {
        !(self.and_literal(xs.into_iter().map(|x| !x)))
    }

    pub fn assert_exactly_one<I:IntoIterator<Item = Bool>>(&mut self, xs :I) {
        let xs = xs.into_iter().collect::<Vec<_>>();
        self.add_clause(xs.iter().cloned());
        self.assert_at_most_one(xs.iter().cloned());
    }

    pub fn assert_at_most_one(&mut self, xs: impl Iterator<Item = Bool>) {
        let xs = xs.collect::<Vec<_>>();
        if xs.len() <= 5 {
            for i in 0..xs.len() {
                for j in (i+1)..xs.len() {
                    self.add_clause(once(!xs[i]).chain(once(!xs[j])));
                }
            }
        } else {
            let x = self.new_lit();
            let k = xs.len()/2;
            self.assert_at_most_one(once(x).chain(xs.iter().take(k).cloned()));
            self.assert_at_most_one(once(!x).chain(xs.iter().skip(k).cloned()));
        }
    }

    pub fn implies(&mut self, a :Bool, b :Bool) -> Bool {
        self.or_literal(once(!a).chain(once(b)))
    }

    pub fn equiv(&mut self, a :Bool, b :Bool) -> Bool {
        self.xor_literal(once(!a).chain(once(b)))
    }

    pub fn assert_parity<I:IntoIterator<Item = Bool>>(&mut self, xs :I, x :bool) {
        self.assert_parity_or(empty(), xs, x);
    }

    pub fn assert_parity_or<I:IntoIterator<Item = Bool>,
                            J:IntoIterator<Item = Bool>>
                                (&mut self, prefix :I, xs :J, c :bool) {
        let mut xs = xs.into_iter().collect::<Vec<_>>();
        let prefix = prefix.into_iter().collect::<Vec<_>>();
        if xs.len() == 0 {
            if c {
                self.add_clause(prefix);
            } // else nothing
        } else if xs.len() <= 5 {
            let x = xs.pop().unwrap();
            self.assert_parity_or(prefix.iter().cloned().chain(once(!x)), 
                                  xs.iter().cloned(), !c);
            self.assert_parity_or(prefix.iter().cloned().chain(once(x)), 
                                  xs.iter().cloned(), c);
        } else {
            let x = self.new_lit();
            let k = xs.len()/2;
            self.assert_parity_or(prefix.iter().cloned(), 
                      xs.iter().cloned().take(k).chain(once(x)), c);
            self.assert_parity_or(prefix.iter().cloned(), 
                      xs.iter().cloned().skip(k).chain(once(if c { !x } else { x })), c);
        }
    }

    /// Returns a `Bool` which represents the odd parity bit for the 
    /// given sequence of `Bool` values.
    pub fn xor_literal<I:IntoIterator<Item = Bool>>(&mut self, xs :I) -> Bool {
        use std::collections::HashSet;
        let mut posneg = [HashSet::new(), HashSet::new()];
        let mut const_parity = false;
        for x in xs {
            match x {
                Bool::Const(b) => { const_parity ^= b},
                Bool::Lit(l) => {
                    assert_eq!(l.0, self.ptr);
                    let (var,s) = l.into_var();
                    let s = s as usize;
                    if !posneg[s].insert(var) { 
                        posneg[s].remove(&var);
                    }

                    if posneg[s].contains(&var) && posneg[(s+1) %2].contains(&var) {
                        const_parity = !const_parity;
                        posneg[0].remove(&var);
                        posneg[1].remove(&var);
                    }
                }
            }
        }

        let out = posneg[0].iter().map(|x| Bool::Lit(Lit::from_var_sign(self.ptr,*x,false)))
           .chain(posneg[1].iter().map(|x| Bool::Lit(Lit::from_var_sign(self.ptr,*x,true)))).collect::<Vec<_>>();
        if out.len() == 0 {
            const_parity.into()
        } else if out.len() == 1 {
            if const_parity { !out[0] } else { out[0] } 
        } else {
            let y = self.new_lit();
            self.assert_parity(once(y).chain(out.into_iter()), const_parity);
            y
        }
    }


    pub fn equal<T:ModelEq>(&mut self, a :&T, b :&T) {
        ModelEq::assert_equal_or(self, Vec::new(), a, b);
    }

    pub fn not_equal<T:ModelEq>(&mut self, a :&T, b :&T) {
        ModelEq::assert_not_equal_or(self, Vec::new(), a, b);
    }

    pub fn greater_than<T:ModelOrd>(&mut self, a :&T, b :&T) {
        self.greater_than_or(empty(), a, b);
    }

    pub fn greater_than_equal<T:ModelOrd>(&mut self, a :&T, b :&T) {
        self.greater_than_equal_or(empty(), a, b);
    }

    pub fn less_than<T:ModelOrd>(&mut self, a :&T, b :&T) {
        self.less_than_or(empty(), a, b);
    }

    pub fn less_than_equal<T:ModelOrd>(&mut self, a :&T, b :&T) {
        self.less_than_equal_or(empty(), a, b);
    }

    pub fn greater_than_or<T:ModelOrd, I:IntoIterator<Item = Bool>>(&mut self, prefix :I, a :&T, b :&T) {
        self.less_than_or(prefix,b,a);
    }

    pub fn greater_than_equal_or<T:ModelOrd, I:IntoIterator<Item = Bool>>(&mut self, prefix :I, a :&T, b :&T) {
        self.less_than_equal_or(prefix,b,a);
    }

    pub fn less_than_or<T:ModelOrd, I:IntoIterator<Item = Bool>>(&mut self, prefix :I, a :&T, b :&T) {
        T::assert_less_or(self, prefix.into_iter().collect(), false, a, b);
    }

    pub fn less_than_equal_or<T:ModelOrd, I:IntoIterator<Item = Bool>>(&mut self, prefix :I, a :&T, b :&T) {
        T::assert_less_or(self, prefix.into_iter().collect(), true, a, b);
    }


    pub fn num_assigns(&self) -> isize {
        unsafe { minisat_num_assigns(self.ptr)  as isize }
    }

    pub fn num_clauses(&self) -> isize {
        unsafe { minisat_num_clauses(self.ptr)  as isize }
    }

    pub fn num_learnts(&self) -> isize {
        unsafe { minisat_num_learnts(self.ptr)  as isize }
    }

    pub fn num_vars(&self) -> isize {
        unsafe { minisat_num_vars(self.ptr)  as isize }
    }

    pub fn num_free_vars(&self) -> isize {
        unsafe { minisat_num_freeVars(self.ptr)  as isize }
    }
}

impl Drop for Solver {
    fn drop(&mut self) {
        unsafe { minisat_delete(self.ptr); }
    }
}

use std::fmt;
impl fmt::Debug for Solver {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "SAT instance (MiniSat v2.1.0) {{ variables: {}, clauses: {} }}", self.num_vars(), self.num_clauses())
    }
}


/// A model, in the logic sense, contains and assignments to each variable
/// in the SAT instance which satisfies the clauses added to the problem.
pub struct Model<'a>(&'a mut Solver);

pub trait ModelValue<'a> {
    type T;
    fn value(&'a self, m: &'a Model) -> Self::T;
}

use std::iter::{once,empty};




impl<'a> ModelValue<'a> for Bool {
    type T = bool;

    fn value(&self, m: &Model) -> bool {
        match self {
            Bool::Const(b) => *b,
            Bool::Lit(Lit(s,l)) => {
                assert_eq!(m.0.ptr, *s);
                let lbool = unsafe { minisat_modelValue_Lit(*s,*l) };
                if unsafe { minisat_get_l_True() } == lbool {
                    true
                } else if unsafe { minisat_get_l_False() } == lbool {
                    false
                } else {
                    unreachable!()
                }
            }
        }
    }
}

impl<'a> Model<'a> {
    pub fn value<V, T :ModelValue<'a, T=V>>(&'a self, v :&'a T) -> V {
        v.value(self)
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use super::unary::*;
    use super::binary::*;



    #[test]
    fn sat() {
        let mut sat = Solver::new();
        let a = sat.new_lit();
        let b = sat.new_lit();
        //sat.add_clause(&[a,b]);
        sat.add_clause(once(a).chain(once(b)));
        match sat.solve() {
            Ok(m) => {
                println!("a: {:?}", m.value(&a));
                println!("b: {:?}", m.value(&b));
            }
            Err(_) => panic!(),
        };
    }

    #[test]
    fn unsat() {
        let mut sat = Solver::new();
        let a = sat.new_lit();
        let b = sat.new_lit();
        //sat.add_clause(&[a]);
        //sat.add_clause(&[b]);
        //sat.add_clause(&[!b]);
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

    #[test]
    fn xor() {
        let mut sat = Solver::new();
        let a = sat.new_lit();
        let b = sat.new_lit();
        let c = sat.new_lit();
        let d = sat.new_lit();
        let x = sat.xor_literal(vec![a,!b,c,d]);
        sat.add_clause(vec![x]);
        loop {
            let (av,bv,cv,dv);
            match sat.solve() {
                Ok(model) => {
                    av = model.value(&a);
                    bv = model.value(&b);
                    cv = model.value(&c);
                    dv = model.value(&d);
                    println!("MODEL: a={}\tb={}\tc={}\td={}", av,bv,cv,dv);
                    assert_eq!(true, av^(!bv)^cv^dv);
                },
                _ => {break;},
            };

            sat.add_clause(vec![av,bv,cv,dv].into_iter().zip(vec![a,b,c,d])
                           .map(|(v,x)| if v { !x } else { x } ));
        }
    }

    #[test]
    fn unary_1() {
        let mut sat = Solver::new();
        let a = Unary::new(&mut sat, 100);
        let b = Unary::new(&mut sat, 200);
        sat.greater_than(&a, &Unary::constant(50));
        sat.less_than(&a.mul_const(2), &b);

        match sat.solve() {
            Ok(model) => {
                let av = model.value(&a);
                println!("A value: {}", av);
                let bv = model.value(&b);
                println!("B value: {}", bv);
                assert!(av > 50);
                assert!(bv > av);
            },
            _ => panic!(),
        }
    }

    #[test]
    fn graph_color() {
        use symbolic::*;
        let mut coloring = Solver::new();

        #[derive(PartialEq, Eq, Debug, PartialOrd, Ord)]
        enum Color { Red, Green, Blue };

        let n_nodes = 5;
        let edges = vec![(0,1),(1,2),(2,3),(3,4),(3,1),(4,0),(4,2)];
        let colors = (0..n_nodes)
            .map(|_| Symbolic::new(&mut coloring, vec![Color::Red, Color::Green, Color::Blue]))
            .collect::<Vec<_>>();
        for (n1,n2) in edges {
            coloring.not_equal(&colors[n1],&colors[n2]);
        }
        match coloring.solve() {
            Ok(model) => {
                for i in 0..n_nodes {
                    println!("Node {}: {:?}", i, model.value(&colors[i]));
                }
            },
            Err(()) => {
                println!("No solution.");
            }
        }
    }

    #[test]
    fn take_more_than_len() {
        let mut iter = vec![1,2,3].into_iter().take(9999);
        assert_eq!(iter.next(), Some(1));
        assert_eq!(iter.next(), Some(2));
        assert_eq!(iter.next(), Some(3));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn factorization_unary() {
        let mut sat = Solver::new();
        let a = Unary::new(&mut sat, 20);
        let b = Unary::new(&mut sat, 20);
        let c = a.mul(&mut sat, &b);
        sat.equal(&c, &Unary::constant(209));

        println!("Solving {:?}", sat);
        match sat.solve() {
            Ok(model) => {
                println!("{}*{}=209", model.value(&a), model.value(&b));
                assert_eq!(model.value(&a)*model.value(&b), 209);
            },
            Err(()) => {
                println!("No solution.");
            }
        }
    }

    #[test]
    fn factorization_binary() {
        let mut sat = Solver::new();
        let a = Binary::new(&mut sat, 1000); 
        let b = Binary::new(&mut sat, 1000);
        let c = a.mul(&mut sat, &b);
        sat.equal(&c, &Binary::constant(36863));

        println!("Solving {:?}", sat);
        match sat.solve() {
            Ok(model) => {
                println!("{}*{}=36863", model.value(&a), model.value(&b));
            },
            Err(()) => {
                println!("No solution.");
            }
        }
    }

    #[test]
    fn binary_ord() {
        let mut sat = Solver::new();
        let a = Binary::new(&mut sat, 2_usize.pow(16));
        let b = Binary::new(&mut sat, 123123123123);
        let c = Binary::new(&mut sat, 1231231231239);


        sat.less_than(&Binary::constant(30), &a);
        sat.less_than(&a, &Binary::constant(90));
        sat.less_than(&Binary::constant(15), &b);
        sat.less_than(&b, &Binary::constant(17));
        let d = a.add(&mut sat, &b);
        let e = a.add(&mut sat, &Binary::constant(2));
        //sat.less_than(&a, &b);
//        sat.less_than(&Binary::constant(100001), &b);
//        sat.greater_than(&Binary::constant(100003), &b);
//        let d = a.add(&mut sat, &Binary::constant(100));
//        sat.equal(&d, &b);
        //sat.greater_than(&c, &b);
        //sat.less_than_equal(&c, &Binary::constant(100100));

        println!("Solving {:?}", sat);
        match sat.solve() {
            Ok(m) => {
                println!("a={}, b={}, c={}, d={}, e={}", m.value(&a), m.value(&b), m.value(&c), m.value(&d), m.value(&e));
                //assert_eq!(m.value(&b), 100002);
            },
            Err(()) => {
                panic!()
            },
        }

    }

    quickcheck! {
        fn const_binary_eq(xs :Vec<usize>) -> bool {
            let mut sat = Solver::new();
            let xs = xs.into_iter().map(|x| {
                println!("CONST BINARY EQ {}", x);
                let b = Binary::new(&mut sat, x);
                sat.equal(&b, &Binary::constant(x));
                (x,b)
            }).collect::<Vec<_>>();

            match sat.solve() {
                Ok(m) => {
                    for (x,b) in xs {
                        assert_eq!(x, m.value(&b));
                    }
                },
                _ => panic!(),
            };
            true
        }
    }

    quickcheck! {
        fn xor_odd_constant(lits :Vec<bool>) -> bool {
            // The xor literal function returns the odd parity bit
            // which is a constant when the input is a list of constants
            let mut sat = Solver::new();
            let f = sat.xor_literal(lits.iter().map(|_| false.into())) == false.into();
            let t = sat.xor_literal(lits.iter().map(|_| true.into())) == (lits.len() % 2 == 1).into();
            t && f
        }
    }

    quickcheck!  {
        fn xor_literal_lits(lits :Vec<bool>) -> bool {
            let mut sat = Solver::new();
            if lits.len() == 0 { return true; }
            let lits = lits.iter().map(|_| sat.new_lit()).collect::<Vec<_>>();
            let xor = sat.xor_literal(lits.iter().cloned());
            sat.add_clause(vec![xor]); // assert odd parity of list of literals

            match sat.solve() {
                Ok(m) => {
                    let model_parity = lits.iter().map(|x| {
                        if m.value(x) { 1usize } else {0usize }
                    }).sum::<usize>() % 2;
                    assert_eq!(model_parity, 1);
                },
                Err(()) => panic!(),
            };
            true
        }
    }

    quickcheck! {
        fn xor_literal(lits :Vec<bool>, consts :Vec<bool>) -> bool {
            let mut sat = Solver::new();
            let lits = lits.iter().map(|_| sat.new_lit()).collect::<Vec<_>>();
            let expr = consts.iter().map(|x| (*x).into()).chain(lits.into_iter()).collect::<Vec<_>>();
            let xor = sat.xor_literal(expr.iter().cloned());

            match sat.solve() {
                Ok(m) => {
                    let model_parity = expr.iter().map(|x| {
                        println!(" {:?} -> {:?}", x, m.value(x));
                        if m.value(x) { 1usize } else { 0usize }
                    })
                        .sum::<usize>() % 2 == 1;
                    assert_eq!(model_parity, m.value(&xor));
                }
                Err(()) => panic!(),
            };
            true
        }
    }

    quickcheck! {
        fn parity(xs :Vec<bool>) -> bool {
            let mut sat = Solver::new();
            let parity = xs.iter().map(|x| if *x { 1usize } else { 0usize }).sum::<usize>() % 2 == 1;
            let lits = xs.iter().map(|x| {
                let lit = sat.new_lit();
                sat.equal(&lit, &(*x).into());
                lit
            }).collect::<Vec<_>>();
            sat.assert_parity(lits, parity);

            match sat.solve() {
                Err(()) => panic!(),
                _ => {},
            };
            true
        }
    }

    quickcheck! {
        fn const_bool_equal(xs :Vec<bool>) -> bool {
            let mut sat = Solver::new();
            let xs = xs.into_iter().map(|x| {
                let y = sat.new_lit();
                sat.equal(&y,&x.into());
                (x,y)
            }).collect::<Vec<_>>();

            match sat.solve() {
                Ok(m) => {
                    for (x,y) in xs {
                        assert_eq!(x, m.value(&y));
                    }
                },
                _ => panic!(),
            };
            true
        }
    }

    quickcheck! {
        fn const_bool_addclause(xs :Vec<bool>) -> bool {
            let mut sat = Solver::new();
            let xs = xs.into_iter().map(|x| {
                let y = sat.new_lit();
                sat.add_clause(vec![y, (!x).into()]); // x -> y == y, !x
                sat.add_clause(vec![x.into(), !y]); // y -> x == x, !y
                (x,y)
            }).collect::<Vec<_>>();

            match sat.solve() {
                Ok(m) => {
                    for (x,y) in xs {
                        assert_eq!(x, m.value(&y));
                    }
                },
                _ => panic!(),
            };
            true
        }
    }
}
