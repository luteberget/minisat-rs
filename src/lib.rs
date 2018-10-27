//! [MiniSat](http://minisat.se) Rust interface. 
//! Solves a boolean satisfiability problem given in conjunctive normal form.
//!
//! ```rust
//! extern crate minisat;
//! use std::iter::once;
//! fn main() {
//!     let mut sat = minisat::Sat::new();
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
//! Graph coloring example:
//! ```rust
//! extern crate minisat;
//! use std::iter::once;
//! fn main() {
//!     let mut coloring = minisat::Sat::new();
//!
//!     #[derive(PartialEq, Eq, Debug, PartialOrd, Ord)]
//!     enum Color { Red, Green, Blue };
//!
//!     let n_nodes = 5;
//!     let edges = vec![(0,1),(1,2),(2,3),(3,4),(3,1),(4,0),(4,2)];
//!     let colors = (0..n_nodes)
//!         .map(|_| coloring.symbolic(vec![Color::Red, Color::Green, Color::Blue]))
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



#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

extern crate itertools;
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

impl Lit {
    fn into_var(self) -> (minisat_Var, bool) {
        ( unsafe { minisat_var(self.1) },
          unsafe { minisat_sign(self.1) } > 0 )
    }
}

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

//use std::marker::PhantomData;

pub struct Symbolic<T>(Vec<(Value, T)>);

impl<T:Eq> Symbolic<T> {
    pub fn new(solver :&mut Sat, mut xs: Vec<T>) -> Self {
        if xs.len() == 0 {
            panic!("Symbolic value cannot be initialized from empty list.");
        } else if xs.len() == 1 {
            Symbolic(vec![(true.into(), xs.remove(0))])
        } else if xs.len() == 1 {
            let l = solver.new_lit();
            let a = xs.remove(0);
            let b = xs.remove(0);
            Symbolic(vec![(l, a), (!l, b)])
        } else {
            let lits = xs.iter().map(|_| solver.new_lit()).collect::<Vec<_>>();
            solver.exactly_one(lits.iter().cloned());
            Symbolic(lits.into_iter().zip(xs.into_iter()).collect())
        }
    }


    pub fn domain(&self) -> impl Iterator<Item = &T> {
        self.0.iter().map(|(_,t)| t)
    }

    pub fn has_value(&self, a :&T) -> Value {
        for (v,x) in &self.0 {
            if x == a { 
                return *v;
            }
        }
        false.into()
    }
}

pub struct Unary(Vec<Value>);

impl Unary {
    //pub fn new(solver :&mut Sat, size :usize) -> Self {

    //}

    pub fn zero() -> Self {
        Unary(Vec::new())
    }

    pub fn number(n :usize) -> Self {
        Unary(vec![true.into(); n])
    }

    pub fn succ(&self) -> Self {
        let mut v = self.0.clone();
        v.insert(0, true.into());
        Unary(v)
    }

    pub fn pred(&self) -> Self {
        if self.0.len() > 0 {
            let mut v = self.0.clone();
            v.remove(0);
            Unary(v)
        } else {
            Self::zero()
        }
    }

    pub fn reverse(&self) -> Self {
        let mut v = self.0.clone();
        v.reverse();
        for x in &mut v { *x = !*x; }
        Unary(v)
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
    pub fn add_clause<I: IntoIterator<Item = Value>>(&mut self, lits :I) {
        unsafe { minisat_addClause_begin(self.ptr) };
        for lit in lits {
            match lit {
                Value::Bool(true) => return,
                Value::Bool(false) => {}, 
                Value::Lit(Lit(ptr, l)) => {
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
    pub fn solve_under_assumptions<'a, I:IntoIterator<Item = Value>>(&'a mut self, lits :I) -> Result<Model<'a>, ()> {
        unsafe { minisat_solve_begin(self.ptr); }
        for lit in lits {
            match lit {
                Value::Bool(false) => return Err(()),
                Value::Bool(true) => {},
                Value::Lit(Lit(ptr, l)) => {
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

    pub fn and_literal<I:IntoIterator<Item = Value>>(&mut self, xs :I) -> Value {
        use std::collections::HashSet;
        let mut lits = Vec::new();
        let mut posneg = [HashSet::new(), HashSet::new()];
        for v in xs {
            match v {
                Value::Bool(false) => return false.into(),
                Value::Bool(true) => {},
                Value::Lit(l) => {
                    let (var,s) = l.into_var();
                    if posneg[s as usize].contains(&var) { 
                        return false.into(); 
                    }
                    if posneg[(s as usize)+1 % 2].insert(var) {
                        lits.push(l);
                    }
                }
            }
        }

        let y = self.new_lit();
        for x in &mut lits {
            self.add_clause(once(!y).chain(once(Value::Lit(*x))));
        }
        let mut lits = lits.into_iter().map(|x| ! Value::Lit(x)).collect::<Vec<_>>();
        lits.push(y);
        self.add_clause(lits.into_iter());
        y
    }

    pub fn or_literal<I:IntoIterator<Item = Value>>(&mut self, xs :I) -> Value {
        !(self.and_literal(xs.into_iter().map(|x| !x)))
    }

    pub fn exactly_one<I:IntoIterator<Item = Value>>(&mut self, xs :I) {
        let xs = xs.into_iter().collect::<Vec<_>>();
        self.add_clause(xs.iter().cloned());
        self.at_most_one(xs.iter().cloned());
    }

    pub fn at_most_one(&mut self, xs: impl Iterator<Item = Value>) {
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
            self.at_most_one(once(x).chain(xs.iter().take(k).cloned()));
            self.at_most_one(once(!x).chain(xs.iter().skip(k).cloned()));
        }
    }

    pub fn implies(&mut self, a :Value, b :Value) -> Value {
        let x = vec![!a, b];
        self.or_literal(x.into_iter())
    }

    pub fn xor_literal(&mut self, xs :impl Iterator<Item = Value>) -> Value {
        unimplemented!()
    }

    pub fn symbolic<T:Eq>(&mut self, xs :Vec<T>) -> Symbolic<T> {
        Symbolic::new(self, xs)
    }

    pub fn equal<T:ModelEq>(&mut self, a :&T, b :&T) {
        ModelEq::assert_equal_or(self, Vec::new(), a, b);
    }

    pub fn not_equal<T:ModelEq>(&mut self, a :&T, b :&T) {
        ModelEq::assert_not_equal_or(self, Vec::new(), a, b);
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

pub trait ModelValue<'a> {
    type T;
    fn value(&'a self, m: &'a Model) -> Self::T;
}

pub trait ModelEq {
    fn assert_equal_or(solver: &mut Sat, prefix: Vec<Value>, a :&Self, b :&Self);
    fn assert_not_equal_or(solver: &mut Sat, prefix: Vec<Value>, a :&Self, b :&Self);
    fn is_equal(solver :&mut Sat, a :&Self, b:&Self) -> Value {
        let q = solver.new_lit();
        Self::assert_equal_or(solver, vec![!q], a, b);
        Self::assert_not_equal_or(solver, vec![q], a, b);
        q
    }
}

use std::iter::{once,empty};
impl ModelEq for Value {
    fn assert_equal_or(solver :&mut Sat, prefix: Vec<Value>, a: &Value, b :&Value)  {
        solver.add_clause(prefix.iter().cloned().chain(once(!*a)).chain(once(*b)));
        solver.add_clause(prefix.iter().cloned().chain(once(*a)) .chain(once(!*b)));
    }

    fn assert_not_equal_or(solver :&mut Sat, prefix: Vec<Value>, a: &Value, b :&Value)  {
        Self::assert_equal_or(solver, prefix, a, &!*b);
    }

    fn is_equal(solver :&mut Sat, a :&Value, b :&Value) -> Value {
        //solver.xor_literal(a, &!*b)
        solver.xor_literal(once(*a).chain(once(!*b)))
    }
}

impl<V:Ord> ModelEq for Symbolic<V> {
    fn assert_equal_or(solver :&mut Sat, prefix: Vec<Value>, 
                       a: &Symbolic<V>, b :&Symbolic<V>)  {
        for (p,q,x) in stitch(a,b) {
            match (p,q,x) {
                (Some(p), None, _) => solver.add_clause(
                    once(!p).chain(prefix.iter().cloned())),
                (None, Some(q), _) => solver.add_clause(
                    once(!q).chain(prefix.iter().cloned())),
                (Some(p), Some(q), _) => solver.add_clause(
                    once(!p).chain(once(q)).chain(prefix.iter().cloned())),
                _ => unreachable!()
            }
        }
    }

    fn assert_not_equal_or(solver :&mut Sat, prefix: Vec<Value>, 
                           a: &Symbolic<V>, b :&Symbolic<V>)  {
        for (p,q,x) in stitch(a,b) {
            match (p,q,x) {
                (Some(p), Some(q), _) => solver.add_clause(
                    once(!p).chain(once(!q)).chain(prefix.iter().cloned())),
                _ => {},
            }
        }
    }
}

fn stitch<'a, V:Ord>(a :&'a Symbolic<V>, b:&'a Symbolic<V>) -> impl Iterator<Item = (Option<Value>, Option<Value>, &'a V)> {
    use itertools::Itertools;
    let mut v : Vec<(Option<Value>, Option<Value>, &'a V)> = 
        a.0.iter().map(|(v,x)| (Some(*v), None,    x)).chain(
        b.0.iter().map(|(v,x)| (None,     Some(*v),x))).collect();
    v.sort_by(|(_,_,x),(_,_,y)| x.cmp(y));
    v.into_iter().coalesce(|(a,b,x),(c,d,y)| 
                           if x == y { 
                               Ok((a.or(c), b.or(d), x)) 
                           } else { 
                               Err(((a,b,x),(c,d,y))) 
                           })
}

impl<'a> ModelValue<'a> for Value {
    type T = bool;

    fn value(&self, m: &Model) -> bool {
        match self {
            Value::Bool(b) => *b,
            Value::Lit(Lit(s,l)) => {
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

impl<'a,V :'a> ModelValue<'a> for Symbolic<V> {
    type T = &'a V;

    fn value(&'a self, m :&'a Model) -> Self::T {
        for (v,x) in &self.0 {
            if m.value(v) {
                return x;
            }
        }
        unreachable!()
    }
}

impl<'a> ModelValue<'a> for Unary {
    type T = usize;
    fn value(&self, m :&Model) -> usize {
        self.0.iter().enumerate()
            .find(|(_i,x)| !m.value(*x))
            .map(|(v,_)| v)
            .unwrap_or(self.0.len())
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

    #[test]
    fn sat() {
        let mut sat = Sat::new();
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
        let mut sat = Sat::new();
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
        let mut sat = Sat::new();
        sat.add_clause(empty());
        assert_eq!(sat.solve().is_err(), true);
    }

    #[test]
    fn sat2() {
        let mut sat = Sat::new();
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
    fn graph_color() {
        let mut coloring = Sat::new();

        #[derive(PartialEq, Eq, Debug, PartialOrd, Ord)]
        enum Color { Red, Green, Blue };

        let n_nodes = 5;
        let edges = vec![(0,1),(1,2),(2,3),(3,4),(3,1),(4,0),(4,2)];
        let colors = (0..n_nodes)
            .map(|_| coloring.symbolic(vec![Color::Red, Color::Green, Color::Blue]))
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
}
