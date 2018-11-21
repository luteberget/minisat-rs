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
//!     let mut coloring = minisat::Sat::new();
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
//!
//! fn main() {
//!     let mut sat = minisat::Sat::new();
//!     let a = sat.new_binary(1000);
//!     let b = sat.new_binary(1000);
//!     let c = a.mul(&mut sat, &b);
//!     sat.equal(&c, &minisat::Binary::constant(36863));
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

/// Symbolic values (see the struct `Symbolic<V>`).
pub mod symbolic;

use std::convert::From;
use std::ops::Not;

/// The SAT problem instance (also called solver instance).
pub struct Sat {
    ptr: *mut minisat_solver_t,
}

/// Boolean value, either a constant (`Bool::Const`) or
/// a literal (`Bool::Lit`).  Create values by creating new 
/// variables (`Sat::new_lit()`) or from a constant boolean (`true.into()`).
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


#[derive(Debug,Clone)]
pub struct Binary(Vec<Bool>);

impl Binary {
    pub fn constant(x :usize) -> Binary {
        let mut v = Vec::new();
        let mut i = x;
        while i > 0 {
            v.push(if i%2 == 1 { true.into() } else { false.into() });
            i /= 2;
        }
        Binary(v)
    }

    pub fn invert(&self) -> Binary {
        Binary(self.0.iter().cloned().map(|x| !x).collect())
    }

    pub fn from_list<I :IntoIterator<Item = Bool>>(xs :I) -> Binary {
        Binary(xs.into_iter().collect())
    }

    pub fn count(&self, solver :&mut Sat) -> Binary {
        let bins = self.0.iter().cloned().map(|d| Binary::from_list(once(d)))
            .collect::<Vec<_>>();
        Binary::add_list(solver, bins.iter())
    }

    pub fn add(&self, solver :&mut Sat, other :&Binary) -> Binary {
        Binary::add_list(solver, once(self).chain(once(other)))
    }

    pub fn add_list<'a, I :IntoIterator<Item = &'a Binary>>(solver :&mut Sat, xs :I) -> Binary {
        Binary::add_bits(solver, 
                         xs.into_iter().flat_map(|x| x.0.iter().cloned()
                                                 .enumerate()).collect())
    }

    pub fn add_bits(solver :&mut Sat, xs :Vec<(usize,Bool)>) -> Binary {
        #[derive(Debug)]
        struct Item { bit :usize, val :Bool };
        let mut xs = xs.into_iter().map(|(bit,val)| Item { bit, val }).collect::<Vec<_>>();
        xs.sort_by_key(|&Item { bit, .. }| bit);
        let mut out = Vec::new();
        let mut i = 0;

        while xs.len() > 0 {
            if i < xs[0].bit {
                out.push(false.into());
                i = i+1;
            } else if xs.len() >= 3 && xs[0].bit == xs[1].bit && xs[1].bit == xs[2].bit {
                let Item { bit     , val: a_val } = xs.remove(0);
                let Item { bit: _,   val: b_val } = xs.remove(0);
                let Item { bit: _,   val: c_val } = xs.remove(0);
                let (v,c) = Binary::full_add(solver, a_val, b_val, c_val);
                xs.push(Item { bit: bit, val: v });
                xs.push(Item { bit: bit + 1, val: c });
                xs.sort_by_key(|&Item { bit, .. }| bit);
                i = bit;
            } else if xs.len() >= 2 && xs[0].bit == xs[1].bit {
                let Item { bit     , val: a_val } = xs.remove(0);
                let Item { bit: _,   val: b_val } = xs.remove(0);
                let (v,c) = Binary::full_add(solver, a_val, b_val, false.into());
                out.push(v);
                xs.push(Item { bit: bit + 1, val: c });
                xs.sort_by_key(|&Item { bit, .. }| bit);
                i = bit + 1;
            } else {
                let Item { bit, val } = xs.remove(0);
                out.push(val);
                i = bit + 1;
            }
        }

        Binary(out)
    }

    fn full_add(solver: &mut Sat, a :Bool, b :Bool, c :Bool) -> (Bool, Bool) {
        let v = solver.xor_literal(once(a).chain(once(b)).chain(once(c)));
        let c = Binary::at_least_two(solver, a, b, c);
        (v,c)
    }

    fn at_least_two(solver :&mut Sat, a :Bool, b :Bool, c :Bool) -> Bool {
        if a == true.into()       { solver.or_literal( once(b).chain(once(c))) }
        else if b == true.into()  { solver.or_literal( once(a).chain(once(c))) }
        else if c == true.into()  { solver.or_literal( once(a).chain(once(b))) }
        else if a == false.into() { solver.and_literal(once(b).chain(once(c))) }
        else if b == false.into() { solver.and_literal(once(a).chain(once(c))) }
        else if c == false.into() { solver.and_literal(once(a).chain(once(b))) }
        else if a == b { a }
        else if b == c { b }
        else if a == c { c }
        else if a == !b { c }
        else if b == !c { a }
        else if a == !c { b }
        else {
            let v = solver.new_lit();
            solver.add_clause(once(!a).chain(once(!b)).chain(once(v)));
            solver.add_clause(once(!a).chain(once(!c)).chain(once(v)));
            solver.add_clause(once(!b).chain(once(!c)).chain(once(v)));
            solver.add_clause(once( a).chain(once( b)).chain(once(!v)));
            solver.add_clause(once( a).chain(once( c)).chain(once(!v)));
            solver.add_clause(once( b).chain(once( c)).chain(once(!v)));
            v
        }
    }

    pub fn bound(&self) -> usize {
        (2 as usize).pow(self.0.len() as u32) -1
    }

    pub fn mul_digit(&self, solver :&mut Sat, y :Bool) -> Binary {
        Binary(self.0.iter().cloned().map(|x| solver.and_literal(once(x).chain(once(y)))).collect())
    }

    pub fn mul(&self, solver :&mut Sat, other :&Binary) -> Binary {
        let mut out = Vec::new();
        for (i,x) in self.0.iter().cloned().enumerate() {
            for (j,y) in other.0.iter().cloned().enumerate() {
                let z = solver.and_literal(once(x).chain(once(y)));
                out.push(((i+j), z));
            }
        }

        Binary::add_bits(solver, out)
    }
}



#[derive(Debug,Clone)]
pub struct Unary(Vec<Bool>);

impl Unary {
    pub fn constant(n :usize) -> Self {
        Unary(vec![true.into(); n])
    }

    pub fn succ(&self) -> Unary {
        Unary(once(Bool::Const(true)).chain(self.0.iter().cloned()).collect())
    }

    pub fn pred(&self) -> Unary {
        if self.0.len() == 0 {
            Unary::constant(0)
        } else {
            Unary(self.0.iter().cloned().skip(1).collect())
        }
    }

    pub fn invert(&self) -> Self {
        let mut v = self.0.clone();
        v.reverse();
        for x in &mut v { *x = !*x; }
        Unary(v)
    }

    pub fn gt_const(&self, x :isize) -> Bool {
        if x < 0 {
            Bool::Const(true)
        } else if x > self.0.len() as isize {
            Bool::Const(false)
        } else {
            (self.0)[x as usize]
        }
    }

    pub fn lt_const(&self, x :isize) -> Bool {
        !(self.gte_const(x))
    }

    pub fn lte_const(&self, x :isize) -> Bool {
        self.lt_const(x+1)
    }

    pub fn gte_const(&self, x :isize) -> Bool {
        self.gt_const(x-1)
    }

    pub fn mul_const(&self, c :usize) -> Unary {
        use std::iter::repeat;
        Unary(self.0.iter().flat_map(|i| repeat(i).take(c)).cloned().collect())
    }

    pub fn div_const(&self, c :usize) -> Unary {
        assert!(c > 0);
        Unary(self.0.chunks(c).flat_map(|x| x.get(c-1)).cloned().collect())
    }

    // pub fn mod_const(&self, c :usize) -> Unary {
    //     unimplemented!()
    // }

    pub fn bound(&self) -> usize {
        self.0.len()
    }

    pub fn add_const(&self, c :usize) -> Unary {
        use std::iter::repeat;
        Unary(repeat(Bool::Const(true)).take(c).chain(self.0.iter().cloned()).collect())
    }

    pub fn add(&self, sat :&mut Sat, other :&Unary) -> Unary {
        self.add_truncate(sat, other, std::usize::MAX)
    }

    pub fn truncate(&self, bound :usize) -> Unary {
        Unary(self.0.iter().take(bound).cloned().collect())
    }

    pub fn add_truncate(&self, sat :&mut Sat, other :&Unary, bound :usize) -> Unary {
        Unary(Self::merge(sat, bound, self.0.clone(), other.0.clone()))
    }

    fn merge(sat :&mut Sat, bound :usize, mut a :Vec<Bool>, mut b :Vec<Bool>) -> Vec<Bool> {
        use itertools::Itertools;
        if a.len() == 0 {
            b.truncate(bound);
            b
        } else if b.len() == 0 {
            a.truncate(bound);
            a
        } else if bound == 0 && a.len() == 1 && b.len() == 1 {
            Vec::new()
        } else if bound == 1 && a.len() == 1 && b.len() == 1 {
            let fst = sat.or_literal(once(a[0]).chain(once(b[0])));
            vec![fst]
        } else if bound > 1 && a.len() == 1 && b.len() == 1 {
            let fst = sat.or_literal( once(a[0]).chain(once(b[0])));
            let snd = sat.and_literal(once(a[0]).chain(once(b[0])));
            vec![fst,snd]
        } else {
            while a.len() < b.len()/2*2 { a.push(Bool::Const(false)); }
            while b.len() < a.len()/2*2 { b.push(Bool::Const(false)); }
            let firsts  = Self::merge(sat, bound, a.iter().cloned().step_by(2).collect(),
                                                  b.iter().cloned().step_by(2).collect());
            let seconds = Self::merge(sat, bound, a.iter().cloned().skip(1).step_by(2).collect(),
                                                  b.iter().cloned().skip(1).step_by(2).collect());
            let interleaved = firsts.into_iter().interleave(seconds.into_iter()).collect::<Vec<_>>();

            let mut v = Vec::new();
            v.push(interleaved[0]);
            for x in interleaved[1..].chunks(2) {
                if let [a,b] = x {
                    v.extend(Self::merge(sat, bound, vec![*a], vec![*b]));
                }
            }
            v.push(*interleaved.last().unwrap());
            v.truncate(bound);
            v
        }
    }

    pub fn sum(sat :&mut Sat, xs :Vec<Unary>) -> Unary {
        Self::sum_truncate(sat, xs, std::usize::MAX)
    }

    pub fn sum_truncate(sat :&mut Sat, mut xs :Vec<Unary>, bound :usize) -> Unary {
        if xs.len() == 0 {
            Unary::constant(0)
        } else if xs.len() == 1 {
            xs[0].clone()
        } else {
            xs.sort_by_key(|x| -(x.0.len() as isize));
            let a = xs.pop().unwrap();
            let b = xs.pop().unwrap();
            xs.push(a.add_truncate(sat, &b, bound));
            Self::sum_truncate(sat, xs, bound)
        }
    }

    pub fn mul_digit(&self, sat :&mut Sat, other :Bool) -> Unary {
        Unary(self.0.iter().cloned().map(|x| 
                 sat.and_literal(once(x).chain(once(other)))).collect())
    }

    pub fn mul(&self, sat :&mut Sat, other :&Unary) -> Unary {
        if self.bound() > other.bound() {
            other.mul(sat,self)
        } else {
            let terms = self.0.iter().cloned().map(|x|
                            other.mul_digit(sat, x)).collect();
            Unary::sum(sat, terms)
        }
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
    pub fn new_lit(&mut self) -> Bool {
        Bool::Lit(Lit(self.ptr, unsafe { minisat_newLit(self.ptr) }))
    }

    pub fn new_unary(&mut self, size :usize) -> Unary {
        let lits = (0..size).map(|_| self.new_lit()).collect::<Vec<_>>();
        for i in 1..size {
            self.add_clause(once(!lits[i]).chain(once(lits[i-1])));
        }
        Unary(lits)
    }

    pub fn new_binary(&mut self, size :usize) -> Binary {
        let (mut bits, mut n) = (0,size);
        while n > 0 {
            bits += 1;
            n /= 2;
        }
        let lits = (0..bits).map(|_| self.new_lit()).collect::<Vec<_>>();
        Binary(lits)
    }

    pub fn bool_to_unary(&mut self, digit :Bool) -> Unary {
        Unary(vec![digit])
    }

    pub fn count<I: IntoIterator<Item = Bool>>(&mut self, lits :I) -> Unary {
        let lits = lits.into_iter().map(|x| self.bool_to_unary(x)).collect();
        Unary::sum(self, lits)
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

impl Drop for Sat {
    fn drop(&mut self) {
        unsafe { minisat_delete(self.ptr); }
    }
}

use std::fmt;
impl fmt::Debug for Sat {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "SAT instance (MiniSat v2.1.0) {{ variables: {}, clauses: {} }}", self.num_vars(), self.num_clauses())
    }
}


/// A model, in the logic sense, contains and assignments to each variable
/// in the SAT instance which satisfies the clauses added to the problem.
pub struct Model<'a>(&'a mut Sat);

pub trait ModelValue<'a> {
    type T;
    fn value(&'a self, m: &'a Model) -> Self::T;
}

use std::iter::{once,empty};

impl ModelOrd for Unary {
    fn assert_less_or(solver :&mut Sat, prefix :Vec<Bool>, inclusive :bool, a :&Unary, b :&Unary) {
        if !inclusive {
            Self::assert_less_or(solver, prefix, true, &a.succ(), b);
        } else {
            for i in 0..(a.0.len()) {
                if i < b.0.len() {
                    solver.add_clause(prefix.iter().cloned()
                                      .chain(once(!(a.0)[i]))
                                      .chain(once((b.0)[i])));
                } else {
                    solver.add_clause(prefix.iter().cloned()
                                      .chain(once(!(a.0)[i])));
                    break;
                }
            }
        }
    }
}


impl ModelOrd for Binary {
    fn assert_less_or(solver :&mut Sat, prefix :Vec<Bool>, inclusive :bool, a :&Binary, b:&Binary) {
        use std::iter::repeat;
        let len = a.0.len().max(b.0.len());
        let mut a_bits = a.0.iter().cloned().chain(repeat(false.into()))
            .take(len).collect::<Vec<_>>();
        a_bits.reverse();
        let mut b_bits = b.0.iter().cloned().chain(repeat(false.into()))
            .take(len).collect::<Vec<_>>();
        b_bits.reverse();
        <&[Bool]>::assert_less_or(solver, prefix, inclusive, 
                                  &&a_bits.as_slice(), 
                                  &&b_bits.as_slice());
    }
}


impl ModelEq for Unary {
    fn assert_equal_or(solver :&mut Sat, prefix: Vec<Bool>, a :&Unary, b :&Unary) {
        solver.less_than_equal_or(prefix.clone(), a, b);
        solver.less_than_equal_or(prefix, b, a);
    }

    fn assert_not_equal_or(solver :&mut Sat, prefix :Vec<Bool>, a :&Unary, b :&Unary) {
        let q = solver.new_lit();
        solver.less_than_or(prefix.iter().cloned().chain(once(q)),  a, b);
        solver.less_than_or(prefix.iter().cloned().chain(once(!q)), b, a);
    }
}


impl ModelEq for Binary {
    fn assert_equal_or(solver :&mut Sat, prefix: Vec<Bool>, a :&Binary, b :&Binary) {
        let mut i = 0;
        while i < a.0.len() || i < b.0.len() {
            Bool::assert_equal_or(solver, prefix.clone(), a.0.get(i).unwrap_or(&false.into()),
                                                  b.0.get(i).unwrap_or(&false.into()));
            i += 1;
        }
    }

    fn assert_not_equal_or(solver :&mut Sat, mut prefix: Vec<Bool>, a :&Binary, b :&Binary) {
        let mut i = 0;
        let mut q = solver.new_lit();
        prefix.push(q);

        while i < a.0.len() || i < b.0.len() {
            let ai = a.0.get(i).cloned().unwrap_or(false.into());
            let bi = b.0.get(i).cloned().unwrap_or(false.into());

            Bool::assert_not_equal_or(solver, prefix.clone(), &ai, &bi);
            prefix.clear();
            prefix.push(!q);

            q = solver.new_lit();
            i += 1;
        }
        solver.add_clause(prefix);
    }
}


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

impl<'a> ModelValue<'a> for Unary {
    type T = usize;
    fn value(&self, m :&Model) -> usize {
        self.0.iter().enumerate()
            .find(|(_i,x)| !m.value(*x))
            .map(|(v,_)| v)
            .unwrap_or(self.0.len())
    }
}

impl<'a> ModelValue<'a> for Binary {
    type T = usize;
    fn value(&self, m :&Model) -> usize {
        self.0.iter().enumerate()
            .map(|(i,x)| if m.value(x) { (2 as usize).pow(i as u32) } else { 0 })
            .sum()
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
    fn xor() {
        let mut sat = Sat::new();
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
        let mut sat = Sat::new();
        let a = sat.new_unary(100);
        let b = sat.new_unary(200);
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
        let mut coloring = Sat::new();

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
        let mut sat = Sat::new();
        let a = sat.new_unary(20);
        let b = sat.new_unary(20);
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
        let mut sat = Sat::new();
        let a = sat.new_binary(1000);
        let b = sat.new_binary(1000);
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
        let mut sat = Sat::new();
        let a = sat.new_binary(2_usize.pow(16));
        let b = sat.new_binary(123123123123);
        let c = sat.new_binary(1231231231239);


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
            let mut sat = Sat::new();
            let xs = xs.into_iter().map(|x| {
                println!("CONST BINARY EQ {}", x);
                let b = sat.new_binary(x);
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
            let mut sat = Sat::new();
            let f = sat.xor_literal(lits.iter().map(|_| false.into())) == false.into();
            let t = sat.xor_literal(lits.iter().map(|_| true.into())) == (lits.len() % 2 == 1).into();
            t && f
        }
    }

    quickcheck!  {
        fn xor_literal_lits(lits :Vec<bool>) -> bool {
            let mut sat = Sat::new();
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
            let mut sat = Sat::new();
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
            let mut sat = Sat::new();
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
            let mut sat = Sat::new();
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
            let mut sat = Sat::new();
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
