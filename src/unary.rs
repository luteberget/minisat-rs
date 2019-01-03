use super::{Bool, Solver, Model, ModelEq, ModelOrd, ModelValue};
use std::iter::once;

#[derive(Debug,Clone)]
pub struct Unary(Vec<Bool>);

impl Unary {
    /// Create a new non-negative integer using a unary encoding.
    pub fn new(solver: &mut Solver, size: usize) -> Unary {
        let lits = (0..size).map(|_| solver.new_lit()).collect::<Vec<_>>();
        for i in 1..size {
            solver.add_clause(once(!lits[i]).chain(once(lits[i - 1])));
        }
        Unary(lits)
    }

    /// Use the given `Bool` as a one-digit number (zero or one).
    pub fn from_bool(digit: Bool) -> Unary {
        Unary(vec![digit])
    }

    /// A constant number in unary encoding (creates no new SAT literals).
    pub fn constant(n: usize) -> Self {
        Unary(vec![true.into(); n])
    }

    /// Unary representation of the number of true literals in set.
    pub fn count<I: IntoIterator<Item = Bool>>(solver: &mut Solver, lits: I) -> Unary {
        let lits = lits.into_iter().map(|x| Unary::from_bool(x)).collect();
        Unary::sum(solver, lits)
    }

    /// The successor of the given number.
    pub fn succ(&self) -> Unary {
        Unary(once(Bool::Const(true)).chain(self.0.iter().cloned()).collect())
    }

    /// The predecessor of the given number, except if the number is zero in
    /// which case the returned number is also zero.
    pub fn pred(&self) -> Unary {
        if self.0.len() == 0 {
            Unary::constant(0)
        } else {
            Unary(self.0.iter().cloned().skip(1).collect())
        }
    }

    /// Using the natural number's upper bound `b`, return a number `b-x`.
    pub fn invert(&self) -> Self {
        let mut v = self.0.clone();
        v.reverse();
        for x in &mut v {
            *x = !*x;
        }
        Unary(v)
    }

    /// Return a `Bool` which represents whether the number is greater than a given constant.
    pub fn gt_const(&self, x: isize) -> Bool {
        if x < 0 {
            Bool::Const(true)
        } else if x >= self.0.len() as isize {
            Bool::Const(false)
        } else {
            (self.0)[x as usize]
        }
    }

    /// Return a `Bool` which represents whether the number is less than a given
    /// non-negative integer constant.
    pub fn lt_const(&self, x: isize) -> Bool {
        !(self.gte_const(x))
    }

    /// Return a `Bool` which represents whether the number is less than or equal
    /// to a given non-negative integer constant.
    pub fn lte_const(&self, x: isize) -> Bool {
        self.lt_const(x + 1)
    }

    /// Return a `Bool` which represents whether the number is greater than or equal
    /// to a given non-negative integer constant.
    pub fn gte_const(&self, x: isize) -> Bool {
        self.gt_const(x - 1)
    }

    /// Multiply a `Unary` by a non-negative integer constant.
    pub fn mul_const(&self, c: usize) -> Unary {
        use std::iter::repeat;
        Unary(self.0.iter().flat_map(|i| repeat(i).take(c)).cloned().collect())
    }

    /// Integer division of a `Unary` by a non-negative integer constant.
    pub fn div_const(&self, c: usize) -> Unary {
        assert!(c > 0);
        Unary(self.0.chunks(c).flat_map(|x| x.get(c - 1)).cloned().collect())
    }

    // pub fn mod_const(&self, c :usize) -> Unary {
    //     unimplemented!()
    // }

    /// The upper bound.
    pub fn bound(&self) -> usize {
        self.0.len()
    }

    /// Addition by a non-negative integer constant.
    pub fn add_const(&self, c: usize) -> Unary {
        use std::iter::repeat;
        Unary(repeat(Bool::Const(true)).take(c).chain(self.0.iter().cloned()).collect())
    }

    /// Add two `Unary` numbers.
    pub fn add(&self, sat: &mut Solver, other: &Unary) -> Unary {
        self.add_truncate(sat, other, std::usize::MAX)
    }

    /// Return `max(bound, x)`.
    pub fn truncate(&self, bound: usize) -> Unary {
        Unary(self.0.iter().take(bound).cloned().collect())
    }

    /// Truncated add.
    pub fn add_truncate(&self, sat: &mut Solver, other: &Unary, bound: usize) -> Unary {
        Unary(Self::merge(sat, bound, self.0.clone(), other.0.clone()))
    }

    fn merge(sat: &mut Solver, bound: usize, mut a: Vec<Bool>, mut b: Vec<Bool>) -> Vec<Bool> {
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
            let fst = sat.or_literal(once(a[0]).chain(once(b[0])));
            let snd = sat.and_literal(once(a[0]).chain(once(b[0])));
            vec![fst, snd]
        } else {
            while a.len() < b.len() / 2 * 2 {
                a.push(Bool::Const(false));
            }
            while b.len() < a.len() / 2 * 2 {
                b.push(Bool::Const(false));
            }
            let firsts = Self::merge(sat,
                                     bound,
                                     a.iter().cloned().step_by(2).collect(),
                                     b.iter().cloned().step_by(2).collect());
            let seconds = Self::merge(sat,
                                      bound,
                                      a.iter().cloned().skip(1).step_by(2).collect(),
                                      b.iter().cloned().skip(1).step_by(2).collect());
            let interleaved =
                firsts.into_iter().interleave(seconds.into_iter()).collect::<Vec<_>>();

            let mut v = Vec::new();
            v.push(interleaved[0]);
            for x in interleaved[1..].chunks(2) {
                if let [a, b] = x {
                    v.extend(Self::merge(sat, bound, vec![*a], vec![*b]));
                }
            }
            v.push(*interleaved.last().unwrap());
            v.truncate(bound);
            v
        }
    }

    /// Sum a list of Unary numbers.
    pub fn sum(sat: &mut Solver, xs: Vec<Unary>) -> Unary {
        Self::sum_truncate(sat, xs, std::usize::MAX)
    }

    /// Truncated sum.
    pub fn sum_truncate(sat: &mut Solver, mut xs: Vec<Unary>, bound: usize) -> Unary {
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

    /// Multiply by a single digit given as a `Bool`.
    pub fn mul_digit(&self, sat: &mut Solver, other: Bool) -> Unary {
        Unary(self.0
            .iter()
            .cloned()
            .map(|x| sat.and_literal(once(x).chain(once(other))))
            .collect())
    }

    /// Multiply Unary numbers.
    pub fn mul(&self, sat: &mut Solver, other: &Unary) -> Unary {
        if self.bound() > other.bound() {
            other.mul(sat, self)
        } else {
            let terms = self.0
                .iter()
                .cloned()
                .map(|x| other.mul_digit(sat, x))
                .collect();
            Unary::sum(sat, terms)
        }
    }
}

impl ModelOrd for Unary {
    fn assert_less_or(solver: &mut Solver,
                      prefix: Vec<Bool>,
                      inclusive: bool,
                      a: &Unary,
                      b: &Unary) {
        if !inclusive {
            Self::assert_less_or(solver, prefix, true, &a.succ(), b);
        } else {
            for i in 0..(a.0.len()) {
                if i < b.0.len() {
                    solver.add_clause(prefix.iter()
                        .cloned()
                        .chain(once(!(a.0)[i]))
                        .chain(once((b.0)[i])));
                } else {
                    solver.add_clause(prefix.iter()
                        .cloned()
                        .chain(once(!(a.0)[i])));
                    break;
                }
            }
        }
    }
}

impl ModelEq for Unary {
    fn assert_equal_or(solver: &mut Solver, prefix: Vec<Bool>, a: &Unary, b: &Unary) {
        solver.less_than_equal_or(prefix.clone(), a, b);
        solver.less_than_equal_or(prefix, b, a);
    }

    fn assert_not_equal_or(solver: &mut Solver, prefix: Vec<Bool>, a: &Unary, b: &Unary) {
        let q = solver.new_lit();
        solver.less_than_or(prefix.iter().cloned().chain(once(q)), a, b);
        solver.less_than_or(prefix.iter().cloned().chain(once(!q)), b, a);
    }
}

impl<'a> ModelValue<'a> for Unary {
    type T = usize;
    fn value(&self, m: &Model) -> usize {
        self.0
            .iter()
            .enumerate()
            .find(|(_i, x)| !m.value(*x))
            .map(|(v, _)| v)
            .unwrap_or(self.0.len())
    }
}
