//! Cumulative Normal Form (CNF) Structure

use std::collections::BTreeSet;
use std::iter::once;
use std::ops::{BitAnd, BitOr, BitXor, Not};

use super::Lit;

/// A structure for creating and manipulating boolean expressions in CNF
#[derive(Debug, Clone)]
pub struct Cnf(pub(crate) BTreeSet<BTreeSet<Lit>>);

impl From<Lit> for Cnf {
    fn from(l: Lit) -> Self {
        Self(once(once(l).collect()).collect())
    }
}

impl Cnf {
    /// Create an And clause between multiple AST. The iterator cannot be empty!
    pub fn and(elems: impl IntoIterator<Item = Cnf>) -> Cnf {
        // TODO implement a more performant version.
        elems.into_iter().reduce(|a, b| a & b).unwrap()
    }

    /// Create an Or clause between multiple AST. The iterator cannot be empty!
    pub fn or(elems: impl IntoIterator<Item = Cnf>) -> Cnf {
        // TODO implement a more performant version.
        elems.into_iter().reduce(|a, b| a | b).unwrap()
    }

    /// Create an Implication clause.
    pub fn implies(self, rhs: impl Into<Cnf>) -> Cnf {
        (!self) | rhs.into()
    }

    /// Create an Iff clause.
    pub fn iff(self, rhs: impl Into<Cnf>) -> Cnf {
        let rhs: Cnf = rhs.into();
        (self.clone() | (!rhs.clone())) & ((!self) | rhs)
    }
}

impl Not for Cnf {
    type Output = Cnf;

    fn not(self) -> Self::Output {
        assert!(!self.0.is_empty());
        // we will use construction in this case, instead of manually transforming it. Notice,
        // that we can simply transform the statement into the following one, containing only
        // or, and not:
        //
        // Not(And(Or(a, b), Or(c, d)))
        // => Or(Not(Or(a, b)), Not(Or(c, d))
        //
        // Since we have already implemented the not case for or, and we have implemented or
        // for any CNF, we can do the following:
        //
        // self.0
        //     .into_iter()
        //     .map(|or| Self(once(or).collect()).not())
        //     .reduce(|a, b| a | b)
        //     .unwrap()
        //
        // in fact, we can use the not operation of a single or condition as follows:
        //
        // Not(Or(a, b)) = And(Not(a), Not(b)) = And(Or(Not(a)), Or(Not(b)))
        //
        // Hence, we perform this operation inside of the Self. This means, that we don't need
        // do the case distinction.
        self.0
            .into_iter()
            .map(|or| {
                // perform the Not(Or(a, b)) = And(Or(Not(a)), Or(Not(b)))
                Self(
                    or.into_iter()
                        .map(|lit| once(lit.not()).collect())
                        .collect(),
                )
            })
            // Combine all with an or, using construction.
            .reduce(|a, b| a | b)
            .unwrap()
    }
}

impl BitAnd for Cnf {
    type Output = Cnf;

    fn bitand(mut self, mut rhs: Self) -> Self::Output {
        self.0.append(&mut rhs.0);
        self
    }
}

impl BitAnd for Lit {
    type Output = Cnf;

    fn bitand(self, rhs: Self) -> Self::Output {
        let lhs: Cnf = self.into();
        let rhs: Cnf = rhs.into();
        lhs & rhs
    }
}

impl BitOr for Cnf {
    type Output = Cnf;

    fn bitor(self, rhs: Self) -> Self::Output {
        if self.0.len() == 1 && rhs.0.len() == 1 {
            // both are or
            let mut lhs_or = self.0.into_iter().next().unwrap();
            let mut rhs_or = rhs.0.into_iter().next().unwrap();
            lhs_or.append(&mut rhs_or);
            Self(once(lhs_or).collect())
        } else if self.0.len() == 1 || rhs.0.len() == 1 {
            // one is or, ther other is and
            let (or, and) = if self.0.len() == 1 {
                (self.0.into_iter().next().unwrap(), rhs.0)
            } else {
                (rhs.0.into_iter().next().unwrap(), self.0)
            };
            // OR(OR(a, b), And(Or(c, d), OR(e, f)))
            // => And(Or(a, b, c, d), Or(a, b, e, f))
            Self(
                and.into_iter()
                    .map(|mut x| {
                        x.extend(or.iter().cloned());
                        x
                    })
                    .collect(),
            )
        } else {
            // both are clauses of and
            // Or(And(Or(a, b), Or(c, d)), And(Or(e, f), Or(g, h)))
            Self(
                self.0
                    .into_iter()
                    .map(|a| {
                        rhs.0.iter().cloned().map(move |mut b| {
                            b.extend(a.iter());
                            b
                        })
                    })
                    .flatten()
                    .collect(),
            )
        }
    }
}

impl BitOr for Lit {
    type Output = Cnf;

    fn bitor(self, rhs: Self) -> Self::Output {
        let lhs: Cnf = self.into();
        let rhs: Cnf = rhs.into();
        lhs | rhs
    }
}

impl BitXor for Cnf {
    type Output = Cnf;

    fn bitxor(self, rhs: Self) -> Self::Output {
        (self.clone() | rhs.clone()) & ((!self) | (!rhs))
    }
}

impl BitXor for Lit {
    type Output = Cnf;

    fn bitxor(self, rhs: Self) -> Self::Output {
        let lhs: Cnf = self.into();
        let rhs: Cnf = rhs.into();
        lhs ^ rhs
    }
}

#[cfg(test)]
mod tests {
    use std::iter::FromIterator;

    use super::*;
    use crate::Solver;

    #[test]
    fn constructor() {
        let mut sat = Solver::new();
        let a = sat.new_lit();
        let x: Cnf = a.into();
        assert_eq_cnf(x, &[&[a]]);
    }

    #[test]
    fn cnf_or_lit() {
        let mut sat = Solver::new();
        let a = sat.new_lit();
        let b = sat.new_lit();
        let x = a | b;
        assert_eq_cnf(x, &[&[a, b]]);
    }

    #[test]
    fn cnf_and_lit() {
        let mut sat = Solver::new();
        let a = sat.new_lit();
        let b = sat.new_lit();
        let x = a & b;
        assert_eq_cnf(x, &[&[a], &[b]]);
    }

    #[test]
    fn cnf_not_lit() {
        let mut sat = Solver::new();
        let a = sat.new_lit();
        let x: Cnf = a.into();
        assert_eq_cnf(!x, &[&[a.not()]]);
    }

    #[test]
    fn cnf_xor_lit() {
        let mut sat = Solver::new();
        let a = sat.new_lit();
        let b = sat.new_lit();
        let x = a ^ b;
        assert_eq_cnf(x, &[&[a, b], &[a.not(), b.not()]]);
    }

    #[test]
    fn cnf_iff_lit() {
        let mut sat = Solver::new();
        let a = sat.new_lit();
        let b = sat.new_lit();
        let a_cnf: Cnf = a.into();
        let x = a_cnf.iff(b);
        assert_eq_cnf(x, &[&[a, b.not()], &[a.not(), b]]);
    }

    #[test]
    fn cnf_implies_lit() {
        let mut sat = Solver::new();
        let a = sat.new_lit();
        let b = sat.new_lit();
        let a_cnf: Cnf = a.into();
        let x = a_cnf.implies(b);
        assert_eq_cnf(x, &[&[a.not(), b]]);
    }

    #[test]
    fn cnf_or_expr() {
        let mut sat = Solver::new();
        let a = sat.new_lit();
        let b = sat.new_lit();
        let c = sat.new_lit();
        let d = sat.new_lit();
        let e = sat.new_lit();
        let f = sat.new_lit();
        let g = sat.new_lit();
        let h = sat.new_lit();
        let x = (a | b) & (c | d);
        let y = (e | f) & (g | h);
        assert_eq_cnf(
            x | y,
            &[&[a, b, e, f], &[c, d, e, f], &[a, b, g, h], &[c, d, g, h]],
        );
    }

    #[test]
    fn cnf_and_expr() {
        let mut sat = Solver::new();
        let a = sat.new_lit();
        let b = sat.new_lit();
        let c = sat.new_lit();
        let d = sat.new_lit();
        let e = sat.new_lit();
        let f = sat.new_lit();
        let g = sat.new_lit();
        let h = sat.new_lit();
        let x = (a | b) & (c | d);
        let y = (e | f) & (g | h);
        assert_eq_cnf(x & y, &[&[a, b], &[c, d], &[e, f], &[g, h]]);
    }

    #[test]
    fn cnf_not_expr() {
        let mut sat = Solver::new();
        let a = sat.new_lit();
        let b = sat.new_lit();
        let c = sat.new_lit();
        let d = sat.new_lit();
        let x = (a | b) & (c | d);
        assert_eq_cnf(
            !x,
            &[
                &[a.not(), c.not()],
                &[b.not(), c.not()],
                &[a.not(), d.not()],
                &[b.not(), d.not()],
            ],
        );
    }

    #[test]
    fn cnf_xor_expr() {
        let mut sat = Solver::new();
        let a = sat.new_lit();
        let b = sat.new_lit();
        let c = sat.new_lit();
        let d = sat.new_lit();
        let e = sat.new_lit();
        let f = sat.new_lit();
        let g = sat.new_lit();
        let h = sat.new_lit();
        let x = (a | b) & (c | d);
        let y = (e | f) & (g | h);
        assert_eq_cnf(
            x ^ y,
            &[
                &[a, b, e, f],
                &[a, b, g, h],
                &[c, d, e, f],
                &[c, d, g, h],
                &[!a, !c, !e, !g],
                &[!b, !c, !e, !g],
                &[!a, !d, !e, !g],
                &[!b, !d, !e, !g],
                &[!a, !c, !f, !g],
                &[!b, !c, !f, !g],
                &[!a, !d, !f, !g],
                &[!b, !d, !f, !g],
                &[!a, !c, !e, !h],
                &[!b, !c, !e, !h],
                &[!a, !d, !e, !h],
                &[!b, !d, !e, !h],
                &[!a, !c, !f, !h],
                &[!b, !c, !f, !h],
                &[!a, !d, !f, !h],
                &[!b, !d, !f, !h],
            ],
        );
    }

    #[test]
    fn cnf_iff_expr() {
        let mut sat = Solver::new();
        let a = sat.new_lit();
        let b = sat.new_lit();
        let c = sat.new_lit();
        let d = sat.new_lit();
        let e = sat.new_lit();
        let f = sat.new_lit();
        let g = sat.new_lit();
        let h = sat.new_lit();
        let x = (a | b) & (c | d);
        let y = (e | f) & (g | h);
        assert_eq_cnf(
            x.iff(y),
            &[
                &[a, b, !e, !g],
                &[a, b, !f, !g],
                &[a, b, !e, !h],
                &[a, b, !f, !h],
                &[c, d, !e, !g],
                &[c, d, !f, !g],
                &[c, d, !e, !h],
                &[c, d, !f, !h],
                &[!a, !c, e, f],
                &[!b, !c, e, f],
                &[!a, !d, e, f],
                &[!b, !d, e, f],
                &[!a, !c, g, h],
                &[!b, !c, g, h],
                &[!a, !d, g, h],
                &[!b, !d, g, h],
            ],
        );
    }

    #[test]
    fn cnf_implies_expr() {
        let mut sat = Solver::new();
        let a = sat.new_lit();
        let b = sat.new_lit();
        let c = sat.new_lit();
        let d = sat.new_lit();
        let e = sat.new_lit();
        let f = sat.new_lit();
        let g = sat.new_lit();
        let h = sat.new_lit();
        let x = (a | b) & (c | d);
        let y = (e | f) & (g | h);
        assert_eq_cnf(
            x.implies(y),
            &[
                &[!a, !c, e, f],
                &[!b, !c, e, f],
                &[!a, !d, e, f],
                &[!b, !d, e, f],
                &[!a, !c, g, h],
                &[!b, !c, g, h],
                &[!a, !d, g, h],
                &[!b, !d, g, h],
            ],
        );
    }

    fn assert_eq_cnf(acq: Cnf, exp: &[&[Lit]]) {
        let acq = acq.0;
        let exp: BTreeSet<BTreeSet<Lit>> =
            BTreeSet::from_iter(exp.iter().map(|x| BTreeSet::from_iter(x.iter().cloned())));
        assert_eq!(acq, exp)
    }
}
