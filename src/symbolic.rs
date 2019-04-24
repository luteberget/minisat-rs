use super::{Bool, Solver, Model, ModelValue, ModelEq};
use std::iter::once;

#[derive(Debug)]
pub struct Symbolic<T>(Vec<(Bool, T)>);

impl<T> Symbolic<T> {
    pub fn domain(&self) -> impl Iterator<Item = &T> {
        self.0.iter().map(|(_, t)| t)
    }

    pub fn new(solver: &mut Solver, mut xs: Vec<T>) -> Symbolic<T> {
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
            solver.assert_exactly_one(lits.iter().cloned());
            Symbolic(lits.into_iter().zip(xs.into_iter()).collect())
        }
    }
}

impl<T: Eq> Symbolic<T> {
    pub fn has_value(&self, a: &T) -> Bool {
        for (v, x) in &self.0 {
            if x == a {
                return *v;
            }
        }
        false.into()
    }
}

impl<V: Ord> ModelEq for Symbolic<V> {
    fn assert_equal_or(solver: &mut Solver, prefix: Vec<Bool>, a: &Symbolic<V>, b: &Symbolic<V>) {
        for (p, q, x) in stitch(a, b) {
            match (p, q, x) {
                (Some(p), None, _) => solver.add_clause(once(!p).chain(prefix.iter().cloned())),
                (None, Some(q), _) => solver.add_clause(once(!q).chain(prefix.iter().cloned())),
                (Some(p), Some(q), _) => {
                    solver.add_clause(once(!p).chain(once(q)).chain(prefix.iter().cloned()))
                }
                _ => unreachable!(),
            }
        }
    }

    fn assert_not_equal_or(solver: &mut Solver,
                           prefix: Vec<Bool>,
                           a: &Symbolic<V>,
                           b: &Symbolic<V>) {
        for (p, q, x) in stitch(a, b) {
            match (p, q, x) {
                (Some(p), Some(q), _) => {
                    solver.add_clause(once(!p).chain(once(!q)).chain(prefix.iter().cloned()))
                }
                _ => {}
            }
        }
    }
}

fn stitch<'a, V: Ord>(a: &'a Symbolic<V>,
                      b: &'a Symbolic<V>)
                      -> impl Iterator<Item = (Option<Bool>, Option<Bool>, &'a V)> {
    use itertools::Itertools;
    let mut v: Vec<(Option<Bool>, Option<Bool>, &'a V)> = a.0
        .iter()
        .map(|(v, x)| (Some(*v), None, x))
        .chain(b.0.iter().map(|(v, x)| (None, Some(*v), x)))
        .collect();
    v.sort_by(|(_, _, x), (_, _, y)| x.cmp(y));
    v.into_iter().coalesce(|(a, b, x), (c, d, y)| if x == y {
        Ok((a.or(c), b.or(d), x))
    } else {
        Err(((a, b, x), (c, d, y)))
    })
}



impl<'a, V: 'a> ModelValue<'a> for Symbolic<V> {
    type T = &'a V;

    fn value(&'a self, m: &'a Model) -> Self::T {
        for (v, x) in &self.0 {
            if m.value(v) {
                return x;
            }
        }
        unreachable!()
    }
}
