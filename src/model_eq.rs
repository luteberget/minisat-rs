use super::{Solver, Bool};
use std::iter::once;

/// Object that can be compared and constrainted for equality.
pub trait ModelEq {
    fn assert_equal_or(solver: &mut Solver, prefix: Vec<Bool>, a: &Self, b: &Self);
    fn assert_not_equal_or(solver: &mut Solver, prefix: Vec<Bool>, a: &Self, b: &Self);
    fn is_equal(solver: &mut Solver, a: &Self, b: &Self) -> Bool {
        let q = solver.new_lit();
        Self::assert_equal_or(solver, vec![!q], a, b);
        Self::assert_not_equal_or(solver, vec![q], a, b);
        q
    }
}


impl ModelEq for Bool {
    fn assert_equal_or(solver: &mut Solver, prefix: Vec<Bool>, a: &Bool, b: &Bool) {
        solver.add_clause(prefix.iter().cloned().chain(once(!*a)).chain(once(*b)));
        solver.add_clause(prefix.iter().cloned().chain(once(*a)).chain(once(!*b)));
    }

    fn assert_not_equal_or(solver: &mut Solver, prefix: Vec<Bool>, a: &Bool, b: &Bool) {
        Self::assert_equal_or(solver, prefix, a, &!*b);
    }

    fn is_equal(solver: &mut Solver, a: &Bool, b: &Bool) -> Bool {
        solver.xor_literal(once(*a).chain(once(!*b)))
    }
}
