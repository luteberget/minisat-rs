use std::iter::once;
use super::{Bool, Solver};

/// Object that can be compared and constrained by ordering.
pub trait ModelOrd {
    fn assert_less_or(solver: &mut Solver,
                      prefix: Vec<Bool>,
                      inclusive: bool,
                      a: &Self,
                      b: &Self) {
        Self::assert_less_tuple_or(solver, prefix, inclusive, (a, &()), (b, &()));
    }

    fn new_less_lit(solver: &mut Solver, inclusive: bool, a: &Self, b: &Self) -> Bool {
        let q = solver.new_lit();
        Self::assert_less_or(solver, vec![!q], inclusive, a, b);
        q
    }

    fn assert_less_tuple_or<B: ModelOrd>(solver: &mut Solver,
                                         prefix: Vec<Bool>,
                                         inclusive: bool,
                                         x_p: (&Self, &B),
                                         y_q: (&Self, &B)) {
        let (x, p) = x_p;
        let (y, q) = y_q;
        match B::new_less_lit(solver, inclusive, p, q) {
            Bool::Const(c) => Self::assert_less_or(solver, prefix, c.into(), x, y),
            lit => {
                Self::assert_less_or(solver, prefix.clone(), true, x, y);
                Self::assert_less_or(solver,
                                     prefix.iter().cloned().chain(once(lit)).collect(),
                                     false,
                                     x,
                                     y);
            }
        }
    }
}

impl ModelOrd for () {
    fn assert_less_or(solver: &mut Solver, prefix: Vec<Bool>, inclusive: bool, _a: &(), _b: &()) {
        if !inclusive {
            solver.add_clause(prefix);
        }
    }

    fn new_less_lit(_: &mut Solver, inclusive: bool, _a: &(), _b: &()) -> Bool {
        inclusive.into()
    }

    fn assert_less_tuple_or<B: ModelOrd>(solver: &mut Solver,
                                         prefix: Vec<Bool>,
                                         inclusive: bool,
                                         (_, p): (&(), &B),
                                         (_, q): (&(), &B)) {
        B::assert_less_or(solver, prefix, inclusive, p, q);
    }
}

impl ModelOrd for Bool {
    fn assert_less_tuple_or<B: ModelOrd>(solver: &mut Solver,
                                         prefix: Vec<Bool>,
                                         inclusive: bool,
                                         (x, p): (&Bool, &B),
                                         (y, q): (&Bool, &B)) {
        if x == y {
            B::assert_less_or(solver, prefix, inclusive, p, q);
        } else {
            let w = B::new_less_lit(solver, inclusive, p, q);
            solver.add_clause(prefix.iter().cloned().chain(once(*y)).chain(once(w)));
            solver.add_clause(prefix.iter().cloned().chain(once(!*x)).chain(once(w)));
            solver.add_clause(prefix.iter().cloned().chain(once(!*x)).chain(once(*y)));
        }

    }

    fn new_less_lit(solver: &mut Solver, inclusive: bool, a: &Bool, b: &Bool) -> Bool {
        if a == b {
            inclusive.into()
        } else if *a == !*b {
            b.clone()
        } else if let Bool::Const(false) = a {
            if inclusive { true.into() } else { b.clone() }
        } else if let Bool::Const(true) = a {
            if inclusive { b.clone() } else { false.into() }
        } else if let Bool::Const(false) = b {
            if inclusive {
                !(a.clone())
            } else {
                false.into()
            }
        } else if let Bool::Const(true) = b {
            if inclusive { true.into() } else { !(a.clone()) }
        } else {
            let q = solver.new_lit();
            Bool::assert_less_or(solver, vec![!q], inclusive, a, b);
            q
        }
    }
}




impl<'a> ModelOrd for &'a [Bool] {
    fn assert_less_or(solver: &mut Solver,
                      prefix: Vec<Bool>,
                      inclusive: bool,
                      a: &&[Bool],
                      b: &&[Bool]) {
        if a.len() > 0 && b.len() > 0 {
            Bool::assert_less_tuple_or(solver,
                                       prefix,
                                       inclusive,
                                       (&a[0], &&a[1..]),
                                       (&b[0], &&b[1..]));
        } else if a.len() > 0 {
            Bool::assert_less_tuple_or(solver,
                                       prefix,
                                       inclusive,
                                       (&a[0], &&a[1..]),
                                       (&false.into(), b));
        } else if b.len() > 0 {
            Bool::assert_less_tuple_or(solver,
                                       prefix,
                                       inclusive,
                                       (&false.into(), a),
                                       (&b[0], &&b[1..]));
        } else {
            if !inclusive {
                solver.add_clause(prefix);
            }
        }
    }
}
