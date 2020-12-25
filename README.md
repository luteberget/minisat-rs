[MiniSat](http://minisat.se) Rust interface.
Solves a boolean satisfiability problem given in conjunctive normal form.

```rust
extern crate minisat;
use std::iter::once;
fn main() {
    let mut sat = minisat::Solver::new();
    let a = sat.new_lit();
    let b = sat.new_lit();

    // Solves ((a OR not b) AND b)
    sat.add_clause(vec![a, !b]);
    sat.add_clause(vec![b]);

    match sat.solve() {
        Ok(m) => {
            assert_eq!(m.value(&a), true);
            assert_eq!(m.value(&b), true);
        },
        Err(()) => panic!("UNSAT"),
    }
}
```

This crate compiles the MiniSat sources directly and binds through
the [minisat-c-bindings](https://github.com/niklasso/minisat-c-bindings) interface.
The low-level C bindings are available through the [`sys`](sys/index.html) module.
