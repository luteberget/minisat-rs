[MiniSat](http://minisat.se) Rust interface. 
Solves a boolean satisfiability problem given in conjunctive normal form.

```rust
extern crate minisat;
fn main() {
    let mut sat = minisat::Sat::new();
    let a = sat.new_lit();
    let b = sat.new_lit();
    sat.add_clause(&[a, !b]);
    sat.add_clause(&[b]);
    match sat.solve() {
        Ok(m) => {
            assert_eq!(m.get(&a), Some(true));
            assert_eq!(m.get(&b), Some(true));
        },
        Err(()) => panic!("UNSAT"),
    }
}
```

This crate compiles the MiniSat sources directly and binds through
the [minisat-c-bindings](https://github.com/niklasso/minisat-c-bindings) interface.
The low-level C bindings are available through the [`sys`](sys/index.html) module. 
