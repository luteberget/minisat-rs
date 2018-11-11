[MiniSat](http://minisat.se) Rust interface. 
Solves a boolean satisfiability problem given in conjunctive normal form.

```rust
extern crate minisat;
use std::iter::once;
fn main() {
    let mut sat = minisat::Sat::new();
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

High-level features ported from [satplus](https://github.com/koengit/satplus):
 * Traits for representing non-boolean values in the SAT problem:
    * Value trait (`ModelValue`)
    * Equality trait (`ModelEq`)
    * Ordering trait (`ModelOrd`)
 * Symbolic values (`Symbolic<V>`)
 * Non-negative integers with unary encoding (`Unary`)

Graph coloring example:
```rust
extern crate minisat;
use std::iter::once;
fn main() {
    let mut coloring = minisat::Sat::new();

    #[derive(PartialEq, Eq, Debug, PartialOrd, Ord)]
    enum Color { Red, Green, Blue };

    let n_nodes = 5;
    let edges = vec![(0,1),(1,2),(2,3),(3,4),(3,1),(4,0),(4,2)];
    let colors = (0..n_nodes)
        .map(|_| coloring.new_symbolic(vec![Color::Red, Color::Green, Color::Blue]))
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
```

Factorization example:
```rust
extern crate minisat;

fn main() {
    let mut sat = minisat::Sat::new();
    let a = sat.new_unary(64);
    let b = sat.new_unary(64);
    let c = a.mul(&mut sat, &b);
    sat.equal(&c, &minisat::Unary::constant(529));

    match sat.solve() {
        Ok(model) => {
            println!("{}*{}=529", model.value(&a), model.value(&b));
        },
        Err(()) => {
            println!("No solution.");
        }
    }
}
```
