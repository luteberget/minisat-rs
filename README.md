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

High-level features ported from [satplus](https://github.com/koengit/satplus):
 * Traits for representing non-boolean values in the SAT problem:
    * Value trait (`ModelValue`)
    * Equality trait (`ModelEq`)
    * Ordering trait (`ModelOrd`)
 * Symbolic values (`Symbolic<V>`)
 * Non-negative integers with unary encoding (`Unary`)
 * Non-negative integers with binary encoding (`Binary`)

Graph coloring example:
```rust
extern crate minisat;
use std::iter::once;
use minisat::symbolic::*;
fn main() {
    let mut coloring = minisat::Solver::new();

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
```

Factorization example:
```rust
extern crate minisat;
use minisat::{*, binary::*};

fn main() {
    let mut sat = Solver::new();
    let a = Binary::new(&mut sat, 1000);
    let b = Binary::new(&mut sat, 1000);
    let c = a.mul(&mut sat, &b);
    sat.equal(&c, &Binary::constant(36863));

    match sat.solve() {
        Ok(model) => {
            println!("{}*{}=36863", model.value(&a), model.value(&b));
        },
        Err(()) => {
            println!("No solution.");
        }
    }
}
```

Sudoku solver, based on the article [Modern SAT solvers: fast, neat and underused (part 1 of N)](https://codingnest.com/modern-sat-solvers-fast-neat-underused-part-1-of-n/). It uses the [sudoku crate](https://docs.rs/sudoku) for generating and displaying boards.

```rust
extern crate itertools;
extern crate sudoku;
use itertools::iproduct;
use minisat::Solver;
use minisat::symbolic::Symbolic;
use sudoku::Sudoku;

pub fn solve_sudoku(problem: &str) -> Option<String> {
    let mut s = Solver::new();
    let matrix = problem.chars().map(|c| {
        if let Some(i) = c.to_digit(10) {
            Symbolic::new(&mut s, vec![i - 1])
        } else {
            Symbolic::new(&mut s, (0..9).collect())
        }
    }).collect::<Vec<_>>();

    for val in 0..9 {
        // Rule 1: no row contains duplicate numbers
        for x in 0..9 {
            s.assert_at_most_one((0..9).map(|y| matrix[9 * y + x].has_value(&val)));
        }
        // Rule 2: no column contains duplicate numbers
        for y in 0..9 {
            s.assert_at_most_one((0..9).map(|x| matrix[9 * y + x].has_value(&val)));
        }
        // Rule 3: no 3x3 box contains duplicate numbers
        for (box_x, box_y) in iproduct!((0..9).step_by(3), (0..9).step_by(3)) {
            s.assert_at_most_one(
                iproduct!(0..3, 0..3)
                    .map(|(x, y)| matrix[9 * (box_x + x) + (box_y + y)].has_value(&val)),
            );
        }
    }

    s.solve().ok().map(|m| {
        matrix.into_iter()
            .map(|v| format!("{}", m.value(&v) + 1))
            .collect()
    })
}



fn main() {
    let puzzle = Sudoku::generate_unique();
    println!("{}", puzzle.display_block());

    let solution = solve_sudoku(&puzzle.to_str_line()).expect("Unable to solve puzzle");
    let solved_puzzle = Sudoku::from_str_line(&solution).expect("Unable to parse puzzle");

    println!("{}", solved_puzzle.display_block());
    assert!(solved_puzzle.is_solved());
}
```
