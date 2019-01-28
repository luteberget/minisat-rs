extern crate cc;
extern crate bindgen;

use std::env;
use std::path::PathBuf;


pub fn main() {
    cc::Build::new()
        .include("lib/minisat")
        .file("lib/minisat/minisat/core/Solver.cc")
        .file("lib/minisat/minisat/simp/SimpSolver.cc")
        .file("lib/minisat/minisat/utils/System.cc")
        //.file("lib/minisat/minisat/utils/Options.cc")
        .file("lib/minisat-c-bindings/minisat.cc")
        .define("__STDC_LIMIT_MACROS", None)
        .define("__STDC_FORMAT_MACROS", None)
        .include("/usr/local/include")
        .compile("minisat");

    let bindings = bindgen::Builder::default()
        .clang_arg("-Ilib/minisat-c-bindings")
        .header("wrapper.h")
        .generate()
        .expect("Could not create bindings to library");

    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
        bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");


    println!("cargo:rustc-flags=-l dylib=stdc++");
}
