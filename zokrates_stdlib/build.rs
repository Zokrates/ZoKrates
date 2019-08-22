use fs_extra::copy_items;
use fs_extra::dir::CopyOptions;
use std::env;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use zokrates_test::write_tests;

fn main() {
    // export stdlib folder to OUT_DIR
    export_stdlib();

    // generate tests
    write_tests(Path::new("./tests/bench/"));
}

fn export_stdlib() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let mut options = CopyOptions::new();
    options.overwrite = true;
    copy_items(&vec!["stdlib"], out_dir, &options).unwrap();
}
