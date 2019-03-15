use glob::glob;
use std::env;
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};

fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let destination = Path::new(&out_dir).join("tests.rs");
    let mut test_file = File::create(&destination).unwrap();

    for directory in glob("./tests/bench/**/*.json").unwrap() {
        write_test(&mut test_file, &directory.unwrap());
    }
}

fn write_test(test_file: &mut File, test_path: &PathBuf) {
    let test_name = format!(
        "test_{}",
        test_path
            .strip_prefix("tests/bench")
            .unwrap()
            .display()
            .to_string()
            .replace("/", "_")
            .replace(".json", "")
            .replace(".", "")
    );

    write!(
        test_file,
        include_str!("./tests/test_template"),
        test_name = test_name,
        test_path = test_path.display()
    )
    .unwrap();
}
