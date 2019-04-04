use fs_extra::copy_items;
use fs_extra::dir::CopyOptions;
use std::env;

fn main() {
    // export stdlib folder to OUT_DIR
    export_stdlib();

    // generate tests
    #[cfg(test)]
    {
        write_tests();
    }
}

fn export_stdlib() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let mut options = CopyOptions::new();
    options.overwrite = true;
    copy_items(&vec!["stdlib"], out_dir, &options).unwrap();
}

#[cfg(test)]
fn write_tests() {
    use glob::glob;
    use std::fs::File;
    use std::io::Write;
    use std::path::{Path, PathBuf};

    let out_dir = env::var("OUT_DIR").unwrap();
    let destination = Path::new(&out_dir).join("tests.rs");
    let mut test_file = File::create(&destination).unwrap();

    for directory in glob("./tests/bench/**/*.json").unwrap() {
        write_test(&mut test_file, &directory.unwrap());
    }
}

#[cfg(test)]
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
