use std::env;
use std::fs::read_dir;
use std::fs::DirEntry;
use std::fs::File;
use std::io::Write;
use std::path::Path;

// build script's entry point
fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let destination = Path::new(&out_dir).join("tests.rs");
    let mut test_file = File::create(&destination).unwrap();

    // write test file header, put `use`, `const` etc there
    //write_header(&mut test_file);

    let test_data_directories = read_dir("./tests/bench/").unwrap();

    for (index, directory) in test_data_directories.enumerate() {
        write_test(&mut test_file, &directory.unwrap(), index);
    }
}

fn write_test(test_file: &mut File, directory: &DirEntry, count: usize) {
    let directory = directory.path().canonicalize().unwrap();
    let test_path = directory.display();
    let test_name = format!("test_{}", count);

    write!(
        test_file,
        include_str!("./tests/test_template"),
        test_name = test_name,
        test_path = test_path
    )
    .unwrap();
}
