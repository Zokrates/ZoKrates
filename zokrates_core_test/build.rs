use std::path::Path;
use zokrates_test::write_tests;

fn main() {
    // generate tests
    write_tests(Path::new("./tests/bench/"));
}
