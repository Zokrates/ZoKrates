use std::env;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

pub fn write_tests(base: &str) {
    use glob::glob;

    let base = Path::new(&base);
    let out_dir = env::var("OUT_DIR").unwrap();
    let destination = Path::new(&out_dir).join("tests.rs");
    let test_file = File::create(destination).unwrap();
    let mut writer = BufWriter::new(test_file);

    for p in glob(base.join("**/*.json").to_str().unwrap()).unwrap() {
        write_test(&mut writer, &p.unwrap(), base);
    }
}

fn write_test<W: Write>(test_file: &mut W, test_path: &Path, base_path: &Path) {
    println!("{:?}", test_path);
    println!("{:?}", base_path);

    let test_name = format!(
        "test_{}",
        test_path
            .strip_prefix(base_path.strip_prefix("./").unwrap())
            .unwrap()
            .display()
            .to_string()
            .replace('/', "_")
            .replace(".json", "")
            .replace('.', "")
    );

    write!(
        test_file,
        include_str!("../test_template"),
        test_name = test_name,
        test_path = test_path.display()
    )
    .unwrap();
}
