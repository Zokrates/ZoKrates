use fs_extra::copy_items;
use fs_extra::dir::CopyOptions;
use std::env;

fn main() {
    // export js test folder to OUT_DIR
    export_stdlib();
}

fn export_stdlib() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let mut options = CopyOptions::new();
    options.overwrite = true;
    copy_items(&["tests/contract"], out_dir, &options).unwrap();
}
