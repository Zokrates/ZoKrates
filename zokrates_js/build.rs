use std::path::Path;
use std::{env, fs};
use walkdir::WalkDir;

fn main() {
    export_stdlib();
    export_metadata();
}

fn export_stdlib() {
    let root = "../zokrates_stdlib/stdlib";
    let mut stdlib = json::JsonValue::new_object();

    for entry in WalkDir::new(root)
        .into_iter()
        .map(Result::unwrap)
        .filter(|e| {
            !e.file_type().is_dir() && e.path().extension().map(|e| e == "zok").unwrap_or(false)
        })
    {
        let path: &Path = entry.path();
        let source = fs::read_to_string(path).unwrap();
        stdlib
            .insert(path.strip_prefix(root).unwrap().to_str().unwrap(), source)
            .unwrap();
    }

    let out_dir = env::var_os("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join("stdlib.json");

    fs::write(dest_path, stdlib.dump()).unwrap();
}

fn export_metadata() {
    let path = "../zokrates_cli/Cargo.toml";
    let config: toml::Value = toml::from_str(&fs::read_to_string(path).unwrap()).unwrap();

    let mut metadata = json::JsonValue::new_object();
    metadata
        .insert("version", config["package"]["version"].as_str().unwrap())
        .unwrap();

    fs::write(
        "metadata.js",
        format!("module.exports = {}", metadata.dump()),
    )
    .unwrap();
}
