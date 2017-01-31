extern crate gcc;

fn main() {
    println!("cargo:rustc-link-search=lib/libsnark/lib");
    gcc::Config::new()
        .cpp(true)
        .include("lib/libsnark/include")
        .include("lib/libsnark/include/libsnark")
        .flag("-std=c++11")
        // .define("CURVE", Some("ALT_BN128"))
        .define("CURVE_BN128", None)
        .file("lib/wraplibsnark.cpp")
        .compile("libwraplibsnark.a");
}
