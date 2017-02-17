#[cfg(not(feature="nolibsnark"))]
extern crate gcc;

fn main() {
    #[cfg(not(feature="nolibsnark"))]
    {
        println!("cargo:rustc-link-search=/usr/local/lib");
        gcc::Config::new()
            .cpp(true)
            .include("/usr/local/include")
            .include("/usr/local/include/libsnark")
            .flag("-std=c++11")
            .define("CURVE_ALT_BN128", None)
            .file("lib/wraplibsnark.cpp")
            .compile("libwraplibsnark.a");
    }
}
