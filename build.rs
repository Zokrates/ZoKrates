#[cfg(not(feature = "nolibsnark"))]
extern crate gcc;

fn main() {
    #[cfg(not(feature = "nolibsnark"))]
    {
        gcc::Config::new()
            .cpp(true)
            .debug(true)
            .include("/usr/local/include")
            .include("/usr/local/include/libsnark")
            .flag("-std=c++11")
            .define("CURVE_ALT_BN128", None)
            .file("lib/wraplibsnark.cpp")
            .compile("libwraplibsnark.a");

        println!("cargo:rustc-link-lib=gmp");
        println!("cargo:rustc-link-lib=gmpxx");
        println!("cargo:rustc-link-lib=supercop");
        println!("cargo:rustc-link-lib=snark");
        println!("cargo:rustc-link-search=/usr/local/lib");
    }
}
