#[cfg(not(feature = "nolibsnark"))]
extern crate gcc;

fn main() {
    #[cfg(not(feature = "nolibsnark"))]
    {
        gcc::Build::new()
            .cpp(true)
            .debug(true)
            //.include("/usr/local/include")
            .include("./depends/libsnark")
            .include("./depends/libsnark/depends/libff")
            .include("./depends/libsnark/depends/libfqfft")

            //.include("/usr/local/include/libsnark")
            .warnings(false)
            .flag("-std=c++11")
            .define("CURVE_ALT_BN128", None)
            .file("lib/wraplibsnark.cpp")
            .compile("libwraplibsnark.a");

        gcc::Build::new()
            .cpp(true)
            .debug(true)
            //.include("/usr/local/include")
            .include("./depends/libsnark")
            .include("./depends/libsnark/depends/libff")
            .include("./depends/libsnark/depends/libfqfft")

            //.include("/usr/local/include/libsnark")
            .warnings(false)
            .flag("-std=c++11")
            .define("CURVE_ALT_BN128", None)
            .file("lib/wraplibsnarkgadgets.cpp")
            .compile("libwraplibsnarkgadgets.a");

        println!("cargo:rustc-link-lib=gmp");
        println!("cargo:rustc-link-lib=gmpxx");
        println!("cargo:rustc-link-lib=supercop");
        println!("cargo:rustc-link-lib=snark");
        println!("cargo:rustc-link-lib=wraplibsnarkgadgets");
        println!("cargo:rustc-link-search=/usr/local/lib");
    }
}
