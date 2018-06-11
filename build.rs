#[cfg(not(feature = "nolibsnark"))]
extern crate gcc;
#[cfg(not(feature = "nolibsnark"))]
extern crate cmake;

use std::path::Path;
use std::env;

fn main() {
    #[cfg(not(feature = "nolibsnark"))]
    {
        let libsnark_source_path_string = env::var_os("LIBSNARK_SOURCE_PATH").expect("$LIBSNARK_SOURCE_PATH not set");
        let libsnark_source_path = Path::new(&libsnark_source_path_string);

        let libsnark = cmake::Config::new(libsnark_source_path)
            .define("WITH_PROCPS", "OFF")
            .define("CURVE", "ALT_BN128")
            .define("USE_PT_COMPRESSION", "OFF")
            .define("MONTGOMERY_OUTPUT", "ON")
            .define("BINARY_OUTPUT", "ON")
            .build();

        gcc::Build::new()
            .cpp(true)
            .debug(cfg!(debug_assertions))
            .flag("-std=c++11")
            .include(libsnark_source_path)
            .include(libsnark_source_path.join("depends/libff"))
            .include(libsnark_source_path.join("depends/libfqfft"))
            .define("CURVE_ALT_BN128", None)
            .file("lib/wraplibsnark.cpp")
            .compile("libwraplibsnark.a");

        println!(
            "cargo:rustc-link-search=native={}",
            libsnark.join("lib").display()
        );

        println!("cargo:rustc-link-lib=gmp");
        println!("cargo:rustc-link-lib=gmpxx");

        #[cfg(debug_assertions)] {
            println!("cargo:rustc-link-lib=static=snarkd");
            println!("cargo:rustc-link-lib=static=ffd");
        }
        #[cfg(not(debug_assertions))] {
            println!("cargo:rustc-link-lib=static=snark");
            println!("cargo:rustc-link-lib=static=ff");
        }
    }
}
