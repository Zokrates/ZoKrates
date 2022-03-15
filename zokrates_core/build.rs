#[cfg(feature = "libsnark")]
extern crate cc;
#[cfg(feature = "libsnark")]
extern crate cmake;

fn main() {
    #[cfg(feature = "libsnark")]
    {
        use std::env;
        use std::path::PathBuf;
        use std::process::Command;

        // fetch libsnark source
        const LIBSNARK_URL: &'static str = "https://github.com/scipr-lab/libsnark.git";
        const LIBSNARK_COMMIT: &'static str = "f7c87b88744ecfd008126d415494d9b34c4c1b20";

        let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
        let libsnark_source_path = &out_path.join("libsnark");

        if !libsnark_source_path.exists() {
            // Clone the repository
            let _ = Command::new("git")
                .current_dir(out_path)
                .args(&["clone", "--no-checkout", LIBSNARK_URL])
                .status()
                .unwrap();

            // Checkout the specific commit
            let _ = Command::new("git")
                .current_dir(libsnark_source_path)
                .args(&["checkout", "-f", LIBSNARK_COMMIT])
                .status()
                .unwrap();

            // Unencrypted `git://` protocol is no longer supported on GitHub
            // so we replace all submodule urls to use `https://`
            let gitmodules_path = libsnark_source_path.join(".gitmodules");
            let gitmodules = std::fs::read_to_string(&gitmodules_path)
                .unwrap()
                .replace("git://", "https://");

            std::fs::write(&gitmodules_path, gitmodules).unwrap();

            // Update all submodules recursively
            let _ = Command::new("git")
                .current_dir(libsnark_source_path)
                .args(&["submodule", "update", "--init", "--recursive"])
                .status()
                .unwrap();
        }

        // build libsnark
        let libsnark = cmake::Config::new(libsnark_source_path)
            .define("WITH_SUPERCOP", "OFF")
            .define("WITH_PROCPS", "OFF")
            .define("WITH_SUPERCOP", "OFF")
            .define("CURVE", "ALT_BN128")
            .define("USE_PT_COMPRESSION", "OFF")
            .define("MONTGOMERY_OUTPUT", "ON")
            .define("BINARY_OUTPUT", "ON")
            .define("DMULTICORE", "ON")
            .build();

        // build backends
        cc::Build::new()
            .cpp(true)
            .debug(cfg!(debug_assertions))
            .flag("-std=c++11")
            .include(libsnark_source_path)
            .include(libsnark_source_path.join("depends/libff"))
            .include(libsnark_source_path.join("depends/libfqfft"))
            .define("CURVE_ALT_BN128", None)
            .file("lib/ffi.cpp")
            .file("lib/gm17.cpp")
            .file("lib/pghr13.cpp")
            .compile("libsnark_wrapper.a");

        println!(
            "cargo:rustc-link-search=native={}",
            libsnark.join("lib").display()
        );

        println!("cargo:rustc-link-lib=gmp");
        println!("cargo:rustc-link-lib=gmpxx");

        #[cfg(debug_assertions)]
        {
            println!("cargo:rustc-link-lib=static=snarkd");
            println!("cargo:rustc-link-lib=static=ffd");
        }
        #[cfg(not(debug_assertions))]
        {
            println!("cargo:rustc-link-lib=static=snark");
            println!("cargo:rustc-link-lib=static=ff");
        }
    }
}
