#[cfg(feature = "libsnark")]
extern crate cc;
#[cfg(feature = "libsnark")]
extern crate cmake;
#[cfg(feature = "libsnark")]
extern crate git2;

fn main() {
    #[cfg(feature = "libsnark")]
    {
        use git2::{Oid, Repository, ResetType};
        use std::env;
        use std::fs::remove_dir;
        use std::path::PathBuf;

        // fetch libsnark source
        const LIBSNARK_URL: &'static str = "https://github.com/scipr-lab/libsnark.git";
        const LIBSNARK_COMMIT: &'static str = "f7c87b88744ecfd008126d415494d9b34c4c1b20";

        let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
        let libsnark_source_path = &out_path.join("libsnark");

        let repo = Repository::open(libsnark_source_path).unwrap_or_else(|_| {
            remove_dir(libsnark_source_path).ok();
            Repository::clone(LIBSNARK_URL, libsnark_source_path).unwrap()
        });

        let commit = Oid::from_str(LIBSNARK_COMMIT).unwrap();
        let commit = repo.find_commit(commit).unwrap();

        repo.reset(&commit.as_object(), ResetType::Hard, None)
            .unwrap();

        for mut s in repo.submodules().unwrap() {
            s.update(true, None).unwrap();
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
