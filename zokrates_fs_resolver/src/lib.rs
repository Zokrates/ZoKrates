use std::fs::read_to_string;
use std::io;

use std::path::Path;
use std::path::{Component, PathBuf};

const ZOKRATES_HOME: &str = &"ZOKRATES_HOME";

pub fn resolve<'a>(
    location: Option<String>,
    source: &'a str,
) -> Result<(String, String, &'a str), io::Error> {
    // the fs resolver has to be provided a location, as it supports relative paths
    match location {
        Some(location) => resolve_with_location(location, source),
        None => Err(io::Error::new(io::ErrorKind::Other, "No location provided")),
    }
}

fn resolve_with_location<'a>(
    location: String,
    source: &'a str,
) -> Result<(String, String, &'a str), io::Error> {
    let source = Path::new(source);

    // paths starting with `./` or `../` are interpreted relative to the current file
    // other paths `abc/def.code` are interpreted relative to $ZOKRATES_HOME
    let base = match source.components().next() {
        Some(Component::CurDir) | Some(Component::ParentDir) => PathBuf::from(location),
        _ => PathBuf::from(
            std::env::var(ZOKRATES_HOME).expect("$ZOKRATES_HOME is not set, please set it"),
        ),
    };

    let path_owned = base.join(PathBuf::from(source));

    if path_owned.is_dir() {
        return Err(io::Error::new(io::ErrorKind::Other, "Not a file"));
    }

    let alias = generate_alias(source);
    let next_location = generate_next_location(&path_owned)?;
    let source = read_to_string(path_owned)?;

    Ok((source, next_location, alias))
}

fn generate_next_location<'a>(path: &'a PathBuf) -> Result<String, io::Error> {
    path.parent()
        .ok_or(io::Error::new(io::ErrorKind::Other, "Invalid path"))
        .map(|v| v.to_path_buf().into_os_string().into_string().unwrap())
}

fn generate_alias<'a>(path: &'a Path) -> &'a str {
    path.file_stem().unwrap().to_str().unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::File;

    #[test]
    fn valid_path_with_location() {
        let (_, next_location, alias) = resolve(Some(String::from("./src")), &"./lib.rs").unwrap();
        assert_eq!(next_location, String::from("./src"));
        assert_eq!(alias, String::from("lib"));
    }

    #[test]
    fn valid_path_without_location() {
        let res = resolve(None, &"./src/lib.rs");
        assert!(res.is_err());
    }

    #[test]
    fn non_existing_file() {
        let res = resolve(Some(String::from("./src")), &"./rubbish.rs");
        assert!(res.is_err());
    }

    #[test]
    fn invalid_location() {
        let res = resolve(Some(String::from(",8!-$2abc")), &"./foo.code");
        assert!(res.is_err());
    }

    #[test]
    fn not_a_file() {
        let res = resolve(Some(String::from(".")), &"./src/");
        assert!(res.is_err());
    }

    #[test]
    fn no_parent() {
        let res = resolve(Some(String::from(".")), &".");
        assert!(res.is_err());
    }

    #[test]
    #[should_panic]
    fn no_file_name_without_stdlib() {
        // an empty string is interpreted relative to the HOME folder. If there's none, panic
        std::env::remove_var(ZOKRATES_HOME);
        let _res = resolve(Some(String::from(".")), &"");
    }

    #[test]
    fn no_file_name_with_stdlib() {
        use std::io::Write;

        // create a HOME folder with a code file
        let zokrates_home_folder = tempfile::tempdir().unwrap();
        let file_path = zokrates_home_folder.path().join("bar.code");
        let mut file = File::create(file_path).unwrap();
        writeln!(file, "<stdlib code>").unwrap();

        // assign HOME folder to ZOKRATES_HOME
        std::env::set_var(ZOKRATES_HOME, zokrates_home_folder.path());

        let res = resolve(Some(String::from(".")), &"");
        assert!(res.is_err());
    }

    #[test]
    fn treat_relative_as_local() {
        use std::io::Write;

        // create a HOME folder with a code file
        let zokrates_home_folder = tempfile::tempdir().unwrap();
        let file_path = zokrates_home_folder.path().join("bar.code");
        let mut file = File::create(file_path).unwrap();
        writeln!(file, "<stdlib code>").unwrap();

        // create a user folder with a code file
        let source_folder = tempfile::tempdir().unwrap();
        let file_path = source_folder.path().join("bar.code");
        let mut file = File::create(file_path).unwrap();
        writeln!(file, "<user code>").unwrap();

        // assign HOME folder to ZOKRATES_HOME
        std::env::set_var(ZOKRATES_HOME, zokrates_home_folder.path());

        let result = resolve(
            Some(
                source_folder
                    .path()
                    .to_path_buf()
                    .to_string_lossy()
                    .to_string(),
            ),
            &"./bar.code",
        );
        assert!(result.is_ok());
        // the imported file should be the user's
        assert_eq!(result.unwrap().0, String::from("<user code>\n"));
    }

    #[test]
    fn treat_absolute_as_std() {
        use std::io::Write;

        // create a HOME folder with a code file
        let zokrates_home_folder = tempfile::tempdir().unwrap();
        let file_path = zokrates_home_folder.path().join("bar.code");
        let mut file = File::create(file_path).unwrap();
        writeln!(file, "<stdlib code>").unwrap();

        // create a user folder with a code file
        let source_folder = tempfile::tempdir().unwrap();
        let file_path = source_folder.path().join("bar.code");
        let mut file = File::create(file_path).unwrap();
        writeln!(file, "<user code>").unwrap();

        // assign HOME folder to ZOKRATES_HOME
        std::env::set_var(ZOKRATES_HOME, zokrates_home_folder.path());

        let result = resolve(
            Some(
                source_folder
                    .path()
                    .to_path_buf()
                    .to_string_lossy()
                    .to_string(),
            ),
            &"bar.code",
        );
        assert!(result.is_ok());
        // the imported file should be the user's
        assert_eq!(result.unwrap().0, String::from("<stdlib code>\n"));
    }

    #[test]
    fn navigate_up() {
        use std::io::Write;

        // create a user folder with a code file
        let source_folder = tempfile::tempdir().unwrap();
        let source_subfolder = tempfile::tempdir_in(&source_folder).unwrap();
        let file_path = source_folder.path().join("bar.code");
        let mut file = File::create(file_path).unwrap();
        writeln!(file, "<user code>").unwrap();

        let result = resolve(
            Some(
                source_subfolder
                    .path()
                    .to_path_buf()
                    .to_string_lossy()
                    .to_string(),
            ),
            &"../bar.code",
        );
        assert!(result.is_ok());
        // the imported file should be the user's
        assert_eq!(result.unwrap().0, String::from("<user code>\n"));
    }

    #[test]
    fn dont_fallback_to_std() {
        use std::io::Write;

        // create a HOME folder
        let zokrates_home_folder = tempfile::tempdir().unwrap();
        let file_path = zokrates_home_folder.path().join("bar.code");
        let mut file = File::create(file_path).unwrap();
        writeln!(file, "<stdlib code>").unwrap();

        // assign HOME folder to ZOKRATES_HOME
        std::env::set_var(ZOKRATES_HOME, zokrates_home_folder.path());

        let result = resolve(Some("/path/to/user/folder".to_string()), &"./bar.code");
        assert!(result.is_err());
    }

    #[test]
    fn fail_if_not_found_in_std() {
        std::env::set_var(ZOKRATES_HOME, "");
        let result = resolve(Some("/path/to/source".to_string()), &"bar.code");
        assert!(result.is_err());
    }

    #[test]
    #[should_panic]
    fn panic_if_home_not_set() {
        std::env::remove_var(ZOKRATES_HOME);
        let _ = resolve(Some("/path/to/source".to_string()), &"bar.code");
    }
}
