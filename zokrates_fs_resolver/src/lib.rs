use std::fs::File;
use std::io;
use std::io::BufReader;
use std::path::Path;
use std::path::{Component, PathBuf};

const ZOKRATES_HOME: &str = &"ZOKRATES_HOME";

pub fn resolve<'a>(
    location: Option<String>,
    source: &'a str,
) -> Result<(BufReader<File>, String, &'a str), io::Error> {
    // the fs resolver has to be provided a location, as it supports relative paths
    match location {
        Some(location) => resolve_with_location(location, source),
        None => Err(io::Error::new(io::ErrorKind::Other, "No location provided")),
    }
}

fn resolve_with_location<'a>(
    location: String,
    source: &'a str,
) -> Result<(BufReader<File>, String, &'a str), io::Error> {
    let source = Path::new(source);

    // paths starting with `./` or `../` are interpreted relative to the current file
    // other paths `abc/def` are interpreted relative to $ZOKRATES_HOME
    let base = match source.components().next() {
        Some(Component::CurDir) | Some(Component::ParentDir) => PathBuf::from(location),
        _ => PathBuf::from(
            std::env::var(ZOKRATES_HOME).expect("$ZOKRATES_HOME is not set, please set it"),
        ),
    };

    let path_owned = base.join(PathBuf::from(source)).with_extension("zok");

    if path_owned.is_dir() {
        return Err(io::Error::new(io::ErrorKind::Other, "Not a file"));
    }

    let alias = generate_alias(source);
    let next_location = generate_next_location(&path_owned)?;

    File::open(path_owned).and_then(|f| Ok((BufReader::new(f), next_location, alias)))
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

    #[test]
    fn valid_path_with_location() {
        use std::io::Write;

        // create a source folder with a zok file
        let folder = tempfile::tempdir().unwrap();
        let file_path = folder.path().join("bar.zok");
        let mut file = File::create(file_path).unwrap();
        writeln!(file, "some code").unwrap();
        let (_, next_location, alias) =
            resolve(Some(folder.path().to_str().unwrap().to_string()), &"./bar").unwrap();
        assert_eq!(next_location, folder.path().to_str().unwrap().to_string());
        assert_eq!(alias, String::from("bar"));
    }

    #[test]
    fn valid_path_without_location() {
        let res = resolve(None, &"./src/lib.rs");
        assert!(res.is_err());
    }

    #[test]
    fn non_existing_file() {
        let res = resolve(Some(String::from("./src")), &"./rubbish");
        assert!(res.is_err());
    }

    #[test]
    fn invalid_location() {
        let res = resolve(Some(String::from(",8!-$2abc")), &"./foo.zok");
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
    fn treat_relative_as_local() {
        use std::io::BufRead;
        use std::io::Write;

        // create a HOME folder with a code file
        let zokrates_home_folder = tempfile::tempdir().unwrap();
        let file_path = zokrates_home_folder.path().join("bar.zok");
        let mut file = File::create(file_path).unwrap();
        writeln!(file, "<stdlib code>").unwrap();

        // create a user folder with a code file
        let source_folder = tempfile::tempdir().unwrap();
        let file_path = source_folder.path().join("bar.zok");
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
            &"./bar.zok",
        );
        assert!(result.is_ok());
        let mut code = String::new();
        result.unwrap().0.read_line(&mut code).unwrap();
        // the imported file should be the user's
        assert_eq!(code, "<user code>\n".to_string());
    }

    #[test]
    fn treat_absolute_as_std() {
        use std::io::BufRead;
        use std::io::Write;

        // create a HOME folder with a code file
        let zokrates_home_folder = tempfile::tempdir().unwrap();
        let file_path = zokrates_home_folder.path().join("bar.zok");
        let mut file = File::create(file_path).unwrap();
        writeln!(file, "<stdlib code>").unwrap();

        // create a user folder with a code file
        let source_folder = tempfile::tempdir().unwrap();
        let file_path = source_folder.path().join("bar.zok");
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
            &"bar.zok",
        );
        assert!(result.is_ok());
        let mut code = String::new();
        result.unwrap().0.read_line(&mut code).unwrap();
        // the imported file should be the user's
        assert_eq!(code, "<stdlib code>\n".to_string());
    }

    #[test]
    fn navigate_up() {
        use std::io::BufRead;
        use std::io::Write;

        // create a user folder with a code file
        let source_folder = tempfile::tempdir().unwrap();
        let source_subfolder = tempfile::tempdir_in(&source_folder).unwrap();
        let file_path = source_folder.path().join("bar.zok");
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
            &"../bar.zok",
        );
        assert!(result.is_ok());
        let mut code = String::new();
        result.unwrap().0.read_line(&mut code).unwrap();
        // the imported file should be the user's
        assert_eq!(code, "<user code>\n".to_string());
    }

    #[test]
    fn dont_fallback_to_std() {
        use std::io::Write;

        // create a HOME folder
        let zokrates_home_folder = tempfile::tempdir().unwrap();
        let file_path = zokrates_home_folder.path().join("bar.zok");
        let mut file = File::create(file_path).unwrap();
        writeln!(file, "<stdlib code>").unwrap();

        // assign HOME folder to ZOKRATES_HOME
        std::env::set_var(ZOKRATES_HOME, zokrates_home_folder.path());

        let result = resolve(Some("/path/to/user/folder".to_string()), &"./bar.zok");
        assert!(result.is_err());
    }

    #[test]
    fn fail_if_not_found_in_std() {
        std::env::set_var(ZOKRATES_HOME, "");
        let result = resolve(Some("/path/to/source".to_string()), &"bar.zok");
        assert!(result.is_err());
    }

    #[test]
    #[should_panic]
    fn panic_if_home_not_set() {
        std::env::remove_var(ZOKRATES_HOME);
        let _ = resolve(Some("/path/to/source".to_string()), &"bar.zok");
    }
}
