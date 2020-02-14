use std::fs::read_to_string;
use std::io;

use std::path::Path;
use std::path::{Component, PathBuf};

const ZOKRATES_HOME: &str = &"ZOKRATES_HOME";

// path to the current file we're importing into
type CurrentLocation = PathBuf;
// path we're importing from
type ImportLocation<'a> = PathBuf;
type SourceCode = String;

pub fn resolve<'a>(
    current_location: CurrentLocation,
    import_location: ImportLocation<'a>,
) -> Result<(SourceCode, CurrentLocation), io::Error> {
    let source = Path::new(&import_location);

    // paths starting with `./` or `../` are interpreted relative to the current file
    // other paths `abc/def` are interpreted relative to $ZOKRATES_HOME
    let base = match source.components().next() {
        Some(Component::CurDir) | Some(Component::ParentDir) => {
            PathBuf::from(current_location).parent().unwrap().into()
        }
        _ => PathBuf::from(
            std::env::var(ZOKRATES_HOME).expect("$ZOKRATES_HOME is not set, please set it"),
        ),
    };

    let path_owned = base
        .join(PathBuf::from(import_location))
        .with_extension("zok");

    if path_owned.is_dir() {
        return Err(io::Error::new(io::ErrorKind::Other, "Not a file"));
    }

    let source = read_to_string(&path_owned)?;

    Ok((source, path_owned))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::File;

    #[test]
    fn valid_path() {
        // create a source folder with a zok file
        let folder = tempfile::tempdir().unwrap();
        let file_path = folder.path().join("bar.zok");
        File::create(file_path.clone()).unwrap();
        let (_, next_location) = resolve(file_path.clone(), "./bar.zok".into()).unwrap();
        assert_eq!(next_location, file_path);
    }

    #[test]
    fn non_existing_file() {
        let res = resolve("./source.zok".into(), "./rubbish".into());
        assert!(res.is_err());
    }

    #[test]
    fn invalid_location() {
        let res = resolve(",8!-$2abc".into(), "./foo".into());
        assert!(res.is_err());
    }

    #[test]
    fn not_a_file() {
        // create a source folder with a zok file
        let folder = tempfile::tempdir().unwrap();
        let dir_path = folder.path().join("dir");
        std::fs::create_dir(dir_path.clone()).unwrap();

        let res = resolve(".".into(), "./dir/".into());
        assert!(res.is_err());
    }

    #[test]
    fn no_parent() {
        // create a source folder with a zok file
        let folder = tempfile::tempdir().unwrap();
        let file_path = folder.path().join("foo.zok");
        File::create(file_path.clone()).unwrap();
        let res = resolve(file_path, ".".into());
        assert!(res.is_err());
    }

    #[test]
    fn treat_relative_as_local() {
        use std::io::Write;

        // create a HOME folder with a code file
        let zokrates_home_folder = tempfile::tempdir().unwrap();
        let file_path = zokrates_home_folder.path().join("bar.zok");
        let mut file = File::create(file_path).unwrap();
        writeln!(file, "<stdlib code>").unwrap();

        // create a user folder with a code file
        let source_folder = tempfile::tempdir().unwrap();
        let file_path = source_folder.path().join("bar.zok");
        let mut file = File::create(file_path.clone()).unwrap();
        writeln!(file, "<user code>").unwrap();

        // assign HOME folder to ZOKRATES_HOME
        std::env::set_var(ZOKRATES_HOME, zokrates_home_folder.path());

        let result = resolve(file_path, "./bar.zok".into());
        assert!(result.is_ok());
        // the imported file should be the user's
        assert_eq!(result.unwrap().0, String::from("<user code>\n"));
    }

    #[test]
    fn treat_absolute_as_std() {
        use std::io::Write;

        // create a HOME folder with a code file
        let zokrates_home_folder = tempfile::tempdir().unwrap();
        let file_path = zokrates_home_folder.path().join("bar.zok");
        let mut file = File::create(file_path).unwrap();
        writeln!(file, "<stdlib code>").unwrap();

        // create a user folder with a code file
        let source_folder = tempfile::tempdir().unwrap();
        let file_path = source_folder.path().join("bar.zok");
        let mut file = File::create(file_path.clone()).unwrap();
        writeln!(file, "<user code>").unwrap();

        // assign HOME folder to ZOKRATES_HOME
        std::env::set_var(ZOKRATES_HOME, zokrates_home_folder.path());

        let result = resolve(file_path.clone(), "bar.zok".into());
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
        let file_path = source_folder.path().join("bar.zok");
        let mut file = File::create(file_path).unwrap();
        writeln!(file, "<user code>").unwrap();

        let result = resolve(
            source_subfolder.path().to_path_buf().join("foo.zok"),
            "../bar.zok".into(),
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
        let file_path = zokrates_home_folder.path().join("bar.zok");
        let mut file = File::create(file_path).unwrap();
        writeln!(file, "<stdlib code>").unwrap();

        // assign HOME folder to ZOKRATES_HOME
        std::env::set_var(ZOKRATES_HOME, zokrates_home_folder.path());

        let result = resolve("/path/to/source.zok".into(), "./bar.zok".into());
        assert!(result.is_err());
    }

    #[test]
    fn fail_if_not_found_in_std() {
        std::env::set_var(ZOKRATES_HOME, "");
        let result = resolve("/path/to/source.zok".into(), "bar.zok".into());
        assert!(result.is_err());
    }

    #[test]
    #[should_panic]
    fn panic_if_home_not_set() {
        std::env::remove_var(ZOKRATES_HOME);
        let _ = resolve("/path/to/source.zok".into(), "bar.zok".into());
    }
}
