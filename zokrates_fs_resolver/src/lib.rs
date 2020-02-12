use std::fs::read_to_string;
use std::io;

use std::path::Path;
use std::path::{Component, PathBuf};

const ZOKRATES_HOME: &str = &"ZOKRATES_HOME";

type CurrentLocation = String;
type ImportLocation<'a> = String;
type SourceCode = String;

pub fn resolve<'a>(
    current_location: CurrentLocation,
    import_location: ImportLocation<'a>,
) -> Result<(SourceCode, CurrentLocation), io::Error> {

    println!("get file {} {}", current_location, import_location);

    let source = Path::new(&import_location);

    // paths starting with `./` or `../` are interpreted relative to the current file
    // other paths `abc/def` are interpreted relative to $ZOKRATES_HOME
    let base = match source.components().next() {
        Some(Component::CurDir) | Some(Component::ParentDir) => PathBuf::from(current_location).parent().unwrap().into(),
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

    let next_location = generate_next_location(&path_owned)?;
    let source = read_to_string(path_owned)?;

    Ok((source, next_location))
}

fn generate_next_location<'a>(path: &'a PathBuf) -> Result<String, io::Error> {
    Ok(path.to_path_buf().into_os_string().into_string().unwrap())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::File;

    #[test]
    fn valid_path() {
        use std::io::Write;

        // create a source folder with a zok file
        let folder = tempfile::tempdir().unwrap();
        let file_path = folder.path().join("bar.zok");
        let mut file = File::create(file_path).unwrap();
        writeln!(file, "some code").unwrap();
        let (_, next_location) =
            resolve(folder.path().to_str().unwrap().to_string(), "./bar".into()).unwrap();
        assert_eq!(next_location, folder.path().to_str().unwrap().to_string());
    }

    #[test]
    fn non_existing_file() {
        let res = resolve(String::from("./src"), "./rubbish".into());
        assert!(res.is_err());
    }

    #[test]
    fn invalid_location() {
        let res = resolve(String::from(",8!-$2abc"), "./foo".into());
        assert!(res.is_err());
    }

    #[test]
    fn not_a_file() {
        let res = resolve(String::from("."), "./src/".into());
        assert!(res.is_err());
    }

    #[test]
    fn no_parent() {
        let res = resolve(String::from("."), ".".into());
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
        let mut file = File::create(file_path).unwrap();
        writeln!(file, "<user code>").unwrap();

        // assign HOME folder to ZOKRATES_HOME
        std::env::set_var(ZOKRATES_HOME, zokrates_home_folder.path());

        let result = resolve(
            source_folder
                .path()
                .to_path_buf()
                .to_string_lossy()
                .to_string(),
            "./bar.zok".into(),
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
            source_folder
                .path()
                .to_path_buf()
                .to_string_lossy()
                .to_string(),
            "bar.zok".into(),
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
        let file_path = source_folder.path().join("bar.zok");
        let mut file = File::create(file_path).unwrap();
        writeln!(file, "<user code>").unwrap();

        let result = resolve(
            source_subfolder
                .path()
                .to_path_buf()
                .to_string_lossy()
                .to_string(),
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

        let result = resolve("/path/to/user/folder".to_string(), "./bar.zok".into());
        assert!(result.is_err());
    }

    #[test]
    fn fail_if_not_found_in_std() {
        std::env::set_var(ZOKRATES_HOME, "");
        let result = resolve("/path/to/source".to_string(), "bar.zok".into());
        assert!(result.is_err());
    }

    #[test]
    #[should_panic]
    fn panic_if_home_not_set() {
        std::env::remove_var(ZOKRATES_HOME);
        let _ = resolve("/path/to/source".to_string(), "bar.zok".into());
    }
}
