use std::fs::File;
use std::io;
use std::io::BufReader;
use std::path::PathBuf;

const ZOKRATES_HOME: &str = &"ZOKRATES_HOME";

pub fn resolve(
    location: &Option<String>,
    source: &String,
) -> Result<(BufReader<File>, String, String), io::Error> {
    // the fs resolver has to be provided a location, as it supports relative paths
    match location {
        Some(location) => resolve_with_location(location, source),
        None => Err(io::Error::new(io::ErrorKind::Other, "No location provided")),
    }
}

fn resolve_with_location(
    location: &String,
    source: &String,
) -> Result<(BufReader<File>, String, String), io::Error> {
    let path = PathBuf::from(location).join(PathBuf::from(source));
    let (next_location, alias) = generate_next_parameters(&path)?;

    match File::open(path) {
        Ok(f) => Ok((BufReader::new(f), next_location, alias)),
        Err(e) => match e.kind() {
            io::ErrorKind::NotFound => match std::env::var(ZOKRATES_HOME) {
                Ok(v) => {
                    let path = PathBuf::from(v).join(PathBuf::from(source));
                    let (next_location, alias) = generate_next_parameters(&path)?;
                    File::open(path).and_then(|f| Ok((BufReader::new(f), next_location, alias)))
                }
                Err(_) => Err(e),
            },
            _ => Err(e),
        },
    }
}

fn generate_next_parameters(path: &PathBuf) -> Result<(String, String), io::Error> {
    match (path.parent(), path.file_stem()) {
        (Some(parent), Some(stem)) => Ok((
            parent.to_path_buf().into_os_string().into_string().unwrap(),
            stem.to_os_string().to_string_lossy().to_string(),
        )),
        _ => Err(io::Error::new(io::ErrorKind::Other, "Invalid path")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn valid_path_with_location() {
        let (_, next_location, alias) =
            resolve(&Some(String::from("./src")), &String::from("lib.rs")).unwrap();
        assert_eq!(next_location, String::from("./src"));
        assert_eq!(alias, String::from("lib"));
    }

    #[test]
    fn valid_path_without_location() {
        let res = resolve(&None, &String::from("./src/lib.rs"));
        assert!(res.is_err());
    }

    #[test]
    fn non_existing_file() {
        let res = resolve(&Some(String::from("./src")), &String::from("rubbish.rs"));
        assert!(res.is_err());
    }

    #[test]
    fn invalid_location() {
        let res = resolve(&Some(String::from(",8!-$2abc")), &String::from("foo.code"));
        assert!(res.is_err());
    }

    #[test]
    fn invalid_file() {
        let res = resolve(&Some(String::from("./src")), &String::from(",8!-$2abc"));
        assert!(res.is_err());
    }

    #[test]
    fn not_a_file() {
        let res = resolve(&Some(String::from(".")), &String::from("/src/"));
        assert!(res.is_err());
    }

    #[test]
    fn no_parent() {
        let res = resolve(&Some(String::from(".")), &String::from("."));
        assert!(res.is_err());
    }

    #[test]
    fn no_file_name() {
        let res = resolve(&Some(String::from(".")), &String::from(""));
        assert!(res.is_err());
    }

    #[test]
    fn default_to_local() {
        use std::io::BufRead;
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
            &Some(
                source_folder
                    .path()
                    .to_path_buf()
                    .to_string_lossy()
                    .to_string(),
            ),
            &"bar.code".to_string(),
        );
        assert!(result.is_ok());
        let mut code = String::new();
        result.unwrap().0.read_line(&mut code).unwrap();
        // the imported file should be the user's
        assert_eq!(code, "<user code>\n".to_string());
    }

    #[test]
    fn fallback_to_std() {
        use std::io::BufRead;
        use std::io::Write;

        // create a HOME folder
        let zokrates_home_folder = tempfile::tempdir().unwrap();
        let file_path = zokrates_home_folder.path().join("bar.code");
        let mut file = File::create(file_path).unwrap();
        writeln!(file, "<stdlib code>").unwrap();

        // assign HOME folder to ZOKRATES_HOME
        std::env::set_var(ZOKRATES_HOME, zokrates_home_folder.path());

        let result = resolve(
            &Some("/path/to/user/folder".to_string()),
            &"bar.code".to_string(),
        );
        assert!(result.is_ok());
        let mut code = String::new();
        result.unwrap().0.read_line(&mut code).unwrap();
        // the imported file should be the one in $ZOKRATES_HOME
        assert_eq!(code, "<stdlib code>\n".to_string());
    }

    #[test]
    fn fail_if_no_std() {
        std::env::set_var(ZOKRATES_HOME, "");
        let result = resolve(
            &Some("/path/to/source".to_string()),
            &"bar.code".to_string(),
        );
        assert!(result.is_err());
    }
}
