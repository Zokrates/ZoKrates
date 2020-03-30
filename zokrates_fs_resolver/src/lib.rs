use std::fs::read_to_string;
use std::io;

use std::path::Path;
use std::path::{Component, PathBuf};
use zokrates_common::Resolver;

const ZOKRATES_HOME: &str = &"ZOKRATES_HOME";

pub struct FileSystemResolver;

impl FileSystemResolver {
    pub fn new() -> Self {
        FileSystemResolver {}
    }
}

impl Resolver<io::Error> for FileSystemResolver {
    fn resolve(
        &self,
        current_location: PathBuf,
        import_location: PathBuf,
    ) -> Result<(String, PathBuf), io::Error> {
        let source = Path::new(&import_location);

        if !current_location.is_file() {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                format!("{} was expected to be a file", current_location.display()),
            ));
        }

        // paths starting with `./` or `../` are interpreted relative to the current file
        // other paths `abc/def` are interpreted relative to $ZOKRATES_HOME
        let base = match source.components().next() {
            Some(Component::CurDir) | Some(Component::ParentDir) => {
                Ok(PathBuf::from(current_location).parent().unwrap().into())
            }
            _ => std::env::var(ZOKRATES_HOME)
                .map_err(|_| {
                    io::Error::new(
                        io::ErrorKind::Other,
                        "$ZOKRATES_HOME is not set, please set it",
                    )
                })
                .map(PathBuf::from),
        }?;

        let path_owned = base
            .join(PathBuf::from(import_location.clone()))
            .with_extension("zok");

        if !path_owned.is_file() {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                format!("No file found at {}", import_location.display()),
            ));
        }

        let source = read_to_string(&path_owned)?;
        Ok((source, path_owned))
    }
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

        let fs_resolver = FileSystemResolver::new();
        let (_, next_location) = fs_resolver
            .resolve(file_path.clone(), "./bar.zok".into())
            .unwrap();
        assert_eq!(next_location, file_path);
    }

    #[test]
    fn non_existing_file() {
        let fs_resolver = FileSystemResolver::new();
        let res = fs_resolver.resolve("./source.zok".into(), "./rubbish".into());
        assert!(res.is_err());
    }

    #[test]
    fn invalid_location() {
        let fs_resolver = FileSystemResolver::new();
        let res = fs_resolver.resolve(",8!-$2abc".into(), "./foo".into());
        assert!(res.is_err());
    }

    #[test]
    fn not_a_file() {
        // create a source folder with a zok file
        let folder = tempfile::tempdir().unwrap();
        let dir_path = folder.path().join("dir");
        std::fs::create_dir(dir_path.clone()).unwrap();

        let fs_resolver = FileSystemResolver::new();
        let res = fs_resolver.resolve(".".into(), "./dir/".into());
        assert!(res.is_err());
    }

    #[test]
    fn no_parent() {
        // create a source folder with a zok file
        let folder = tempfile::tempdir().unwrap();
        let file_path = folder.path().join("foo.zok");
        File::create(file_path.clone()).unwrap();

        let fs_resolver = FileSystemResolver::new();
        let res = fs_resolver.resolve(file_path, ".".into());
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

        let fs_resolver = FileSystemResolver::new();
        let result = fs_resolver.resolve(file_path, "./bar.zok".into());
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

        let fs_resolver = FileSystemResolver::new();
        let result = fs_resolver.resolve(file_path.clone(), "bar.zok".into());
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
        let origin_path = source_subfolder.path().join("foo.zok");
        File::create(origin_path).unwrap();

        let fs_resolver = FileSystemResolver::new();
        let result = fs_resolver.resolve(
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

        let fs_resolver = FileSystemResolver::new();
        let result = fs_resolver.resolve("/path/to/source.zok".into(), "./bar.zok".into());
        assert!(result.is_err());
    }

    #[test]
    fn fail_if_not_found_in_std() {
        std::env::set_var(ZOKRATES_HOME, "");
        let fs_resolver = FileSystemResolver::new();
        let result = fs_resolver.resolve("/path/to/source.zok".into(), "bar.zok".into());
        assert!(result.is_err());
    }

    #[test]
    fn panic_if_home_not_set() {
        std::env::remove_var(ZOKRATES_HOME);
        let fs_resolver = FileSystemResolver::new();
        let result = fs_resolver.resolve("/path/to/source.zok".into(), "bar.zok".into());
        assert!(result.is_err());
    }
}
