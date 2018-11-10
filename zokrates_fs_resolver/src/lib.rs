use std::fs::File;
use std::io;
use std::io::BufReader;
use std::path::PathBuf;

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

    File::open(path).and_then(|f| Ok((BufReader::new(f), next_location, alias)))
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
}
