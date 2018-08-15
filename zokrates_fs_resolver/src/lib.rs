use std::io::{BufReader};
use std::path::PathBuf;
use std::fs::File;
use std::io;

pub fn resolve(location: &Option<String>, source: &String) -> Result<(BufReader<File>, String, String), io::Error> {
	let path = match location {
		Some(location) => {
			PathBuf::from(location).join(PathBuf::from(source))
		},
		None => {
			PathBuf::from(source)
		}
	};

	let next_location = path.parent().unwrap().to_path_buf().into_os_string().into_string().unwrap();
	let alias = path.file_stem().unwrap().to_os_string().to_string_lossy().to_string();

	File::open(path).and_then(|f| Ok((BufReader::new(f), next_location, alias)))
}