use std::io::{BufReader};
use std::path::PathBuf;
use std::fs::File;
use std::io;

pub fn resolve(source: &PathBuf) -> Result<BufReader<File>, io::Error> {
	File::open(source).and_then(|f| Ok(BufReader::new(f)))
}