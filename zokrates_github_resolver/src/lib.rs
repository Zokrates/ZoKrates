//! # GitHub import resolver
//!
//! GitHub import resolver allows to import files located in github.com repos.
//!
//! To import file from github, use following syntax:
//! ```zokrates
//! import "github:user/repo/branch/path/to/file.code"
//! ```
//!
//! For example:
//! ```zokrates
//! import "github:eupn/test/master/examples/merkleTree/sha256PathProof3.code" as merkleTreeProof
//! ```
//!
//! Example above imports file `examples/merkleTree/sha256PathProof3.code` located at @eupn's `test`
//! repository's `master` branch by downloading from URL:
//! https://raw.githubusercontent.com/eupn/test/master/examples/merkleTree/sha256PathProof3.code
//!

use reqwest;
use std::fs::File;
use std::io::{self, copy, BufReader};
use std::path::PathBuf;
use tempfile::NamedTempFile;

/// Prefix for github import source to be distinguished.
const GITHUB_IMPORT_PREFIX: &str = "github:";

/// Resolves import from the Github.
/// This importer needs to be provided with location since relative paths could be used inside the
/// files that are imported from github.
pub fn resolve(
    location: &Option<String>,
    path: &String,
) -> Result<(BufReader<File>, String, String), io::Error> {
    if let Some(location) = location {
        let (root, repo, branch, path) = parse_input_path(&path)?;

        let pb = download_from_github(&root, &repo, &branch, &path).unwrap();
        let file = File::open(&pb)?;
        let br = BufReader::new(file);

        let alias = PathBuf::from(path.clone())
            .as_path()
            .file_stem()
            .unwrap()
            .to_string_lossy()
            .to_string();

        Ok((br, location.to_owned(), alias))
    } else {
        Err(io::Error::new(io::ErrorKind::Other, "No location provided"))
    }
}

/// Checks that import source is using github import location.
pub fn is_github_import(source: &str) -> bool {
    source.starts_with(GITHUB_IMPORT_PREFIX)
}

/// Parses github import syntax: "github:<root>/<repo>/<branch>/<path/to/file>"
/// Where:
/// - <root> is the user or organization name
/// - <repo> is the repository name
/// - <branch> is the branch/snapshot name, e.g. `master`
/// - <path/to/file> is the absolute path to file in the specified branch of the repository
fn parse_input_path(path: &str) -> Result<(String, String, String, String), io::Error> {
    let path = path.replacen("github:", "", 1);
    if path.contains("..") {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "Invalid github import syntax. It must not contain '..'",
        ));
    }

    let components = path.split("/").collect::<Vec<_>>();

    // Check that root, repo, branch & path are specified
    if components.len() < 4 {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            "Invalid github import syntax. Should be: github:<root>/<repo>/<branch>/<path>",
        ));
    }

    let root = components[0];
    let repo = components[1];
    let branch = components[2];
    let path = components[3..].join("/"); // Collect the rest of the import path into single string

    Ok((
        root.to_owned(),
        repo.to_owned(),
        branch.to_owned(),
        path.to_owned(),
    ))
}

/// Downloads the file from github by specific root (user/org), repository, branch and path.
fn download_from_github(
    root: &str,
    repo: &str,
    branch: &str,
    path: &str,
) -> Result<PathBuf, io::Error> {
    let url = format!(
        "https://raw.githubusercontent.com/{root}/{repo}/{branch}/{path}",
        root = root,
        repo = repo,
        branch = branch,
        path = path
    );

    Ok(download_url(&url)?)
}

fn download_url(url: &str) -> Result<PathBuf, io::Error> {
    let mut response = reqwest::get(url).map_err(|e| {
        io::Error::new(
            io::ErrorKind::Other,
            format!("Unable to access github: {}", e.to_string()),
        )
    })?;

    let (mut dest, pb) = NamedTempFile::new()?.keep()?;
    copy(&mut response, &mut dest)?;

    Ok(pb)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn import_simple() {
        let res = parse_input_path("github:eupn/test/master/examples/imports.code").unwrap();
        let (root, repo, branch, path) = res;

        assert_eq!(root, "eupn");
        assert_eq!(repo, "test");
        assert_eq!(branch, "master");
        assert_eq!(path, "examples/imports.code");
    }

    #[test]
    #[should_panic]
    pub fn import_no_branch() {
        // Correct syntax should be: github:eupn/test/master/imports.code
        // but branch name is not specified
        parse_input_path("github:eupn/test/imports.code").unwrap();
    }

    #[test]
    #[should_panic]
    pub fn import_relative_paths() {
        // Relative paths should not be allowed
        parse_input_path("github:eupn/test/master/examples/../imports.code").unwrap();
    }
}
