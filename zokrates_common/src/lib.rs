use std::path::PathBuf;

pub trait Resolver<E> {
    // Requirement: the returned PathBuf must be canonical
    fn resolve(
        &self,
        current_location: PathBuf,
        import_location: PathBuf,
    ) -> Result<(String, PathBuf), E>;
}
