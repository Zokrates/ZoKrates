use std::path::PathBuf;

pub trait Resolver<E> {
    fn resolve(
        &self,
        current_location: PathBuf,
        import_location: PathBuf,
    ) -> Result<(String, PathBuf), E>;
}
