pub mod constants;
pub mod helpers;

use serde::{Deserialize, Serialize};
use std::path::PathBuf;

pub trait Resolver<E> {
    fn resolve(
        &self,
        current_location: PathBuf,
        import_location: PathBuf,
    ) -> Result<(String, PathBuf), E>;
}

#[derive(Debug, Default, Serialize, Deserialize, Clone, Copy)]
pub struct CompileConfig {
    #[serde(default)]
    pub debug: bool,
}

impl CompileConfig {
    pub fn debug(mut self, debug: bool) -> Self {
        self.debug = debug;
        self
    }
}
