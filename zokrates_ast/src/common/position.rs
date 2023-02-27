use std::{
    collections::BTreeMap,
    fmt,
    path::{Path, PathBuf},
};

use serde::{Deserialize, Serialize};

#[derive(Clone, PartialEq, Eq, Copy, Hash, Default, PartialOrd, Ord, Deserialize, Serialize)]
pub struct LocalSpan {
    pub from: Position,
    pub to: Position,
}

pub type ModuleIdHash = u64;

pub type ModuleId = Path;

pub type OwnedModuleId = PathBuf;

#[derive(Clone, PartialEq, Debug, Eq, Hash, Default, PartialOrd, Ord, Deserialize, Serialize)]
pub struct ModuleMap {
    modules: BTreeMap<ModuleIdHash, OwnedModuleId>,
}

impl ModuleMap {
    pub fn new<I: IntoIterator<Item = OwnedModuleId>>(i: I) -> Self {
        Self {
            modules: i.into_iter().map(|id| (hash(&id), id)).collect(),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Copy, Hash, Default, PartialOrd, Ord, Deserialize, Serialize)]
pub struct Position {
    pub line: usize,
    pub col: usize,
}

#[derive(Clone, PartialEq, Eq, Copy, Hash, Default, PartialOrd, Ord, Deserialize, Serialize)]
pub struct Span {
    pub module: ModuleIdHash,
    pub from: Position,
    pub to: Position,
}

#[derive(Clone, PartialEq, Debug)]
pub struct ResolvedSpan {
    pub module: OwnedModuleId,
    pub from: Position,
    pub to: Position,
}

impl Span {
    pub fn resolve(self, map: &ModuleMap) -> ResolvedSpan {
        ResolvedSpan {
            module: map.modules.get(&self.module).cloned().unwrap(),
            from: self.from,
            to: self.to,
        }
    }
}

pub trait WithSpan: Sized {
    fn span(self, _: Option<Span>) -> Self;

    fn with_span(self, span: Span) -> Self {
        self.span(Some(span))
    }

    fn get_span(&self) -> Option<Span>;
}

fn hash(id: &ModuleId) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let mut hasher = DefaultHasher::new();
    id.hash(&mut hasher);
    hasher.finish()
}

impl LocalSpan {
    pub fn mock() -> Self {
        Self {
            from: Position::mock(),
            to: Position::mock(),
        }
    }

    pub fn in_module(self, module_id: &ModuleId) -> Span {
        Span {
            module: hash(module_id),
            from: self.from,
            to: self.to,
        }
    }
}

impl Position {
    pub fn col(&self, delta: isize) -> Position {
        assert!(self.col <= isize::max_value() as usize);
        assert!(self.col as isize >= delta);
        Position {
            line: self.line,
            col: (self.col as isize + delta) as usize,
        }
    }

    pub fn mock() -> Self {
        Position { line: 42, col: 42 }
    }
}
impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}
impl fmt::Debug for Position {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.from)
    }
}
impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl fmt::Display for ResolvedSpan {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}:{} (until {})",
            self.module.display(),
            self.from,
            self.to
        )
    }
}

#[test]
fn position_col() {
    let pos = Position {
        line: 100,
        col: 258,
    };
    assert_eq!(
        pos.col(26),
        Position {
            line: 100,
            col: 284,
        }
    );
    assert_eq!(
        pos.col(-23),
        Position {
            line: 100,
            col: 235,
        }
    );
}
