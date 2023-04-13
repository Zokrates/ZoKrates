use std::{
    collections::BTreeMap,
    fmt,
    path::{Path, PathBuf},
};

use serde::{Deserialize, Serialize};

use super::FlatEmbed;

#[derive(Clone, PartialEq, Eq, Copy, Hash, Default, PartialOrd, Ord, Deserialize, Serialize)]
pub struct LocalSourceSpan {
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

    pub fn remap_prefix(self, prefix: &Path, to: &Path) -> Self {
        Self {
            modules: self
                .modules
                .into_iter()
                .map(|(id, path)| {
                    (
                        id,
                        path.strip_prefix(prefix)
                            .map(|path| to.join(path))
                            .unwrap_or(path),
                    )
                })
                .collect(),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Copy, Hash, Default, PartialOrd, Ord, Deserialize, Serialize)]
pub struct Position {
    pub line: usize,
    pub col: usize,
}

#[derive(Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord, Deserialize, Serialize, Debug)]
pub enum Span {
    Source(SourceSpan),
    Embed(FlatEmbed),
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Span::Source(s) => write!(f, "{}", s),
            Span::Embed(e) => write!(f, "{:?}", e),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ResolvedSpan {
    Source(ResolvedSourceSpan),
    Embed(FlatEmbed),
}

impl fmt::Display for ResolvedSpan {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ResolvedSpan::Source(s) => write!(f, "{}", s),
            ResolvedSpan::Embed(e) => write!(f, "{:?}", e),
        }
    }
}

impl Span {
    pub fn resolve(self, map: &ModuleMap) -> ResolvedSpan {
        match self {
            Span::Source(s) => ResolvedSpan::Source(ResolvedSourceSpan {
                module: map.modules.get(&s.module).cloned().unwrap(),
                from: s.from,
                to: s.to,
            }),
            Span::Embed(s) => ResolvedSpan::Embed(s),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Copy, Hash, Default, PartialOrd, Ord, Deserialize, Serialize)]
pub struct SourceSpan {
    pub module: ModuleIdHash,
    pub from: Position,
    pub to: Position,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ResolvedSourceSpan {
    pub module: OwnedModuleId,
    pub from: Position,
    pub to: Position,
}

impl From<SourceSpan> for Span {
    fn from(span: SourceSpan) -> Self {
        Self::Source(span)
    }
}

impl From<FlatEmbed> for Span {
    fn from(embed: FlatEmbed) -> Self {
        Self::Embed(embed)
    }
}

impl SourceSpan {
    pub fn mock() -> Self {
        Self {
            module: hash(&OwnedModuleId::default()),
            from: Position::mock(),
            to: Position::mock(),
        }
    }
}

pub trait WithSpan: Sized {
    fn span(self, _: Option<Span>) -> Self;

    fn with_span<S: Into<Span>>(self, span: S) -> Self {
        self.span(Some(span.into()))
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

impl LocalSourceSpan {
    pub fn in_module(self, module_id: &ModuleId) -> SourceSpan {
        SourceSpan {
            module: hash(module_id),
            from: self.from,
            to: self.to,
        }
    }

    pub fn mock() -> Self {
        Self {
            from: Position::mock(),
            to: Position::mock(),
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

impl fmt::Display for SourceSpan {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.from)
    }
}
impl fmt::Debug for SourceSpan {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl fmt::Display for ResolvedSourceSpan {
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
