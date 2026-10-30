pub mod ast;
pub mod lexer;
pub mod parser;

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct Location {
    pub start: usize,
    pub end: usize,
}

impl Location {
    pub const fn dummy() -> Self {
        Location { start: 0, end: 0 }
    }
}

impl Location {
    pub fn extract(self, source: &str) -> &str {
        &source[self.start..self.end]
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Error {
    pub location: Location,
    pub error: Box<str>,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.error)
    }
}
