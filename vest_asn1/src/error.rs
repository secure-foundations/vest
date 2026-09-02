use std::fmt;

/// An error produced while parsing or lowering an ASN.1 module.
#[derive(Debug)]
pub enum Error {
    Parse(synta_codegen::ParseError),
    Codegen(CodegenError),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Parse(error) => error.fmt(f),
            Self::Codegen(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Parse(error) => Some(error),
            Self::Codegen(error) => Some(error),
        }
    }
}

impl From<synta_codegen::ParseError> for Error {
    fn from(value: synta_codegen::ParseError) -> Self {
        Self::Parse(value)
    }
}

impl From<CodegenError> for Error {
    fn from(value: CodegenError) -> Self {
        Self::Codegen(value)
    }
}

/// A schema construct that cannot yet be represented faithfully by the Vest backend.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodegenError {
    pub path: String,
    pub message: String,
}

impl CodegenError {
    pub(crate) fn new(path: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            path: path.into(),
            message: message.into(),
        }
    }
}

impl fmt::Display for CodegenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.path, self.message)
    }
}

impl std::error::Error for CodegenError {}
