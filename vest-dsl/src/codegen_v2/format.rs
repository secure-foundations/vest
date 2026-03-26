//! Output formatting with syn and prettyplease.

use proc_macro2::TokenStream;

/// Format a token stream as pretty-printed Rust code.
/// Returns an error if the code is not valid Rust syntax.
pub fn format_rust_code(tokens: TokenStream) -> Result<String, FormatError> {
    let code = tokens.to_string();

    // Parse with syn to validate
    let syntax_tree: syn::File = syn::parse_str(&code)
        .map_err(|e| FormatError::ParseError(format!("Failed to parse generated code: {}", e)))?;

    // Format with prettyplease
    let formatted = prettyplease::unparse(&syntax_tree);

    Ok(formatted)
}

/// Errors that can occur during formatting.
#[derive(Debug, Clone)]
pub enum FormatError {
    /// The generated code failed to parse as valid Rust.
    ParseError(String),
}

impl std::fmt::Display for FormatError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FormatError::ParseError(msg) => write!(f, "Parse error: {}", msg),
        }
    }
}

impl std::error::Error for FormatError {}
