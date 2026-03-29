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

    // Post-process to add blank lines between top-level items
    let formatted = add_blank_lines_between_items(&formatted);

    Ok(formatted)
}

/// Add blank lines between top-level items for better readability.
/// Inserts a blank line after `}` that ends a top-level item (not inside nested blocks).
fn add_blank_lines_between_items(code: &str) -> String {
    let mut result = String::with_capacity(code.len() * 11 / 10);
    let lines: Vec<&str> = code.lines().collect();

    for (i, line) in lines.iter().enumerate() {
        result.push_str(line);
        result.push('\n');

        // Check if this line ends a top-level item and the next line starts a new item
        if i + 1 < lines.len() {
            let trimmed = line.trim();
            let next_line = lines[i + 1].trim();

            // Add blank line after closing brace at column 0 (top-level item end)
            // when followed by another item (not another closing brace, not empty)
            if trimmed == "}" && !line.starts_with(' ') && !next_line.is_empty() && next_line != "}"
            {
                result.push('\n');
            }
        }
    }

    result
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
