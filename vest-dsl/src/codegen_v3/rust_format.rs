use proc_macro2::TokenStream;

pub fn format_rust_code(tokens: TokenStream) -> Result<String, FormatError> {
    let code = tokens.to_string();
    let syntax_tree: syn::File = syn::parse_str(&code)
        .map_err(|e| FormatError::ParseError(format!("Failed to parse generated code: {}", e)))?;
    let formatted = prettyplease::unparse(&syntax_tree);
    Ok(add_blank_lines_between_items(&formatted))
}

fn add_blank_lines_between_items(code: &str) -> String {
    let mut result = String::with_capacity(code.len() * 11 / 10);
    let lines: Vec<&str> = code.lines().collect();

    for (i, line) in lines.iter().enumerate() {
        result.push_str(line);
        result.push('\n');

        if i + 1 < lines.len() {
            let trimmed = line.trim();
            let next_line = lines[i + 1].trim();
            if trimmed == "}" && !line.starts_with(' ') && !next_line.is_empty() && next_line != "}"
            {
                result.push('\n');
            }
        }
    }

    result
}

#[derive(Debug, Clone)]
pub enum FormatError {
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
