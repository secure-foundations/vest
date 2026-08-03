const RUST_KEYWORDS: &[&str] = &[
    "Self", "abstract", "as", "async", "await", "become", "box", "break", "const", "continue",
    "crate", "do", "dyn", "else", "enum", "extern", "false", "final", "fn", "for", "gen", "if",
    "impl", "in", "let", "loop", "macro", "match", "mod", "move", "override", "priv", "pub", "ref",
    "return", "self", "static", "struct", "super", "trait", "true", "try", "type", "typeof",
    "union", "unsafe", "unsized", "use", "virtual", "where", "while", "yield",
];

pub(crate) fn format_type_name(name: &str) -> String {
    let mut result = to_snake_case(name).to_ascii_uppercase();
    if result.is_empty() || result.starts_with(|c: char| c.is_ascii_digit()) {
        result.insert_str(0, "ASN1_");
    }
    if RUST_KEYWORDS
        .iter()
        .any(|keyword| keyword.eq_ignore_ascii_case(&result))
    {
        result.push_str("_ASN1");
    }
    result
}

pub(crate) fn value_type_name(name: &str) -> String {
    let mut result = to_pascal_case(name);
    if result.is_empty() || result.starts_with(|c: char| c.is_ascii_digit()) {
        result.insert_str(0, "Asn1");
    }
    if RUST_KEYWORDS.contains(&result.as_str()) {
        result.push_str("Asn1");
    }
    result
}

pub(crate) fn spec_type_name(name: &str) -> String {
    format!("{}Spec", value_type_name(name))
}

pub(crate) fn rust_field_name(name: &str) -> String {
    let mut result = to_snake_case(name);
    if result.is_empty() || result.starts_with(|c: char| c.is_ascii_digit()) {
        result.insert_str(0, "asn1_");
    }
    if RUST_KEYWORDS.contains(&result.as_str()) {
        result.push('_');
    }
    result
}

pub(crate) fn rust_variant_name(name: &str) -> String {
    value_type_name(name)
}

pub(crate) fn value_const_name(name: &str) -> String {
    let mut result = to_snake_case(name).to_ascii_uppercase();
    if result.is_empty() || result.starts_with(|c: char| c.is_ascii_digit()) {
        result.insert_str(0, "ASN1_");
    }
    if RUST_KEYWORDS
        .iter()
        .any(|keyword| keyword.eq_ignore_ascii_case(&result))
    {
        result.push_str("_ASN1");
    }
    result
}

pub(crate) fn to_pascal_case(name: &str) -> String {
    split_words(name)
        .into_iter()
        .map(|word| {
            let mut chars = word.chars();
            let Some(first) = chars.next() else {
                return String::new();
            };
            let mut result = first.to_ascii_uppercase().to_string();
            if word
                .chars()
                .all(|c| !c.is_ascii_alphabetic() || c.is_ascii_uppercase())
            {
                result.extend(chars.map(|c| c.to_ascii_lowercase()));
            } else {
                result.extend(chars);
            }
            result
        })
        .collect()
}

pub(crate) fn to_snake_case(name: &str) -> String {
    split_words(name)
        .into_iter()
        .map(|word| word.to_ascii_lowercase())
        .collect::<Vec<_>>()
        .join("_")
}

fn split_words(name: &str) -> Vec<String> {
    let chars: Vec<char> = name.chars().collect();
    let mut words = Vec::new();
    let mut current = String::new();

    for (index, &character) in chars.iter().enumerate() {
        if !character.is_ascii_alphanumeric() {
            if !current.is_empty() {
                words.push(std::mem::take(&mut current));
            }
            continue;
        }

        let previous = index.checked_sub(1).and_then(|i| chars.get(i)).copied();
        let next = chars.get(index + 1).copied();
        let starts_word = character.is_ascii_uppercase()
            && !current.is_empty()
            && (previous.is_some_and(|c| c.is_ascii_lowercase() || c.is_ascii_digit())
                || next.is_some_and(|c| c.is_ascii_lowercase()));

        if starts_word {
            words.push(std::mem::take(&mut current));
        }
        current.push(character);
    }

    if !current.is_empty() {
        words.push(current);
    }
    words
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn converts_asn1_names() {
        assert_eq!(format_type_name("AlgorithmIdentifier"), "ALGORITHM_IDENTIFIER");
        assert_eq!(format_type_name("KDC-REQ"), "KDC_REQ");
        assert_eq!(rust_field_name("type"), "type_");
        assert_eq!(rust_variant_name("needs-review"), "NeedsReview");
    }
}
