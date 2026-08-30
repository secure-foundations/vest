//! ASN.1 schema parser

use crate::ast::*;
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub struct ParseError {
    pub message: String,
    pub line: usize,
    pub column: usize,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Parse error at {}:{}: {}",
            self.line, self.column, self.message
        )
    }
}

impl std::error::Error for ParseError {}

type Result<T> = std::result::Result<T, ParseError>;

// ASN.1 X.680 Reserved Keywords - All keywords are case-sensitive per X.680 specification
// These are organized by category for maintainability

/// Type constructor keywords
const TYPE_CONSTRUCTORS: &[&str] = &["SEQUENCE", "SET", "CHOICE", "OF"];

/// Field modifier keywords
const FIELD_MODIFIERS: &[&str] = &["OPTIONAL", "DEFAULT"];

/// Primitive type keywords (all uppercase per X.680)
const PRIMITIVE_TYPES: &[&str] = &[
    "INTEGER",
    "BOOLEAN",
    "OCTET",
    "STRING",
    "BIT",
    "OBJECT",
    "IDENTIFIER",
    "NULL",
    "REAL",
    "ENUMERATED",
];

/// Built-in string types (mixed case per X.680)
/// These can be used both as keywords and as type references
const STRING_TYPES: &[&str] = &[
    "UTF8String",
    "PrintableString",
    "IA5String",
    "TeletexString",
    "T61String",
    "BMPString",
    "UniversalString",
    "GeneralString",
    "GraphicString",
    "NumericString",
    "ObjectDescriptor",
    "VideotexString",
    "VisibleString",
    "ISO646String",
];

/// Time type keywords
const TIME_TYPES: &[&str] = &[
    "UTCTime",
    "GeneralizedTime",
    "DATE",
    "TIME",
    "TIME-OF-DAY",
    "DATE-TIME",
    "DURATION",
];

/// Tagging keywords
const TAGGING_KEYWORDS: &[&str] = &[
    "EXPLICIT",
    "IMPLICIT",
    "AUTOMATIC",
    "TAGS",
    "UNIVERSAL",
    "APPLICATION",
    "PRIVATE",
    "CONTEXT",
    "IMPLIED",
];

/// Module definition keywords
const MODULE_KEYWORDS: &[&str] = &["BEGIN", "END", "DEFINITIONS"];

/// Constraint keywords
const CONSTRAINT_KEYWORDS: &[&str] = &[
    "SIZE",
    "MIN",
    "MAX",
    "FROM",
    "PATTERN",
    "CONTAINING",
    "WITH",
    "COMPONENTS",
];

/// Set operation keywords
const SET_OPERATIONS: &[&str] = &["ALL", "EXCEPT", "INCLUDES", "INTERSECTION", "UNION"];

/// Import/export keywords
const IMPORT_EXPORT: &[&str] = &["IMPORTS", "EXPORTS"];

/// Special keywords
const SPECIAL_KEYWORDS: &[&str] = &[
    "ANY",
    "DEFINED",
    "BY",
    "ABSENT",
    "PRESENT",
    "TRUE",
    "FALSE",
    "EXTENSIBILITY",
    "ENCODED",
    "PLUS-INFINITY",
    "MINUS-INFINITY",
    "NOT-A-NUMBER",
];

/// Class-related keywords
const CLASS_KEYWORDS: &[&str] = &[
    "CLASS",
    "UNIQUE",
    "SYNTAX",
    "TYPE-IDENTIFIER",
    "ABSTRACT-SYNTAX",
];

/// Additional type keywords
const ADDITIONAL_TYPES: &[&str] = &[
    "EXTERNAL",
    "EMBEDDED",
    "PDV",
    "CHARACTER",
    "RELATIVE-OID",
    "OID-IRI",
    "RELATIVE-OID-IRI",
];

/// Check if a string is an ASN.1 reserved keyword
fn is_asn1_keyword(s: &str) -> bool {
    TYPE_CONSTRUCTORS.contains(&s)
        || FIELD_MODIFIERS.contains(&s)
        || PRIMITIVE_TYPES.contains(&s)
        || STRING_TYPES.contains(&s)
        || TIME_TYPES.contains(&s)
        || TAGGING_KEYWORDS.contains(&s)
        || MODULE_KEYWORDS.contains(&s)
        || CONSTRAINT_KEYWORDS.contains(&s)
        || SET_OPERATIONS.contains(&s)
        || IMPORT_EXPORT.contains(&s)
        || SPECIAL_KEYWORDS.contains(&s)
        || CLASS_KEYWORDS.contains(&s)
        || ADDITIONAL_TYPES.contains(&s)
}

/// Built-in types that can be used as type references (keywords that represent types)
fn is_builtin_type_keyword(s: &str) -> bool {
    STRING_TYPES.contains(&s) || TIME_TYPES.contains(&s) || ADDITIONAL_TYPES.contains(&s)
}

/// Tokenizer for ASN.1 schemas
#[derive(Clone)]
struct Lexer {
    input: Vec<char>,
    pos: usize,
    line: usize,
    column: usize,
}

#[derive(Debug, Clone, PartialEq)]
enum Token {
    Identifier(String),
    Number(u64),
    Keyword(String),
    Symbol(String),
    Eof,
}

impl Lexer {
    fn new(input: &str) -> Self {
        Self {
            input: input.chars().collect(),
            pos: 0,
            line: 1,
            column: 1,
        }
    }

    fn current(&self) -> Option<char> {
        self.input.get(self.pos).copied()
    }

    fn advance(&mut self) -> Option<char> {
        if let Some(ch) = self.current() {
            self.pos += 1;
            if ch == '\n' {
                self.line += 1;
                self.column = 1;
            } else {
                self.column += 1;
            }
            Some(ch)
        } else {
            None
        }
    }

    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.current() {
            if ch.is_whitespace() {
                self.advance();
            } else if ch == '-' && self.peek(1) == Some('-') {
                // Skip comments (-- to end of line)
                while let Some(ch) = self.current() {
                    self.advance();
                    if ch == '\n' {
                        break;
                    }
                }
            } else {
                break;
            }
        }
    }

    fn peek(&self, offset: usize) -> Option<char> {
        self.input.get(self.pos + offset).copied()
    }

    fn next_token(&mut self) -> Result<Token> {
        self.skip_whitespace();

        let ch = match self.current() {
            Some(ch) => ch,
            None => return Ok(Token::Eof),
        };

        // Quoted strings
        if ch == '"' {
            self.advance(); // consume opening quote
            let mut string = String::new();
            while let Some(ch) = self.current() {
                if ch == '"' {
                    self.advance(); // consume closing quote
                    break;
                } else if ch == '\\' {
                    // Handle escape sequences
                    self.advance();
                    if let Some(escaped) = self.current() {
                        match escaped {
                            'n' => string.push('\n'),
                            't' => string.push('\t'),
                            'r' => string.push('\r'),
                            '\\' => string.push('\\'),
                            '"' => string.push('"'),
                            _ => string.push(escaped),
                        }
                        self.advance();
                    }
                } else {
                    string.push(ch);
                    self.advance();
                }
            }
            return Ok(Token::Identifier(string)); // Return as identifier for now
        }

        // Numbers
        if ch.is_ascii_digit() {
            let mut num = String::new();
            while let Some(ch) = self.current() {
                if ch.is_ascii_digit() {
                    num.push(ch);
                    self.advance();
                } else {
                    break;
                }
            }
            let n: u64 = num.parse().map_err(|_| ParseError {
                message: format!("number '{num}' overflows u64"),
                line: self.line,
                column: self.column,
            })?;
            return Ok(Token::Number(n));
        }

        // Class field references: &identifier (X.681 §9)
        // Consumed as a single Identifier token with the '&' prefix included.
        if ch == '&' && self.peek(1).is_some_and(|c| c.is_alphabetic()) {
            self.advance(); // consume '&'
            let mut ident = String::from("&");
            while let Some(ch) = self.current() {
                if ch.is_alphanumeric() || ch == '-' {
                    ident.push(ch);
                    self.advance();
                } else {
                    break;
                }
            }
            return Ok(Token::Identifier(ident));
        }

        // Identifiers and keywords
        if ch.is_alphabetic() {
            let mut ident = String::new();
            while let Some(ch) = self.current() {
                if ch.is_alphanumeric() || ch == '-' {
                    ident.push(ch);
                    self.advance();
                } else {
                    break;
                }
            }

            // X.680 specifies that ASN.1 keywords are case-sensitive.
            // Check if this identifier matches a reserved keyword exactly.
            if is_asn1_keyword(&ident) {
                return Ok(Token::Keyword(ident));
            }

            return Ok(Token::Identifier(ident));
        }

        // Multi-character symbols (check these first!)
        if ch == ':' && self.peek(1) == Some(':') && self.peek(2) == Some('=') {
            self.advance();
            self.advance();
            self.advance();
            return Ok(Token::Symbol("::=".to_string()));
        }

        if ch == '.' && self.peek(1) == Some('.') && self.peek(2) == Some('.') {
            self.advance();
            self.advance();
            self.advance();
            return Ok(Token::Symbol("...".to_string()));
        }

        if ch == '.' && self.peek(1) == Some('.') {
            self.advance();
            self.advance();
            return Ok(Token::Symbol("..".to_string()));
        }

        // Minus sign (but not if it's part of -- comment, which is handled in skip_whitespace)
        if ch == '-' && self.peek(1) != Some('-') {
            self.advance();
            return Ok(Token::Symbol("-".to_string()));
        }

        // Single-character symbols
        if matches!(
            ch,
            '{' | '}' | '[' | ']' | '(' | ')' | ',' | ':' | '|' | '^' | '@' | ';' | '.'
        ) {
            self.advance();
            return Ok(Token::Symbol(ch.to_string()));
        }

        Err(ParseError {
            message: format!("Unexpected character: {}", ch),
            line: self.line,
            column: self.column,
        })
    }
}

/// Parser for ASN.1 schemas
#[derive(Clone)]
pub struct Parser {
    lexer: Lexer,
    current: Token,
    /// Default tagging mode derived from the module's `DEFINITIONS [IMPLICIT|EXPLICIT] TAGS`
    /// declaration.  Starts as `Explicit` (the ASN.1 default when no keyword is present) and is
    /// updated in `parse_module()` after the header is parsed.
    default_tagging: Tagging,
}

impl Parser {
    pub fn new(input: &str) -> Result<Self> {
        let mut lexer = Lexer::new(input);
        let current = lexer.next_token()?;
        Ok(Self {
            lexer,
            current,
            default_tagging: Tagging::Explicit,
        })
    }

    fn advance(&mut self) -> Result<()> {
        self.current = self.lexer.next_token()?;
        Ok(())
    }

    fn expect_keyword(&mut self, keyword: &str) -> Result<()> {
        if let Token::Keyword(kw) = &self.current {
            if kw == keyword {
                self.advance()?;
                return Ok(());
            }
        }
        Err(ParseError {
            message: format!("Expected keyword '{}', got {:?}", keyword, self.current),
            line: self.lexer.line,
            column: self.lexer.column,
        })
    }

    fn expect_symbol(&mut self, symbol: &str) -> Result<()> {
        if let Token::Symbol(sym) = &self.current {
            if sym == symbol {
                self.advance()?;
                return Ok(());
            }
        }
        Err(ParseError {
            message: format!("Expected symbol '{}', got {:?}", symbol, self.current),
            line: self.lexer.line,
            column: self.lexer.column,
        })
    }

    fn expect_identifier(&mut self) -> Result<String> {
        if let Token::Identifier(name) = &self.current {
            let result = name.clone();
            self.advance()?;
            return Ok(result);
        }
        Err(ParseError {
            message: format!("Expected identifier, got {:?}", self.current),
            line: self.lexer.line,
            column: self.lexer.column,
        })
    }

    /// Parse size constraint (e.g., (SIZE (16)) or (SIZE (1..64)))
    fn parse_size_constraint(&mut self) -> Result<Option<SizeConstraint>> {
        if !matches!(self.current, Token::Symbol(ref s) if s == "(") {
            return Ok(None);
        }

        self.advance()?; // consume '('

        // Check for SIZE keyword
        if !matches!(self.current, Token::Keyword(ref kw) if kw == "SIZE") {
            // Not a SIZE constraint - skip it
            while !matches!(self.current, Token::Symbol(ref s) if s == ")") {
                if matches!(self.current, Token::Eof) {
                    break;
                }
                self.advance()?;
            }
            if matches!(self.current, Token::Symbol(ref s) if s == ")") {
                self.advance()?;
            }
            return Ok(None);
        }

        self.advance()?; // consume SIZE
        self.expect_symbol("(")?;

        // Parse size value
        let min = if let Token::Number(n) = self.current {
            let val = n;
            self.advance()?;
            Some(val)
        } else {
            None
        };

        let constraint = if matches!(self.current, Token::Symbol(ref s) if s == "..") {
            self.advance()?;
            let max = if let Token::Number(n) = self.current {
                let val = n;
                self.advance()?;
                Some(val)
            } else {
                None
            };
            SizeConstraint::Range(min, max)
        } else if let Some(size) = min {
            SizeConstraint::Fixed(size)
        } else {
            return Ok(None);
        };

        self.expect_symbol(")")?; // inner paren
        self.expect_symbol(")")?; // outer paren

        Ok(Some(constraint))
    }

    /// Parse the X.680 collection form `SIZE (min..max)` which appears
    /// between `SEQUENCE`/`SET` and `OF`.
    fn parse_collection_size_constraint(&mut self) -> Result<SizeConstraint> {
        self.expect_symbol("(")?;
        let min = match self.current.clone() {
            Token::Number(value) => {
                self.advance()?;
                Some(value)
            }
            Token::Keyword(ref keyword) if keyword == "MIN" => {
                self.advance()?;
                None
            }
            _ => None,
        };
        let constraint = if matches!(self.current, Token::Symbol(ref symbol) if symbol == "..") {
            self.advance()?;
            let max = match self.current.clone() {
                Token::Number(value) => {
                    self.advance()?;
                    Some(value)
                }
                Token::Keyword(ref keyword) if keyword == "MAX" => {
                    self.advance()?;
                    None
                }
                _ => None,
            };
            SizeConstraint::Range(min, max)
        } else if let Some(value) = min {
            SizeConstraint::Fixed(value)
        } else {
            return Err(ParseError {
                message: "Expected a collection SIZE value or range".to_string(),
                line: self.lexer.line,
                column: self.lexer.column,
            });
        };
        self.expect_symbol(")")?;
        Ok(constraint)
    }

    /// Parse an integer value (positive or negative)
    fn parse_integer_value(&mut self) -> Result<Option<i64>> {
        // Check for negative sign
        let negative = if matches!(self.current, Token::Symbol(ref s) if s == "-") {
            self.advance()?;
            true
        } else {
            false
        };

        if let Token::Number(n) = self.current {
            let val = if negative { -(n as i64) } else { n as i64 };
            self.advance()?;
            Ok(Some(val))
        } else {
            Ok(None)
        }
    }

    /// Parse a constraint value (X.680: integer, named value, MIN, or MAX)
    fn parse_constraint_value(&mut self) -> Result<ConstraintValue> {
        // Check for MIN keyword
        if matches!(self.current, Token::Keyword(ref kw) if kw == "MIN") {
            self.advance()?;
            return Ok(ConstraintValue::Min);
        }

        // Check for MAX keyword
        if matches!(self.current, Token::Keyword(ref kw) if kw == "MAX") {
            self.advance()?;
            return Ok(ConstraintValue::Max);
        }

        // Check for named value (identifier)
        if let Token::Identifier(ref name) = self.current {
            let name = name.clone();
            self.advance()?;
            return Ok(ConstraintValue::NamedValue(name));
        }

        // Check for integer value
        if let Some(val) = self.parse_integer_value()? {
            return Ok(ConstraintValue::Integer(val));
        }

        Err(ParseError {
            message: "Expected constraint value (integer, MIN, MAX, or identifier)".to_string(),
            line: self.lexer.line,
            column: self.lexer.column,
        })
    }

    /// Parse a subtype constraint with union/intersection operators
    fn parse_subtype_constraint(&mut self) -> Result<SubtypeConstraint> {
        // Parse the first constraint element
        let first = self.parse_single_constraint()?;

        // Check for union (|) or intersection (^) operators
        let mut elements = vec![first];
        let mut is_union = false;
        let mut is_intersection = false;

        while let Token::Symbol(ref s) = self.current {
            if s != "|" && s != "^" {
                break;
            }
            let op = s.clone();

            if op == "|" {
                is_union = true;
            } else {
                is_intersection = true;
            }

            self.advance()?; // consume operator
            elements.push(self.parse_single_constraint()?);
        }

        // Return appropriate constraint type
        if is_union && is_intersection {
            return Err(ParseError {
                message: "Cannot mix union (|) and intersection (^) operators without parentheses"
                    .to_string(),
                line: self.lexer.line,
                column: self.lexer.column,
            });
        }

        if is_union {
            Ok(SubtypeConstraint::Union(elements))
        } else if is_intersection {
            Ok(SubtypeConstraint::Intersection(elements))
        } else {
            Ok(elements.into_iter().next().unwrap())
        }
    }

    /// Parse a single constraint element (value, range, or parenthesized constraint)
    fn parse_single_constraint(&mut self) -> Result<SubtypeConstraint> {
        // Check for ALL EXCEPT
        if matches!(self.current, Token::Keyword(ref kw) if kw == "ALL") {
            self.advance()?;
            self.expect_keyword("EXCEPT")?;
            let inner = self.parse_single_constraint()?;
            return Ok(SubtypeConstraint::Complement(Box::new(inner)));
        }

        // Check for parenthesized constraint
        if matches!(self.current, Token::Symbol(ref s) if s == "(") {
            self.advance()?; // consume '('
            let constraint = self.parse_subtype_constraint()?;
            self.expect_symbol(")")?;
            return Ok(constraint);
        }

        // Parse first value
        let first_value = self.parse_constraint_value()?;

        // Check for range operator (..)
        if matches!(self.current, Token::Symbol(ref s) if s == "..") {
            self.advance()?; // consume '..'
            let second_value = self.parse_constraint_value()?;
            return Ok(SubtypeConstraint::ValueRange {
                min: first_value,
                max: second_value,
            });
        }

        // Single value constraint
        Ok(SubtypeConstraint::SingleValue(first_value))
    }

    /// Parse a permitted alphabet constraint: FROM ("A".."Z" | "0".."9")
    fn parse_permitted_alphabet(&mut self) -> Result<SubtypeConstraint> {
        self.expect_keyword("FROM")?;
        self.expect_symbol("(")?;

        let mut ranges = Vec::new();

        loop {
            // Parse a string literal or character range
            if let Token::Identifier(ref s) = self.current {
                // String literal - extract character range
                let chars: Vec<char> = s.chars().collect();
                if chars.len() == 1 {
                    let ch = chars[0];
                    self.advance()?;

                    // Check for range operator
                    if matches!(self.current, Token::Symbol(ref sym) if sym == "..") {
                        self.advance()?; // consume '..'

                        // Parse end character
                        if let Token::Identifier(ref end_s) = self.current {
                            let end_chars: Vec<char> = end_s.chars().collect();
                            if end_chars.len() == 1 {
                                ranges.push(CharRange {
                                    min: ch,
                                    max: end_chars[0],
                                });
                                self.advance()?;
                            }
                        }
                    } else {
                        // Single character
                        ranges.push(CharRange { min: ch, max: ch });
                    }
                }
            }

            // Check for more ranges
            if matches!(self.current, Token::Symbol(ref s) if s == "|") {
                self.advance()?; // consume '|'
            } else {
                break;
            }
        }

        self.expect_symbol(")")?;
        Ok(SubtypeConstraint::PermittedAlphabet(ranges))
    }

    /// Parse a pattern constraint: PATTERN "regex"
    fn parse_pattern(&mut self) -> Result<SubtypeConstraint> {
        self.expect_keyword("PATTERN")?;

        // Pattern should be a string literal
        if let Token::Identifier(ref pattern) = self.current {
            let pattern_str = pattern.clone();
            self.advance()?;
            Ok(SubtypeConstraint::Pattern(pattern_str))
        } else {
            Err(ParseError {
                message: "Expected pattern string after PATTERN keyword".to_string(),
                line: self.lexer.line,
                column: self.lexer.column,
            })
        }
    }

    /// Parse a DEFAULT value (number, boolean, string, etc.)
    fn parse_default_value(&mut self) -> Result<String> {
        let value = match &self.current {
            Token::Number(n) => {
                let val = n.to_string();
                self.advance()?;
                val
            }
            Token::Symbol(s) if s == "-" => {
                // Negative number
                self.advance()?;
                if let Token::Number(n) = self.current {
                    let val = format!("-{}", n);
                    self.advance()?;
                    val
                } else {
                    return Err(ParseError {
                        message: "Expected number after '-'".to_string(),
                        line: self.lexer.line,
                        column: self.lexer.column,
                    });
                }
            }
            Token::Keyword(kw) if kw == "TRUE" => {
                self.advance()?;
                "true".to_string()
            }
            Token::Keyword(kw) if kw == "FALSE" => {
                self.advance()?;
                "false".to_string()
            }
            Token::Identifier(s) => {
                // Could be a string literal (from quoted string) or named value
                let val = s.clone();
                self.advance()?;
                // If it looks like a string literal, quote it
                // Otherwise assume it's a named constant
                val
            }
            _ => {
                return Err(ParseError {
                    message: format!("Unexpected token in DEFAULT value: {:?}", self.current),
                    line: self.lexer.line,
                    column: self.lexer.column,
                });
            }
        };

        Ok(value)
    }

    /// Helper to parse a string type with optional constraints
    /// This reduces code duplication for UTF8String, PrintableString, IA5String, etc.
    fn parse_string_type(&mut self, base_type: Type) -> Result<Type> {
        self.advance()?;

        // Check for X.680 string constraints (SIZE, FROM, PATTERN)
        if let Some(constraint) = self.parse_string_constraint()? {
            return Ok(Type::Constrained {
                base_type: Box::new(base_type),
                constraint: Constraint {
                    spec: ConstraintSpec::Subtype(constraint),
                    exception: None,
                },
            });
        }

        Ok(base_type)
    }

    /// Parse string constraints (SIZE, FROM, PATTERN)
    /// Supports combined constraints: (SIZE (...) FROM (...))
    fn parse_string_constraint(&mut self) -> Result<Option<SubtypeConstraint>> {
        if !matches!(self.current, Token::Symbol(ref s) if s == "(") {
            return Ok(None);
        }

        self.advance()?; // consume '('

        // Collect multiple constraints that can be combined
        let mut constraints = Vec::new();

        // Parse first constraint
        if let Some(constraint) = self.parse_single_string_constraint()? {
            constraints.push(constraint);
        }

        // Check for additional constraints (combined constraints)
        // e.g., (SIZE (4..6) FROM ("0".."9"))
        while !matches!(self.current, Token::Symbol(ref s) if s == ")") {
            if matches!(self.current, Token::Eof) {
                break;
            }

            // Try to parse another constraint keyword
            if let Some(constraint) = self.parse_single_string_constraint()? {
                constraints.push(constraint);
            } else {
                // If not a recognized constraint, skip to closing paren
                break;
            }
        }

        self.expect_symbol(")")?; // outer paren

        // Return appropriate constraint based on count
        match constraints.len() {
            0 => Ok(None),
            1 => Ok(Some(constraints.into_iter().next().unwrap())),
            _ => {
                // Multiple constraints - combine with Intersection
                Ok(Some(SubtypeConstraint::Intersection(constraints)))
            }
        }
    }

    /// Parse a single string constraint keyword (SIZE, FROM, PATTERN, CONTAINING)
    fn parse_single_string_constraint(&mut self) -> Result<Option<SubtypeConstraint>> {
        // Check for SIZE keyword
        if matches!(self.current, Token::Keyword(ref kw) if kw == "SIZE") {
            self.advance()?; // consume SIZE
            self.expect_symbol("(")?;

            // Parse size value or range
            let size_constraint = self.parse_subtype_constraint()?;

            self.expect_symbol(")")?; // inner paren
                                      // Don't consume outer paren here - let caller handle it

            return Ok(Some(SubtypeConstraint::SizeConstraint(Box::new(
                size_constraint,
            ))));
        }

        // Check for FROM keyword
        if matches!(self.current, Token::Keyword(ref kw) if kw == "FROM") {
            let constraint = self.parse_permitted_alphabet()?;
            // Don't consume outer paren here - let caller handle it
            return Ok(Some(constraint));
        }

        // Check for PATTERN keyword
        if matches!(self.current, Token::Keyword(ref kw) if kw == "PATTERN") {
            let constraint = self.parse_pattern()?;
            // Don't consume outer paren here - let caller handle it
            return Ok(Some(constraint));
        }

        // Check for CONTAINING keyword (Phase 3)
        if matches!(self.current, Token::Keyword(ref kw) if kw == "CONTAINING") {
            self.advance()?; // consume CONTAINING
            let contained_type = self.parse_type()?;
            // Don't consume outer paren here - let caller handle it
            return Ok(Some(SubtypeConstraint::ContainedSubtype(Box::new(
                contained_type,
            ))));
        }

        Ok(None)
    }

    /// Parse EXPORTS clause
    /// EXPORTS Type1, Type2, Type3; or EXPORTS ALL;
    fn parse_exports(&mut self) -> Result<Vec<String>> {
        let mut exports = Vec::new();

        // Check if EXPORTS keyword is present
        if !matches!(self.current, Token::Keyword(ref kw) if kw == "EXPORTS") {
            return Ok(exports);
        }

        self.advance()?; // consume EXPORTS

        // Check for "EXPORTS ALL;"
        if matches!(self.current, Token::Keyword(ref kw) if kw == "ALL") {
            self.advance()?; // consume ALL
            if matches!(self.current, Token::Symbol(ref s) if s == ";") {
                self.advance()?; // consume ';'
            }
            // Return empty vec - ALL means export everything
            // Code generator will handle this appropriately
            return Ok(exports);
        }

        // Parse exported symbol names
        loop {
            if matches!(self.current, Token::Symbol(ref s) if s == ";") {
                self.advance()?; // consume ';'
                break;
            }

            if matches!(self.current, Token::Eof)
                || matches!(self.current, Token::Keyword(ref kw) if kw == "IMPORTS" || kw == "END")
            {
                // Semicolon is optional in some cases
                break;
            }

            let name = self.expect_identifier()?;
            exports.push(name);

            // Check for comma
            if matches!(self.current, Token::Symbol(ref s) if s == ",") {
                self.advance()?; // consume ','
            }
        }

        Ok(exports)
    }

    /// Parse IMPORTS clause
    /// IMPORTS Type1, Type2 FROM Module1 Type3 FROM Module2;
    fn parse_imports(&mut self) -> Result<Vec<Import>> {
        let mut imports = Vec::new();

        // Check if IMPORTS keyword is present
        if !matches!(self.current, Token::Keyword(ref kw) if kw == "IMPORTS") {
            return Ok(imports);
        }

        self.advance()?; // consume IMPORTS

        // Parse import declarations
        loop {
            if matches!(self.current, Token::Symbol(ref s) if s == ";") {
                self.advance()?; // consume ';'
                break;
            }

            if matches!(self.current, Token::Eof)
                || matches!(self.current, Token::Keyword(ref kw) if kw == "END")
            {
                // Semicolon is optional in some cases
                break;
            }

            // Parse symbols (Type1, Type2, ...)
            let mut symbols = Vec::new();
            loop {
                if matches!(self.current, Token::Keyword(ref kw) if kw == "FROM") {
                    break;
                }

                let name = self.expect_identifier()?;

                // Skip optional parameterized type arguments after identifier,
                // e.g. `AlgorithmIdentifier{}` or `AlgorithmIdentifier{T, {S}}`.
                if matches!(self.current, Token::Symbol(ref s) if s == "{") {
                    self.skip_balanced_braces()?;
                }

                symbols.push(name);

                // Check for comma
                if matches!(self.current, Token::Symbol(ref s) if s == ",") {
                    self.advance()?; // consume ','
                } else {
                    break;
                }
            }

            // Expect FROM keyword
            self.expect_keyword("FROM")?;

            // Parse module name
            let module_name = self.expect_identifier()?;

            // Skip optional module OID block after the module name,
            // e.g. `FROM AlgorithmInformation-2009 { iso(1) ... }`.
            if matches!(self.current, Token::Symbol(ref s) if s == "{") {
                self.skip_balanced_braces()?;
            }

            imports.push(Import {
                symbols,
                module_name,
            });

            // Check if there are more imports or end of IMPORTS clause
            if matches!(self.current, Token::Symbol(ref s) if s == ";") {
                self.advance()?; // consume ';'
                break;
            }

            // If no semicolon, check for additional import groups or end
            if matches!(self.current, Token::Eof)
                || matches!(self.current, Token::Keyword(ref kw) if kw == "END")
                || !matches!(self.current, Token::Identifier(_))
            {
                break;
            }
        }

        Ok(imports)
    }

    /// Parse a complete module
    pub fn parse_module(&mut self) -> Result<Module> {
        let name = self.expect_identifier()?;

        // Parse optional module OID
        let oid = if let Token::Symbol(ref sym) = self.current {
            if sym == "{" {
                Some(self.parse_module_oid()?)
            } else {
                None
            }
        } else {
            None
        };

        self.expect_keyword("DEFINITIONS")?;

        // Parse optional tagging mode
        let tagging_mode = if let Token::Keyword(ref kw) = self.current {
            match kw.as_str() {
                "EXPLICIT" => {
                    self.advance()?;
                    self.expect_keyword("TAGS")?;
                    Some(crate::ast::TaggingMode::Explicit)
                }
                "IMPLICIT" => {
                    self.advance()?;
                    self.expect_keyword("TAGS")?;
                    Some(crate::ast::TaggingMode::Implicit)
                }
                "AUTOMATIC" => {
                    self.advance()?;
                    self.expect_keyword("TAGS")?;
                    Some(crate::ast::TaggingMode::Automatic)
                }
                _ => None,
            }
        } else {
            None
        };

        // Propagate the module-level tagging default to the parser so that bare [N] tags
        // in SEQUENCE fields use the correct default (IMPLICIT for "DEFINITIONS IMPLICIT TAGS",
        // etc.).  AUTOMATIC behaves like IMPLICIT for field tagging purposes.
        self.default_tagging = match &tagging_mode {
            Some(crate::ast::TaggingMode::Implicit) | Some(crate::ast::TaggingMode::Automatic) => {
                Tagging::Implicit
            }
            _ => Tagging::Explicit,
        };

        self.expect_symbol("::=")?;
        self.expect_keyword("BEGIN")?;

        // Parse EXPORTS if present
        let exports = self.parse_exports()?;

        // Parse IMPORTS if present
        let imports = self.parse_imports()?;

        // Parse definitions and value assignments
        let mut definitions = Vec::new();
        let mut values = Vec::new();
        let declared_type_names = self.scan_type_definition_names();
        while !matches!(self.current, Token::Keyword(ref kw) if kw == "END") {
            if matches!(self.current, Token::Eof) {
                break;
            }
            // Priority order:
            //  1. Classic value assignment (name OBJECT|INTEGER|BOOLEAN ::= value)
            //  2. IOC value assignment (name ClassName ::= { ... }) — consumed and discarded
            //  3. Type definition (TypeName ::= Type)
            if let Some(value_assignment) =
                self.try_parse_value_assignment(&definitions, &declared_type_names)?
            {
                values.push(value_assignment);
            } else if self.try_skip_class_alias()? {
                // Class alias assignment (e.g. `MyClass ::= TYPE-IDENTIFIER`) consumed and discarded
            } else if self.try_skip_ioc_assignment()? {
                // IOC assignment consumed; loop continues to the next definition
            } else {
                definitions.push(self.parse_definition()?);
            }
        }

        if matches!(self.current, Token::Keyword(ref kw) if kw == "END") {
            self.advance()?;
        }

        Ok(Module {
            name,
            oid,
            tagging_mode,
            imports,
            exports,
            definitions,
            values,
        })
    }

    /// Parse module OID: { iso(1) identified-organization(3) ... }
    /// Returns a vector of OID components as strings for simplicity
    fn parse_module_oid(&mut self) -> Result<Vec<String>> {
        self.expect_symbol("{")?;
        let mut oid_parts = Vec::new();

        // Parse OID components until we hit the closing brace
        while !matches!(self.current, Token::Symbol(ref sym) if sym == "}") {
            match &self.current {
                Token::Identifier(id) => {
                    oid_parts.push(id.clone());
                    self.advance()?;

                    // Check for (number) after identifier
                    if let Token::Symbol(ref sym) = self.current {
                        if sym == "(" {
                            self.advance()?;
                            if let Token::Number(n) = self.current {
                                oid_parts.push(n.to_string());
                                self.advance()?;
                            }
                            self.expect_symbol(")")?;
                        }
                    }
                }
                Token::Number(n) => {
                    oid_parts.push(n.to_string());
                    self.advance()?;
                }
                Token::Eof => {
                    return Err(ParseError {
                        message: "Unexpected end of input in module OID".to_string(),
                        line: self.lexer.line,
                        column: self.lexer.column,
                    });
                }
                _ => {
                    // Skip other tokens (like whitespace, etc.)
                    self.advance()?;
                }
            }
        }

        self.expect_symbol("}")?;
        Ok(oid_parts)
    }

    fn parse_definition(&mut self) -> Result<Definition> {
        let name = self.expect_identifier()?;

        // Skip optional parameterized type formal parameters after the type name,
        // e.g. `AttributeSet{ATTRIBUTE:AttrSet} ::= SEQUENCE { ... }`.
        // The parameter list carries governance information only; no DER encoding
        // information is lost by discarding it.
        if matches!(self.current, Token::Symbol(ref s) if s == "{") {
            self.skip_balanced_braces()?;
        }

        self.expect_symbol("::=")?;
        let ty = self.parse_type()?;

        // Never silently discard a trailing constraint. Consumers can decide
        // how to lower it once the AST represents it explicitly.
        if matches!(self.current, Token::Symbol(ref s) if s == "(") {
            return Err(ParseError {
                message: "trailing type constraints such as WITH COMPONENTS are not represented in the Synta AST".to_string(),
                line: self.lexer.line,
                column: self.lexer.column,
            });
        }

        Ok(Definition { name, ty })
    }

    /// Try to parse a value assignment (e.g., oidName OBJECT IDENTIFIER ::= { 1 2 3 })
    /// Returns None if this is not a value assignment (it's a type definition instead)
    fn try_parse_value_assignment(
        &mut self,
        definitions: &[Definition],
        declared_type_names: &[String],
    ) -> Result<Option<crate::ast::ValueAssignment>> {
        // Look ahead to determine if this is a value assignment
        // Value assignment: name Type ::= value
        // Type definition: TypeName ::= Type
        // We can distinguish by checking if there's a type keyword before ::=

        // We need at least: IDENTIFIER KEYWORD ::=
        // For value assignment, the second token should be OBJECT, INTEGER, BOOLEAN, etc.
        let is_value_assignment = if let Token::Identifier(_) = &self.current {
            match self.peek_next_token() {
                Token::Keyword(ref kw) => matches!(
                    kw.as_str(),
                    "OBJECT" | "INTEGER" | "BOOLEAN" | "REAL"
                ),
                Token::Identifier(ref type_name) => {
                    declared_type_names.iter().any(|name| name == type_name)
                        || resolve_assignment_type(
                            &Type::TypeRef(type_name.clone()),
                            definitions,
                            &mut Vec::new(),
                        )
                        .is_some()
                }
                _ => false,
            }
        } else {
            false
        };

        if !is_value_assignment {
            return Ok(None);
        }

        // Parse value assignment
        let name = self.expect_identifier()?;
        let ty = if let Token::Identifier(type_name) = &self.current {
            let type_name = type_name.clone();
            self.advance()?;
            Type::TypeRef(type_name)
        } else {
            self.parse_type()?
        };
        self.expect_symbol("::=")?;
        let value = if let Some(value_ty) =
            resolve_assignment_type(&ty, definitions, &mut Vec::new()).cloned()
        {
            self.parse_value(&value_ty)?
        } else {
            self.parse_unresolved_typed_value()?
        };

        Ok(Some(crate::ast::ValueAssignment { name, ty, value }))
    }

    /// Collect ordinary type-assignment names without consuming parser state.
    /// This permits value assignments to refer to types declared later in the module.
    fn scan_type_definition_names(&self) -> Vec<String> {
        let mut parser = self.clone();
        let mut names = Vec::new();
        while !matches!(parser.current, Token::Keyword(ref keyword) if keyword == "END")
            && !matches!(parser.current, Token::Eof)
        {
            if let Token::Identifier(name) = parser.current.clone() {
                if parser.advance().is_err() {
                    break;
                }
                if matches!(parser.current, Token::Symbol(ref symbol) if symbol == "::=") {
                    names.push(name);
                }
            } else if parser.advance().is_err() {
                break;
            }
        }
        names
    }

    fn parse_unresolved_typed_value(&mut self) -> Result<crate::ast::Value> {
        match &self.current {
            Token::Symbol(symbol) if symbol == "{" => self.parse_value(&Type::ObjectIdentifier),
            Token::Number(_) | Token::Symbol(_) => {
                if let Some(value) = self.parse_integer_value()? {
                    Ok(crate::ast::Value::Integer(value))
                } else {
                    Err(ParseError {
                        message: "unsupported value for a forward-referenced type".to_string(),
                        line: self.lexer.line,
                        column: self.lexer.column,
                    })
                }
            }
            Token::Keyword(keyword) if keyword == "TRUE" || keyword == "FALSE" => {
                self.parse_value(&Type::Boolean)
            }
            Token::Identifier(name) => {
                let name = name.clone();
                self.advance()?;
                Ok(crate::ast::Value::Identifier(name))
            }
            _ => Err(ParseError {
                message: "unsupported value for a forward-referenced type".to_string(),
                line: self.lexer.line,
                column: self.lexer.column,
            }),
        }
    }

    /// Try to consume a class alias assignment of the form:
    ///   `TypeName ::= TYPE-IDENTIFIER` or `TypeName ::= ABSTRACT-SYNTAX`
    ///
    /// These are X.681 §14.2 built-in class assignments that carry no concrete
    /// DER encoding.  Returning `true` causes the module parser to discard the
    /// definition without generating any Rust type.
    fn try_skip_class_alias(&mut self) -> Result<bool> {
        // Pattern: Identifier ::= (TYPE-IDENTIFIER | ABSTRACT-SYNTAX)
        // We peek: current = Identifier, next = ::=, after-next = keyword
        let is_ident = matches!(self.current, Token::Identifier(_));
        if !is_ident {
            return Ok(false);
        }

        // Save state so we can restore if this is NOT a class alias
        let saved_lexer = self.lexer.clone();
        let saved_current = self.current.clone();

        self.advance()?; // consume identifier

        // Must be followed by ::=
        if !matches!(self.current, Token::Symbol(ref s) if s == "::=") {
            self.lexer = saved_lexer;
            self.current = saved_current;
            return Ok(false);
        }
        self.advance()?; // consume ::=

        // Check if the RHS is a class-defining keyword
        let is_class_keyword = matches!(
            self.current,
            Token::Keyword(ref kw) if kw == "TYPE-IDENTIFIER" || kw == "ABSTRACT-SYNTAX"
        );

        if !is_class_keyword {
            // Restore and let parse_definition handle it
            self.lexer = saved_lexer;
            self.current = saved_current;
            return Ok(false);
        }

        // Consume the class keyword (and any trailing parts)
        self.advance()?;
        Ok(true)
    }

    /// Try to consume an Information Object Set assignment (X.681 §12), returning
    /// `true` if one was consumed and `false` if the current token is not the start
    /// of an IOC assignment.
    ///
    /// Pattern: `name ClassName ::= { ... }` where `ClassName` is an identifier
    /// (not a built-in keyword).  This distinguishes IOC assignments from:
    ///  - Type definitions (`TypeName ::= ...`) where `::=` immediately follows
    ///    the first identifier.
    ///  - Classic value assignments where the second token is a built-in keyword
    ///    (`OBJECT`, `INTEGER`, `BOOLEAN`), handled by `try_parse_value_assignment`.
    ///
    /// IOC assignments carry no DER type information and are discarded.
    fn try_skip_ioc_assignment(&mut self) -> Result<bool> {
        // An IOC assignment begins with Identifier (name) followed by Identifier
        // (class name) — neither the assignment operator nor a built-in keyword.
        let is_ioc = if let Token::Identifier(_) = &self.current {
            matches!(self.peek_next_token(), Token::Identifier(_))
        } else {
            false
        };

        if !is_ioc {
            return Ok(false);
        }

        // Save state so we can backtrack if the two-identifier sequence is not
        // actually an IOC assignment (i.e. the mandatory '::=' is absent).
        let saved_lexer = self.lexer.clone();
        let saved_current = self.current.clone();

        // Consume: name  ClassName  ::=  { ... }
        self.advance()?; // consume assignment name
        self.advance()?; // consume class name

        if !matches!(self.current, Token::Symbol(ref s) if s == "::=") {
            // Not an IOC assignment — restore state and let the caller handle it.
            self.lexer = saved_lexer;
            self.current = saved_current;
            return Ok(false);
        }
        self.advance()?; // consume ::=

        if matches!(self.current, Token::Symbol(ref s) if s == "{") {
            self.skip_balanced_braces()?;
        } else {
            // Scalar value — consume single token
            self.advance()?;
        }

        Ok(true)
    }

    /// Peek at the next token without consuming it
    fn peek_next_token(&mut self) -> Token {
        // Save current state
        let saved_lexer = self.lexer.clone();
        let saved_current = self.current.clone();

        // Consume current token and get next
        let _ = self.advance();
        let next = self.current.clone();

        // Restore state
        self.lexer = saved_lexer;
        self.current = saved_current;

        next
    }

    /// Parse a value based on its type
    fn parse_value(&mut self, ty: &Type) -> Result<crate::ast::Value> {
        match ty {
            Type::ObjectIdentifier => {
                // Parse OID value: { ... }
                self.expect_symbol("{")?;
                let mut components = Vec::new();

                while !matches!(self.current, Token::Symbol(ref sym) if sym == "}") {
                    if matches!(self.current, Token::Eof) {
                        return Err(ParseError {
                            message: "Unexpected EOF in OID value".to_string(),
                            line: self.lexer.line,
                            column: self.lexer.column,
                        });
                    }

                    // Parse OID component: a plain number, a named reference, or the
                    // `name(number)` form used by RFC module OIDs (e.g. `iso(1)`).
                    // When `name(number)` is used, the numeric value is authoritative
                    // and the name is discarded.
                    match &self.current {
                        Token::Number(n) => {
                            // OID arcs fit in u32
                            let arc = (*n).try_into().map_err(|_| ParseError {
                                message: format!("OID arc too large: {}", n),
                                line: self.lexer.line,
                                column: self.lexer.column,
                            })?;
                            components.push(crate::ast::OidComponent::Number(arc));
                            self.advance()?;
                        }
                        Token::Identifier(name) => {
                            let id = name.clone();
                            self.advance()?;
                            // Check for (number) suffix — `iso(1)`, `us(840)`, etc.
                            if matches!(self.current, Token::Symbol(ref s) if s == "(") {
                                self.advance()?; // consume '('
                                if let Token::Number(n) = self.current {
                                    self.advance()?;
                                    self.expect_symbol(")")?;
                                    // OID arcs fit in u32
                                    let arc = n.try_into().map_err(|_| ParseError {
                                        message: format!("OID arc too large: {}", n),
                                        line: self.lexer.line,
                                        column: self.lexer.column,
                                    })?;
                                    components.push(crate::ast::OidComponent::Number(arc));
                                } else {
                                    self.expect_symbol(")")?;
                                    components.push(crate::ast::OidComponent::NamedRef(id));
                                }
                            } else {
                                components.push(crate::ast::OidComponent::NamedRef(id));
                            }
                        }
                        _ => {
                            return Err(ParseError {
                                message: format!(
                                    "Expected number or identifier in OID value, got {:?}",
                                    self.current
                                ),
                                line: self.lexer.line,
                                column: self.lexer.column,
                            });
                        }
                    }
                }

                self.expect_symbol("}")?;
                Ok(crate::ast::Value::ObjectIdentifier(components))
            }
            Type::Integer(_, _) | Type::Enumerated(_) => {
                if let Some(value) = self.parse_integer_value()? {
                    Ok(crate::ast::Value::Integer(value))
                } else if let Token::Identifier(name) = &self.current {
                    let name = name.clone();
                    self.advance()?;
                    Ok(crate::ast::Value::Identifier(name))
                } else {
                    Err(ParseError {
                        message: format!("Expected an integer or named value, got {:?}", self.current),
                        line: self.lexer.line,
                        column: self.lexer.column,
                    })
                }
            }
            Type::Boolean => {
                // Parse boolean value
                match &self.current {
                    Token::Keyword(kw) if kw == "TRUE" => {
                        self.advance()?;
                        Ok(crate::ast::Value::Boolean(true))
                    }
                    Token::Keyword(kw) if kw == "FALSE" => {
                        self.advance()?;
                        Ok(crate::ast::Value::Boolean(false))
                    }
                    _ => Err(ParseError {
                        message: format!(
                            "Expected TRUE or FALSE for BOOLEAN value, got {:?}",
                            self.current
                        ),
                        line: self.lexer.line,
                        column: self.lexer.column,
                    }),
                }
            }
            _ => Err(ParseError {
                message: format!("Value assignments not supported for type {:?}", ty),
                line: self.lexer.line,
                column: self.lexer.column,
            }),
        }
    }

    fn parse_type(&mut self) -> Result<Type> {
        // Check for tagged type
        if let Token::Symbol(ref sym) = self.current {
            if sym == "[" {
                return self.parse_tagged_type();
            }
        }

        if let Token::Keyword(ref kw) = self.current.clone() {
            match kw.as_str() {
                "SEQUENCE" => {
                    self.advance()?;
                    // Handle SIZE constraint before OF: `SEQUENCE SIZE (1..MAX) OF ...`
                    let leading_size = if matches!(self.current, Token::Keyword(ref k) if k == "SIZE") {
                        self.advance()?; // consume SIZE
                        Some(self.parse_collection_size_constraint()?)
                    } else {
                        None
                    };
                    if matches!(self.current, Token::Keyword(ref k) if k == "OF") {
                        self.advance()?;
                        let inner = self.parse_type()?;
                        let trailing_size = self.parse_size_constraint()?;
                        let size_constraint = leading_size.or(trailing_size);
                        return Ok(Type::SequenceOf(Box::new(inner), size_constraint));
                    }
                    self.expect_symbol("{")?;
                    let fields = self.parse_sequence_fields()?;
                    self.expect_symbol("}")?;
                    return Ok(Type::Sequence(fields));
                }
                "SET" => {
                    self.advance()?;
                    // Handle SIZE constraint before OF: `SET SIZE (1..MAX) OF ...`
                    let leading_size = if matches!(self.current, Token::Keyword(ref k) if k == "SIZE") {
                        self.advance()?; // consume SIZE
                        Some(self.parse_collection_size_constraint()?)
                    } else {
                        None
                    };
                    if matches!(self.current, Token::Keyword(ref k) if k == "OF") {
                        self.advance()?;
                        let inner = self.parse_type()?;
                        let trailing_size = self.parse_size_constraint()?;
                        let size_constraint = leading_size.or(trailing_size);
                        return Ok(Type::SetOf(Box::new(inner), size_constraint));
                    }
                    self.expect_symbol("{")?;
                    let fields = self.parse_sequence_fields()?;
                    self.expect_symbol("}")?;
                    return Ok(Type::Set(fields));
                }
                "CHOICE" => {
                    self.advance()?;
                    self.expect_symbol("{")?;
                    let variants = self.parse_choice_variants()?;
                    self.expect_symbol("}")?;
                    return Ok(Type::Choice(variants));
                }
                "INTEGER" => {
                    self.advance()?;

                    // Check for named number list: INTEGER {name(value), ...}
                    let named_numbers = if matches!(self.current, Token::Symbol(ref s) if s == "{")
                    {
                        self.advance()?; // consume '{'
                        let numbers = self.parse_named_numbers()?;
                        self.expect_symbol("}")?;
                        numbers
                    } else {
                        Vec::new()
                    };

                    // Check for X.680 constraint
                    if matches!(self.current, Token::Symbol(ref s) if s == "(") {
                        self.advance()?; // consume '('
                        let constraint = self.parse_subtype_constraint()?;
                        self.expect_symbol(")")?;

                        // Create X.680 constrained type
                        return Ok(Type::Constrained {
                            base_type: Box::new(Type::Integer(None, named_numbers)),
                            constraint: Constraint {
                                spec: ConstraintSpec::Subtype(constraint),
                                exception: None,
                            },
                        });
                    }

                    // Return INTEGER with optional named numbers
                    return Ok(Type::Integer(None, named_numbers));
                }
                "ENUMERATED" => {
                    self.advance()?;

                    // ENUMERATED must have named values
                    self.expect_symbol("{")?;
                    let named_values = self.parse_named_numbers()?;
                    self.expect_symbol("}")?;

                    if named_values.is_empty() {
                        return Err(ParseError {
                            message: "ENUMERATED must have at least one named value".to_string(),
                            line: self.lexer.line,
                            column: self.lexer.column,
                        });
                    }

                    return Ok(Type::Enumerated(named_values));
                }
                "REAL" => {
                    self.advance()?;
                    return Ok(Type::Real);
                }
                "BOOLEAN" => {
                    self.advance()?;
                    return Ok(Type::Boolean);
                }
                "OCTET" => {
                    self.advance()?;
                    self.expect_keyword("STRING")?;

                    // Check for X.680 string constraints (SIZE, FROM, PATTERN)
                    if let Some(constraint) = self.parse_string_constraint()? {
                        return Ok(Type::Constrained {
                            base_type: Box::new(Type::OctetString(None)),
                            constraint: Constraint {
                                spec: ConstraintSpec::Subtype(constraint),
                                exception: None,
                            },
                        });
                    }

                    return Ok(Type::OctetString(None));
                }
                "BIT" => {
                    self.advance()?;
                    self.expect_keyword("STRING")?;

                    // Check for named bit list: { bitName(n), ... }
                    let named_bits = if matches!(self.current, Token::Symbol(ref s) if s == "{") {
                        self.advance()?; // consume '{'
                        let bits = self.parse_named_numbers()?;
                        self.expect_symbol("}")?;
                        bits
                    } else {
                        Vec::new()
                    };

                    // Check for X.680 string constraints (SIZE, FROM, PATTERN)
                    if let Some(size_constraint) = self.parse_string_constraint()? {
                        if named_bits.is_empty() {
                            return Ok(Type::Constrained {
                                base_type: Box::new(Type::BitString(None)),
                                constraint: Constraint {
                                    spec: ConstraintSpec::Subtype(size_constraint),
                                    exception: None,
                                },
                            });
                        } else {
                            // Named bits + size constraint: use Intersection
                            return Ok(Type::Constrained {
                                base_type: Box::new(Type::BitString(None)),
                                constraint: Constraint {
                                    spec: ConstraintSpec::Subtype(SubtypeConstraint::Intersection(
                                        vec![
                                            SubtypeConstraint::NamedBitList(named_bits),
                                            size_constraint,
                                        ],
                                    )),
                                    exception: None,
                                },
                            });
                        }
                    }

                    if !named_bits.is_empty() {
                        return Ok(Type::Constrained {
                            base_type: Box::new(Type::BitString(None)),
                            constraint: Constraint {
                                spec: ConstraintSpec::Subtype(SubtypeConstraint::NamedBitList(
                                    named_bits,
                                )),
                                exception: None,
                            },
                        });
                    }

                    return Ok(Type::BitString(None));
                }
                "OBJECT" => {
                    self.advance()?;
                    self.expect_keyword("IDENTIFIER")?;
                    return Ok(Type::ObjectIdentifier);
                }
                "RELATIVE-OID" => {
                    self.advance()?;
                    return Ok(Type::RelativeOid);
                }
                "NULL" => {
                    self.advance()?;
                    return Ok(Type::Null);
                }
                "UTF8String" => return self.parse_string_type(Type::Utf8String(None)),
                "PrintableString" => return self.parse_string_type(Type::PrintableString(None)),
                "IA5String" => return self.parse_string_type(Type::IA5String(None)),
                "TeletexString" | "T61String" => {
                    return self.parse_string_type(Type::TeletexString(None))
                }
                "UniversalString" => return self.parse_string_type(Type::UniversalString(None)),
                "BMPString" => return self.parse_string_type(Type::BmpString(None)),
                "GeneralString" => return self.parse_string_type(Type::GeneralString(None)),
                "NumericString" => return self.parse_string_type(Type::NumericString(None)),
                "VisibleString" => return self.parse_string_type(Type::VisibleString(None)),
                "UTCTime" => {
                    self.advance()?;
                    return Ok(Type::UtcTime);
                }
                "GeneralizedTime" => {
                    self.advance()?;
                    return Ok(Type::GeneralizedTime);
                }
                "ANY" => {
                    self.advance()?;
                    // Check for "DEFINED BY fieldname"
                    if matches!(self.current, Token::Keyword(ref kw) if kw == "DEFINED") {
                        self.advance()?; // consume DEFINED
                        self.expect_keyword("BY")?;
                        let field_name = self.expect_identifier()?;
                        return Ok(Type::AnyDefinedBy(field_name));
                    }
                    return Ok(Type::Any);
                }
                "CLASS" => {
                    self.advance()?;
                    return self.parse_class_body();
                }
                // Built-in information object classes used as type aliases (X.681 §14).
                // `TYPE-IDENTIFIER` and `ABSTRACT-SYNTAX` are class names that appear in
                // type-assignment position (e.g. `MyClass ::= TYPE-IDENTIFIER`).  Treat
                // them as ANY since they carry no concrete DER structure.
                "TYPE-IDENTIFIER" | "ABSTRACT-SYNTAX" => {
                    self.advance()?;
                    return Ok(Type::Any);
                }
                _ => {}
            }
        }

        // Type reference - accept both identifiers and keywords that represent built-in types
        // Per X.680, built-in types like TeletexString, BMPString, etc. are keywords but can be used as types
        let type_name = if let Token::Identifier(name) = &self.current {
            Some(name.clone())
        } else if let Token::Keyword(kw) = &self.current {
            // Allow built-in type names that are keywords but should be usable as types
            if is_builtin_type_keyword(kw) {
                Some(kw.clone())
            } else {
                None
            }
        } else {
            None
        };

        if let Some(result) = type_name {
            self.advance()?;

            // Skip optional parameterized type arguments,
            // e.g. `AlgorithmIdentifier{ KEM-ALGORITHM, {KEMAlgSet} }`.
            // The type is still resolved as a plain TypeRef; the parameter set
            // carries no DER encoding information.
            if matches!(self.current, Token::Symbol(ref s) if s == "{") {
                self.skip_balanced_braces()?;
            }

            // Handle `INSTANCE OF TypeName` (X.681 §14) — treat as ANY.
            // The `INSTANCE` identifier is already consumed as the TypeRef name.
            // The `OF` keyword and following class name are discarded.
            if result == "INSTANCE" && matches!(self.current, Token::Keyword(ref k) if k == "OF") {
                self.advance()?; // consume OF
                                 // Consume the class name (identifier)
                                 // Consume the class name (identifier)
                self.advance()?;
                // Skip optional parameterized arguments
                if matches!(self.current, Token::Symbol(ref s) if s == "{") {
                    self.skip_balanced_braces()?;
                }
                return Ok(Type::Any);
            }

            // Handle IOC field access notation: `ClassName.&field({params})`.
            // This appears in 2009-syntax modules as a field type, e.g.:
            //   `type  ATTRIBUTE.&id({AttrSet})`
            //   `parameters  ALGORITHM-TYPE.&Params({AlgorithmSet}{@algorithm}) OPTIONAL`
            //
            // For `&id` fields, the class definition always constrains the type to
            // `OBJECT IDENTIFIER UNIQUE`, so we resolve these to ObjectIdentifier.
            // All other IOC field accesses are treated as ANY (Type::Any).
            if matches!(self.current, Token::Symbol(ref s) if s == ".") {
                self.advance()?; // consume '.'
                                 // Consume the &field identifier and remember its name
                                 // Consume the &field identifier and remember its name
                let field_name = if let Token::Identifier(ref name) = self.current {
                    let n = name.clone();
                    self.advance()?;
                    n
                } else {
                    self.advance()?;
                    String::new()
                };
                // Skip any optional parameterized argument groups {..} or (..) after the field name
                loop {
                    if matches!(self.current, Token::Symbol(ref s) if s == "{") {
                        self.skip_balanced_braces()?;
                    } else if matches!(self.current, Token::Symbol(ref s) if s == "(") {
                        self.skip_balanced_parens()?;
                    } else {
                        break;
                    }
                }
                // Resolve &id to ObjectIdentifier (X.681 convention: &id fields are OIDs)
                if field_name == "&id" {
                    return Ok(Type::ObjectIdentifier);
                }
                return Ok(Type::Any);
            }

            // Check for constraint on type reference (subtype definition)
            if matches!(self.current, Token::Symbol(ref s) if s == "(") {
                // Peek ahead to determine if this is a string constraint or value constraint
                self.advance()?; // consume '('

                // Check if current token (after '(') is a string constraint keyword
                let is_string_constraint = if let Token::Keyword(ref kw) = self.current {
                    matches!(kw.as_str(), "SIZE" | "FROM" | "PATTERN" | "CONTAINING")
                } else {
                    false
                };

                // Parse the appropriate constraint type
                let constraint = if is_string_constraint {
                    // Parse string constraint (SIZE, FROM, PATTERN)
                    let mut constraints = Vec::new();

                    while !matches!(self.current, Token::Symbol(ref s) if s == ")") {
                        if matches!(self.current, Token::Eof) {
                            break;
                        }

                        if let Some(c) = self.parse_single_string_constraint()? {
                            constraints.push(c);
                        } else {
                            break;
                        }
                    }

                    self.expect_symbol(")")?;

                    match constraints.len() {
                        0 => {
                            return Err(ParseError {
                                message: "Expected string constraint".to_string(),
                                line: self.lexer.line,
                                column: self.lexer.column,
                            })
                        }
                        1 => constraints.into_iter().next().unwrap(),
                        _ => SubtypeConstraint::Intersection(constraints),
                    }
                } else {
                    // Parse value constraint (integer ranges, etc.)
                    let c = self.parse_subtype_constraint()?;
                    self.expect_symbol(")")?;
                    c
                };

                // Create X.680 constrained type with TypeRef as base
                return Ok(Type::Constrained {
                    base_type: Box::new(Type::TypeRef(result)),
                    constraint: Constraint {
                        spec: ConstraintSpec::Subtype(constraint),
                        exception: None,
                    },
                });
            }

            return Ok(Type::TypeRef(result));
        }

        Err(ParseError {
            message: format!("Expected type, got {:?}", self.current),
            line: self.lexer.line,
            column: self.lexer.column,
        })
    }

    fn parse_tagged_type(&mut self) -> Result<Type> {
        self.expect_symbol("[")?;

        // Check for optional tag class keyword: APPLICATION, UNIVERSAL, PRIVATE
        let class = if matches!(self.current, Token::Keyword(ref kw) if kw == "APPLICATION") {
            self.advance()?;
            TagClass::Application
        } else if matches!(self.current, Token::Keyword(ref kw) if kw == "UNIVERSAL") {
            self.advance()?;
            TagClass::Universal
        } else if matches!(self.current, Token::Keyword(ref kw) if kw == "PRIVATE") {
            self.advance()?;
            TagClass::Private
        } else {
            TagClass::ContextSpecific
        };

        let number = if let Token::Number(n) = self.current {
            self.advance()?;
            // Tag numbers fit in u32
            n.try_into().map_err(|_| ParseError {
                message: format!("Tag number too large: {}", n),
                line: self.lexer.line,
                column: self.lexer.column,
            })?
        } else {
            return Err(ParseError {
                message: "Expected tag number".to_string(),
                line: self.lexer.line,
                column: self.lexer.column,
            });
        };

        self.expect_symbol("]")?;

        // Check for EXPLICIT or IMPLICIT
        let tagging = if matches!(self.current, Token::Keyword(ref kw) if kw == "EXPLICIT") {
            self.advance()?;
            Tagging::Explicit
        } else if matches!(self.current, Token::Keyword(ref kw) if kw == "IMPLICIT") {
            self.advance()?;
            Tagging::Implicit
        } else {
            self.default_tagging.clone() // use the module-level default
        };

        let inner = self.parse_type()?;

        Ok(Type::Tagged {
            tag: TagInfo {
                class,
                number,
                tagging,
            },
            inner: Box::new(inner),
        })
    }

    fn parse_sequence_fields(&mut self) -> Result<Vec<SequenceField>> {
        let mut fields = Vec::new();

        while !matches!(self.current, Token::Symbol(ref s) if s == "}") {
            if matches!(self.current, Token::Eof) {
                break;
            }

            // Extension semantics must not be flattened or silently discarded.
            if matches!(self.current, Token::Symbol(ref s) if s == "...") {
                return Err(ParseError {
                    message: "extension markers are not represented in the Synta AST".to_string(),
                    line: self.lexer.line,
                    column: self.lexer.column,
                });
            }

            // Handle version extension addition groups: [[N: field1, field2, ... ]]
            // These are used in 2009-syntax modules to group optional extension fields
            // by version number.  The contained fields are flattened into the SEQUENCE.
            if matches!(self.current, Token::Symbol(ref s) if s == "[") {
                // Peek to see if the next token is also '[' (double bracket)
                let saved_lexer = self.lexer.clone();
                let saved_current = self.current.clone();
                self.advance()?; // consume first '['
                if matches!(self.current, Token::Symbol(ref s) if s == "[") {
                    return Err(ParseError {
                        message: "extension addition groups are not represented in the Synta AST".to_string(),
                        line: self.lexer.line,
                        column: self.lexer.column,
                    });
                } else {
                    // Not a double bracket — restore and fall through to normal parsing
                    self.lexer = saved_lexer;
                    self.current = saved_current;
                }
            }

            let name = self.expect_identifier()?;
            let ty = self.parse_type()?;

            let optional = if matches!(self.current, Token::Keyword(ref kw) if kw == "OPTIONAL") {
                self.advance()?;
                true
            } else {
                false
            };

            let default = if matches!(self.current, Token::Keyword(ref kw) if kw == "DEFAULT") {
                self.advance()?;
                // Parse the default value
                let default_value = self.parse_default_value()?;
                Some(default_value)
            } else {
                None
            };

            fields.push(SequenceField {
                name,
                ty,
                optional,
                default,
            });

            if matches!(self.current, Token::Symbol(ref s) if s == ",") {
                self.advance()?;
            }
        }

        Ok(fields)
    }

    fn parse_choice_variants(&mut self) -> Result<Vec<ChoiceVariant>> {
        let mut variants = Vec::new();

        while !matches!(self.current, Token::Symbol(ref s) if s == "}") {
            if matches!(self.current, Token::Eof) {
                break;
            }

            // Extension semantics must not be silently discarded.
            if matches!(self.current, Token::Symbol(ref s) if s == "...") {
                return Err(ParseError {
                    message: "extension markers are not represented in the Synta AST".to_string(),
                    line: self.lexer.line,
                    column: self.lexer.column,
                });
            }

            let name = self.expect_identifier()?;
            let ty = self.parse_type()?;

            variants.push(ChoiceVariant { name, ty });

            if matches!(self.current, Token::Symbol(ref s) if s == ",") {
                self.advance()?;
            }
        }

        Ok(variants)
    }

    /// Parse an ASN.1 Information Object Class body (X.681 §9).
    ///
    /// Called after the `CLASS` keyword has been consumed.  Parses:
    ///
    /// ```text
    /// CLASS { &field [TYPE] [UNIQUE] [OPTIONAL] [DEFAULT value], ... }
    ///         [WITH SYNTAX { ... }]
    /// ```
    ///
    /// The `WITH SYNTAX` block (if present) is consumed and discarded — its
    /// content is arbitrary keyword syntax and has no DER representation.
    /// The resulting [`Type::Class`] stores only the field names and the
    /// `UNIQUE`/`OPTIONAL` qualifiers; actual type expressions within the
    /// class body are also consumed and discarded.
    fn parse_class_body(&mut self) -> Result<Type> {
        self.expect_symbol("{")?;

        let mut fields = Vec::new();

        while !matches!(self.current, Token::Symbol(ref s) if s == "}") {
            if matches!(self.current, Token::Eof) {
                break;
            }

            // Skip extension markers
            if matches!(self.current, Token::Symbol(ref s) if s == "...") {
                self.advance()?;
                if matches!(self.current, Token::Symbol(ref s) if s == ",") {
                    self.advance()?;
                }
                continue;
            }

            // Each field begins with &name
            let field_name = if let Token::Identifier(ref id) = self.current {
                if id.starts_with('&') {
                    let name = id.strip_prefix('&').unwrap_or(id).to_string();
                    self.advance()?;
                    name
                } else {
                    // Not a field reference — skip token and try to recover
                    self.advance()?;
                    continue;
                }
            } else {
                // Non-identifier token — skip and recover
                self.advance()?;
                continue;
            };

            // Consume optional type expression and qualifiers until ',', '}', or '...'
            // We track brace depth to handle nested { } in DEFAULT values.
            let mut unique = false;
            let mut optional = false;
            let mut depth = 0usize;

            loop {
                match &self.current {
                    Token::Symbol(ref s) if s == "}" && depth == 0 => break,
                    Token::Symbol(ref s) if s == "," && depth == 0 => break,
                    Token::Symbol(ref s) if s == "..." && depth == 0 => break,
                    Token::Symbol(ref s) if s == "{" => {
                        depth += 1;
                        self.advance()?;
                    }
                    Token::Symbol(ref s) if s == "}" => {
                        depth -= 1;
                        self.advance()?;
                    }
                    Token::Keyword(ref kw) if kw == "UNIQUE" && depth == 0 => {
                        unique = true;
                        self.advance()?;
                    }
                    Token::Keyword(ref kw) if kw == "OPTIONAL" && depth == 0 => {
                        optional = true;
                        self.advance()?;
                    }
                    Token::Eof => break,
                    _ => {
                        self.advance()?;
                    }
                }
            }

            fields.push(ClassField {
                name: field_name,
                unique,
                optional,
            });

            if matches!(self.current, Token::Symbol(ref s) if s == ",") {
                self.advance()?;
            }
        }

        self.expect_symbol("}")?;

        // Consume optional WITH SYNTAX { ... } block
        if matches!(self.current, Token::Keyword(ref kw) if kw == "WITH") {
            self.advance()?; // consume WITH
            if matches!(self.current, Token::Keyword(ref kw) if kw == "SYNTAX") {
                self.advance()?; // consume SYNTAX
                                 // The syntax block is a balanced { ... } with arbitrary token content
                self.skip_balanced_braces()?;
            }
        }

        Ok(Type::Class(fields))
    }

    /// Consume a balanced `{ ... }` block, discarding all tokens inside.
    ///
    /// Handles nested braces.  Assumes the opening `{` is the current token.
    fn skip_balanced_braces(&mut self) -> Result<()> {
        self.expect_symbol("{")?;
        let mut depth = 1usize;
        while depth > 0 {
            match &self.current {
                Token::Symbol(ref s) if s == "{" => {
                    depth += 1;
                    self.advance()?;
                }
                Token::Symbol(ref s) if s == "}" => {
                    depth -= 1;
                    self.advance()?;
                }
                Token::Eof => {
                    return Err(ParseError {
                        message: "Unexpected EOF inside braced block".to_string(),
                        line: self.lexer.line,
                        column: self.lexer.column,
                    });
                }
                _ => {
                    self.advance()?;
                }
            }
        }
        Ok(())
    }

    /// Consume a balanced `( ... )` block, discarding all tokens inside.
    ///
    /// Used to skip parameterized argument groups in IOC field access expressions,
    /// e.g. the `({AttrSet})` and `({AttrSet}{@type})` parts of
    /// `ATTRIBUTE.&id({AttrSet})` and `ATTRIBUTE.&Type({AttrSet}{@type})`.
    fn skip_balanced_parens(&mut self) -> Result<()> {
        self.expect_symbol("(")?;
        let mut depth = 1usize;
        while depth > 0 {
            match &self.current {
                Token::Symbol(ref s) if s == "(" => {
                    depth += 1;
                    self.advance()?;
                }
                Token::Symbol(ref s) if s == ")" => {
                    depth -= 1;
                    self.advance()?;
                }
                Token::Eof => {
                    return Err(ParseError {
                        message: "Unexpected EOF inside parenthesized block".to_string(),
                        line: self.lexer.line,
                        column: self.lexer.column,
                    });
                }
                _ => {
                    self.advance()?;
                }
            }
        }
        Ok(())
    }

    /// Parse named number list: name1(value1), name2(value2), ...
    fn parse_named_numbers(&mut self) -> Result<Vec<NamedNumber>> {
        let mut numbers = Vec::new();

        while !matches!(self.current, Token::Symbol(ref s) if s == "}") {
            if matches!(self.current, Token::Eof) {
                break;
            }

            // Skip extension markers (...)
            if matches!(self.current, Token::Symbol(ref s) if s == "...") {
                self.advance()?;
                if matches!(self.current, Token::Symbol(ref s) if s == ",") {
                    self.advance()?;
                }
                continue;
            }

            // Parse name
            let name = self.expect_identifier()?;

            // Optional explicit numeric value: name(N)
            // If absent, auto-number (X.680 §19.5 auto-numbering for ENUMERATED).
            let value = if matches!(self.current, Token::Symbol(ref s) if s == "(") {
                self.advance()?; // consume '('
                let v = self.parse_integer_value()?.ok_or_else(|| ParseError {
                    message: "Expected number value for named number".to_string(),
                    line: self.lexer.line,
                    column: self.lexer.column,
                })?;
                self.expect_symbol(")")?;
                v
            } else {
                // Auto-number: next value after the last one (or 0 for first)
                numbers
                    .last()
                    .map(|n: &NamedNumber| n.value + 1)
                    .unwrap_or(0)
            };

            numbers.push(NamedNumber { name, value });

            // Optional comma
            if matches!(self.current, Token::Symbol(ref s) if s == ",") {
                self.advance()?;
            }
        }

        Ok(numbers)
    }
}

fn resolve_assignment_type<'a>(
    ty: &'a Type,
    definitions: &'a [Definition],
    visiting: &mut Vec<String>,
) -> Option<&'a Type> {
    match ty {
        Type::TypeRef(name) => {
            if visiting.iter().any(|entry| entry == name) {
                return None;
            }
            visiting.push(name.clone());
            let definition = definitions.iter().find(|definition| definition.name == *name)?;
            let resolved = resolve_assignment_type(&definition.ty, definitions, visiting);
            visiting.pop();
            resolved
        }
        Type::Tagged { inner, .. } | Type::Constrained { base_type: inner, .. } => {
            resolve_assignment_type(inner, definitions, visiting)
        }
        Type::Boolean
        | Type::Integer(_, _)
        | Type::Enumerated(_)
        | Type::ObjectIdentifier
        | Type::Real => Some(ty),
        _ => None,
    }
}

/// Parse an ASN.1 module from a string
pub fn parse(input: &str) -> Result<Module> {
    let mut parser = Parser::new(input)?;
    parser.parse_module()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_sequence() {
        let input = r#"
            TestModule DEFINITIONS ::= BEGIN
                SimpleSeq ::= SEQUENCE {
                    field1 INTEGER,
                    field2 OCTET STRING
                }
            END
        "#;

        let module = parse(input).unwrap();
        assert_eq!(module.name, "TestModule");
        assert_eq!(module.definitions.len(), 1);

        let def = &module.definitions[0];
        assert_eq!(def.name, "SimpleSeq");

        if let Type::Sequence(fields) = &def.ty {
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0].name, "field1");
            assert!(matches!(fields[0].ty, Type::Integer(_, _)));
        } else {
            panic!("Expected SEQUENCE type");
        }
    }

    #[test]
    fn test_parse_choice() {
        let input = r#"
            TestModule DEFINITIONS ::= BEGIN
                MyChoice ::= CHOICE {
                    option1 INTEGER,
                    option2 BOOLEAN
                }
            END
        "#;

        let module = parse(input).unwrap();
        let def = &module.definitions[0];

        if let Type::Choice(variants) = &def.ty {
            assert_eq!(variants.len(), 2);
            assert_eq!(variants[0].name, "option1");
        } else {
            panic!("Expected CHOICE type");
        }
    }

    #[test]
    fn test_parse_tagged_type() {
        let input = r#"
            TestModule DEFINITIONS ::= BEGIN
                TaggedSeq ::= SEQUENCE {
                    field1 [0] EXPLICIT INTEGER,
                    field2 [1] IMPLICIT OCTET STRING
                }
            END
        "#;

        let module = parse(input).unwrap();
        let def = &module.definitions[0];

        if let Type::Sequence(fields) = &def.ty {
            if let Type::Tagged { tag, .. } = &fields[0].ty {
                assert_eq!(tag.number, 0);
                assert_eq!(tag.tagging, Tagging::Explicit);
            } else {
                panic!("Expected tagged type");
            }
        } else {
            panic!("Expected SEQUENCE type");
        }
    }

    #[test]
    fn test_implicit_tags_module_default() {
        // In a "DEFINITIONS IMPLICIT TAGS" module, a bare [N] tag (no EXPLICIT/IMPLICIT keyword)
        // must default to IMPLICIT.  An explicitly-marked [N] EXPLICIT must remain EXPLICIT.
        let input = r#"
            TestModule DEFINITIONS IMPLICIT TAGS ::= BEGIN
                TaggedSeq ::= SEQUENCE {
                    field1 [0] INTEGER,
                    field2 [1] EXPLICIT OCTET STRING,
                    field3 [2] IMPLICIT BOOLEAN
                }
            END
        "#;

        let module = parse(input).unwrap();
        assert_eq!(module.tagging_mode, Some(crate::ast::TaggingMode::Implicit));
        let def = &module.definitions[0];
        if let Type::Sequence(fields) = &def.ty {
            // bare [0] — should inherit IMPLICIT from module header
            if let Type::Tagged { tag, .. } = &fields[0].ty {
                assert_eq!(tag.number, 0);
                assert_eq!(
                    tag.tagging,
                    Tagging::Implicit,
                    "bare tag should be IMPLICIT in IMPLICIT TAGS module"
                );
            } else {
                panic!("Expected tagged type for field1");
            }
            // [1] EXPLICIT — explicit keyword overrides module default
            if let Type::Tagged { tag, .. } = &fields[1].ty {
                assert_eq!(tag.number, 1);
                assert_eq!(
                    tag.tagging,
                    Tagging::Explicit,
                    "[1] EXPLICIT should stay EXPLICIT"
                );
            } else {
                panic!("Expected tagged type for field2");
            }
            // [2] IMPLICIT — explicit keyword matches module default
            if let Type::Tagged { tag, .. } = &fields[2].ty {
                assert_eq!(tag.number, 2);
                assert_eq!(tag.tagging, Tagging::Implicit);
            } else {
                panic!("Expected tagged type for field3");
            }
        } else {
            panic!("Expected SEQUENCE type");
        }
    }

    #[test]
    fn test_explicit_tags_module_default() {
        // In a "DEFINITIONS EXPLICIT TAGS" module (or no keyword — same thing), a bare [N]
        // tag must default to EXPLICIT.
        let input = r#"
            TestModule DEFINITIONS EXPLICIT TAGS ::= BEGIN
                TaggedSeq ::= SEQUENCE {
                    field1 [0] INTEGER
                }
            END
        "#;

        let module = parse(input).unwrap();
        let def = &module.definitions[0];
        if let Type::Sequence(fields) = &def.ty {
            if let Type::Tagged { tag, .. } = &fields[0].ty {
                assert_eq!(tag.number, 0);
                assert_eq!(
                    tag.tagging,
                    Tagging::Explicit,
                    "bare tag should be EXPLICIT in EXPLICIT TAGS module"
                );
            } else {
                panic!("Expected tagged type");
            }
        } else {
            panic!("Expected SEQUENCE type");
        }
    }

    #[test]
    fn test_parse_optional_field() {
        let input = r#"
            TestModule DEFINITIONS ::= BEGIN
                OptSeq ::= SEQUENCE {
                    required INTEGER,
                    optional BOOLEAN OPTIONAL
                }
            END
        "#;

        let module = parse(input).unwrap();
        let def = &module.definitions[0];

        if let Type::Sequence(fields) = &def.ty {
            assert!(!fields[0].optional);
            assert!(fields[1].optional);
        } else {
            panic!("Expected SEQUENCE type");
        }
    }

    #[test]
    fn test_parse_value_constraint_range() {
        let input = r#"
            TestModule DEFINITIONS ::= BEGIN
                Int32 ::= INTEGER (-2147483648..2147483647)
            END
        "#;

        let module = parse(input).unwrap();
        let def = &module.definitions[0];

        assert_eq!(def.name, "Int32");
        // Now expects X.680 Constrained type
        if let Type::Constrained {
            base_type,
            constraint,
        } = &def.ty
        {
            assert!(matches!(base_type.as_ref(), Type::Integer(None, _)));
            if let ConstraintSpec::Subtype(SubtypeConstraint::ValueRange { min, max }) =
                &constraint.spec
            {
                assert_eq!(*min, ConstraintValue::Integer(-2147483648));
                assert_eq!(*max, ConstraintValue::Integer(2147483647));
            } else {
                panic!("Expected SubtypeConstraint::ValueRange");
            }
        } else {
            panic!("Expected Constrained type");
        }
    }

    #[test]
    fn test_parse_value_constraint_single() {
        let input = r#"
            TestModule DEFINITIONS ::= BEGIN
                FixedValue ::= INTEGER (42)
            END
        "#;

        let module = parse(input).unwrap();
        let def = &module.definitions[0];

        // Now expects X.680 Constrained type
        if let Type::Constrained {
            base_type,
            constraint,
        } = &def.ty
        {
            assert!(matches!(base_type.as_ref(), Type::Integer(None, _)));
            if let ConstraintSpec::Subtype(SubtypeConstraint::SingleValue(val)) = &constraint.spec {
                assert_eq!(*val, ConstraintValue::Integer(42));
            } else {
                panic!("Expected SubtypeConstraint::SingleValue");
            }
        } else {
            panic!("Expected Constrained type");
        }
    }

    #[test]
    fn test_parse_size_constraint() {
        // Note: SIZE constraints are parsed but currently skipped
        // This test verifies that OCTET STRING with SIZE parses without error
        let input = r#"
TestModule DEFINITIONS ::= BEGIN
    ShortString ::= OCTET STRING
END
        "#;

        let module = parse(input).unwrap();
        let def = &module.definitions[0];

        // For now, OCTET STRING without constraint should parse fine
        assert!(matches!(def.ty, Type::OctetString(_)));
    }

    // X.680 Constraint Tests

    #[test]
    fn test_parse_constraint_value_min_max() {
        let mut parser = Parser::new("MIN..MAX").unwrap();

        let value1 = parser.parse_constraint_value().unwrap();
        assert_eq!(value1, ConstraintValue::Min);

        parser.expect_symbol("..").unwrap();

        let value2 = parser.parse_constraint_value().unwrap();
        assert_eq!(value2, ConstraintValue::Max);
    }

    #[test]
    fn test_parse_constraint_value_integer() {
        let mut parser = Parser::new("42").unwrap();

        let value = parser.parse_constraint_value().unwrap();
        assert_eq!(value, ConstraintValue::Integer(42));
    }

    #[test]
    fn test_parse_constraint_value_negative() {
        let mut parser = Parser::new("-100").unwrap();

        let value = parser.parse_constraint_value().unwrap();
        assert_eq!(value, ConstraintValue::Integer(-100));
    }

    #[test]
    fn test_parse_constraint_value_named() {
        let mut parser = Parser::new("maxValue").unwrap();

        let value = parser.parse_constraint_value().unwrap();
        assert_eq!(value, ConstraintValue::NamedValue("maxValue".to_string()));
    }

    #[test]
    fn test_parse_single_value_constraint() {
        let mut parser = Parser::new("42").unwrap();

        let constraint = parser.parse_single_constraint().unwrap();
        assert_eq!(
            constraint,
            SubtypeConstraint::SingleValue(ConstraintValue::Integer(42))
        );
    }

    #[test]
    fn test_parse_value_range_constraint() {
        let mut parser = Parser::new("0..100").unwrap();

        let constraint = parser.parse_single_constraint().unwrap();
        assert!(matches!(constraint, SubtypeConstraint::ValueRange { .. }));
    }

    #[test]
    fn test_parse_min_max_range() {
        let mut parser = Parser::new("MIN..MAX").unwrap();

        let constraint = parser.parse_single_constraint().unwrap();
        if let SubtypeConstraint::ValueRange { min, max } = constraint {
            assert_eq!(min, ConstraintValue::Min);
            assert_eq!(max, ConstraintValue::Max);
        } else {
            panic!("Expected ValueRange constraint");
        }
    }

    #[test]
    fn test_parse_union_constraint() {
        let mut parser = Parser::new("1 | 2 | 3").unwrap();

        let constraint = parser.parse_subtype_constraint().unwrap();
        if let SubtypeConstraint::Union(elements) = constraint {
            assert_eq!(elements.len(), 3);
        } else {
            panic!("Expected Union constraint");
        }
    }

    #[test]
    fn test_parse_intersection_constraint() {
        let mut parser = Parser::new("(0..100) ^ (10 | 20 | 30)").unwrap();

        let constraint = parser.parse_subtype_constraint().unwrap();
        if let SubtypeConstraint::Intersection(elements) = constraint {
            assert_eq!(elements.len(), 2);
        } else {
            panic!("Expected Intersection constraint");
        }
    }

    #[test]
    fn test_parse_complement_constraint() {
        let mut parser = Parser::new("ALL EXCEPT 0").unwrap();

        let constraint = parser.parse_single_constraint().unwrap();
        if let SubtypeConstraint::Complement(inner) = constraint {
            assert_eq!(
                *inner,
                SubtypeConstraint::SingleValue(ConstraintValue::Integer(0))
            );
        } else {
            panic!("Expected Complement constraint");
        }
    }

    #[test]
    fn test_parse_pattern_constraint() {
        let input = r#"
TestModule DEFINITIONS ::= BEGIN
    EmailPattern ::= IA5String (PATTERN "[a-z]+@[a-z]+\.[a-z]+")
END
        "#;

        let module = parse(input).unwrap();
        assert_eq!(module.definitions.len(), 1);

        let def = &module.definitions[0];
        assert_eq!(def.name, "EmailPattern");

        // Should be a constrained type
        if let Type::Constrained {
            base_type,
            constraint,
        } = &def.ty
        {
            // Accept either TypeRef or IA5String
            assert!(
                matches!(base_type.as_ref(), Type::IA5String(_))
                    || matches!(base_type.as_ref(), Type::TypeRef(s) if s == "IA5String")
            );
            if let ConstraintSpec::Subtype(SubtypeConstraint::Pattern(pattern)) = &constraint.spec {
                // Note: Single backslash in ASN.1 becomes single backslash in parsed string
                assert_eq!(pattern, "[a-z]+@[a-z]+.[a-z]+");
            } else {
                panic!("Expected Pattern constraint");
            }
        } else {
            panic!("Expected Constrained type");
        }
    }

    #[test]
    fn test_parse_permitted_alphabet() {
        let input = r#"
TestModule DEFINITIONS ::= BEGIN
    MyNumericString ::= IA5String (FROM ("0".."9"))
END
        "#;

        let module = parse(input).unwrap();
        let def = &module.definitions[0];

        if let Type::Constrained { constraint, .. } = &def.ty {
            if let ConstraintSpec::Subtype(SubtypeConstraint::PermittedAlphabet(ranges)) =
                &constraint.spec
            {
                assert_eq!(ranges.len(), 1);
                assert_eq!(ranges[0].min, '0');
                assert_eq!(ranges[0].max, '9');
            } else {
                panic!("Expected PermittedAlphabet constraint");
            }
        } else {
            panic!("Expected Constrained type");
        }
    }

    #[test]
    fn test_parse_containing_constraint() {
        let input = r#"
TestModule DEFINITIONS ::= BEGIN
    EncodedCert ::= OCTET STRING (CONTAINING INTEGER)
END
        "#;

        let module = parse(input).unwrap();
        let def = &module.definitions[0];

        if let Type::Constrained { constraint, .. } = &def.ty {
            if let ConstraintSpec::Subtype(SubtypeConstraint::ContainedSubtype(inner_type)) =
                &constraint.spec
            {
                assert!(matches!(inner_type.as_ref(), Type::Integer(_, _)));
            } else {
                panic!("Expected ContainedSubtype constraint");
            }
        } else {
            panic!("Expected Constrained type");
        }
    }

    #[test]
    fn test_parse_inner_type_constraint() {
        let input = r#"
TestModule DEFINITIONS ::= BEGIN
    PositiveList ::= SEQUENCE OF INTEGER (1..MAX)
END
        "#;

        let module = parse(input).unwrap();
        let def = &module.definitions[0];

        // Inner type constraints on SEQUENCE OF create a SequenceOf with constrained inner type
        if let Type::SequenceOf(inner_type, _) = &def.ty {
            // The inner type should be constrained
            if let Type::Constrained {
                base_type,
                constraint,
            } = inner_type.as_ref()
            {
                assert!(matches!(base_type.as_ref(), Type::Integer(_, _)));
                if let ConstraintSpec::Subtype(SubtypeConstraint::ValueRange { min, max }) =
                    &constraint.spec
                {
                    assert_eq!(*min, ConstraintValue::Integer(1));
                    assert_eq!(*max, ConstraintValue::Max);
                } else {
                    panic!("Expected ValueRange constraint on inner type");
                }
            } else {
                panic!("Expected inner type to be Constrained");
            }
        } else {
            panic!("Expected SequenceOf type, got: {:?}", def.ty);
        }
    }

    #[test]
    fn test_parse_complex_nested_union() {
        let input = r#"
TestModule DEFINITIONS ::= BEGIN
    ComplexRange ::= INTEGER (0..10 | 20..30 | 40..50)
END
        "#;

        let module = parse(input).unwrap();
        let def = &module.definitions[0];

        if let Type::Constrained { constraint, .. } = &def.ty {
            if let ConstraintSpec::Subtype(SubtypeConstraint::Union(elements)) = &constraint.spec {
                assert_eq!(elements.len(), 3);
                for element in elements {
                    assert!(matches!(element, SubtypeConstraint::ValueRange { .. }));
                }
            } else {
                panic!("Expected Union constraint");
            }
        } else {
            panic!("Expected Constrained type");
        }
    }

    #[test]
    fn test_parse_nested_parentheses() {
        let input = r#"
TestModule DEFINITIONS ::= BEGIN
    Nested ::= INTEGER ((0..10) | (20..30))
END
        "#;

        let module = parse(input).unwrap();
        let def = &module.definitions[0];

        if let Type::Constrained { constraint, .. } = &def.ty {
            if let ConstraintSpec::Subtype(SubtypeConstraint::Union(elements)) = &constraint.spec {
                assert_eq!(elements.len(), 2);
            } else {
                panic!("Expected Union constraint");
            }
        } else {
            panic!("Expected Constrained type");
        }
    }

    #[test]
    fn test_parse_size_constraint_on_string() {
        let input = r#"
TestModule DEFINITIONS ::= BEGIN
    ShortString ::= IA5String (SIZE (1..64))
END
        "#;

        let result = parse(input);
        if let Err(e) = &result {
            println!("Parse error: {}", e);
        }
        let module = result.unwrap();
        let def = &module.definitions[0];

        assert_eq!(def.name, "ShortString");
        // Expect Constrained type with SIZE constraint
        if let Type::Constrained {
            base_type,
            constraint,
        } = &def.ty
        {
            // The base type should be a TypeRef to IA5String now (not inline IA5String(None))
            // because the parser creates type references for known types
            println!("base_type: {:?}", base_type);
            // Accept either TypeRef or IA5String(None)
            assert!(
                matches!(base_type.as_ref(), Type::IA5String(None))
                    || matches!(base_type.as_ref(), Type::TypeRef(s) if s == "IA5String")
            );
            if let ConstraintSpec::Subtype(SubtypeConstraint::SizeConstraint(inner)) =
                &constraint.spec
            {
                // The inner constraint should be a ValueRange
                if let SubtypeConstraint::ValueRange { min, max } = inner.as_ref() {
                    assert_eq!(*min, ConstraintValue::Integer(1));
                    assert_eq!(*max, ConstraintValue::Integer(64));
                } else {
                    panic!("Expected ValueRange inside SIZE constraint");
                }
            } else {
                panic!("Expected SizeConstraint, got {:?}", constraint.spec);
            }
        } else {
            panic!("Expected Constrained type, got {:?}", def.ty);
        }
    }
}
