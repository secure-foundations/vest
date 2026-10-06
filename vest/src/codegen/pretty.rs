//! Pretty-printing of the generated Rust and Verus code.
//!
//! The generator assembles its output from strings and `quote!` fragments whose
//! spacing and line structure are incidental. [`format_items`] lays such text
//! out again from its tokens alone, in the style of rustfmt: spacing follows
//! from each token and its neighbours, and line breaks from a Wadler-style
//! document fitted to [`WIDTH`] columns. Formatting takes time linear in the
//! output, so it keeps up with generated files that `verusfmt` cannot format.
//!
//! Blank lines between items and statements are kept from the input, where the
//! generator places them deliberately. Line comments are kept only between
//! items: the formatted text is split at comment lines, and each part must be a
//! sequence of complete items.

use std::str::FromStr;

use proc_macro2::{Delimiter, Spacing, TokenStream, TokenTree};

/// Maximum line width, as in rustfmt.
const WIDTH: usize = 100;
const INDENT: usize = 4;

/// Formats a sequence of items (or statements), indented by `indent` levels.
///
/// Text that does not tokenize is returned unchanged, so a formatting bug
/// cannot corrupt the generated code.
pub(crate) fn format_items(src: &str, indent: usize) -> String {
    // Split the text into comment lines and code between them, noting which
    // segments a blank line precedes.
    let mut segments: Vec<(bool, String, bool)> = Vec::new(); // (is_code, text, blank_before)
    let mut chunk = String::new();
    let mut chunk_blank_before = false;
    let mut blank = false;
    let mut last_blank = false;
    for line in src.lines() {
        let trimmed = line.trim_start();
        if trimmed.is_empty() {
            blank = true;
            last_blank = true;
            if !chunk.is_empty() {
                chunk.push('\n');
            }
            continue;
        }
        let is_comment =
            trimmed.starts_with("//") && !trimmed.starts_with("///") && !trimmed.starts_with("//!");
        if is_comment {
            if !chunk.is_empty() {
                segments.push((true, std::mem::take(&mut chunk), chunk_blank_before));
            }
            segments.push((false, trimmed.to_string(), last_blank));
            blank = false;
        } else {
            if chunk.is_empty() {
                chunk_blank_before = blank;
                blank = false;
            }
            chunk.push_str(line);
            chunk.push('\n');
        }
        last_blank = false;
    }
    if !chunk.is_empty() {
        segments.push((true, chunk, chunk_blank_before));
    }

    let mut out = String::new();
    for (is_code, text, blank_before) in segments {
        if !out.is_empty() && blank_before {
            out.push('\n');
        }
        if is_code {
            let formatted = format_chunk(&text, indent).unwrap_or(text);
            out.push_str(formatted.trim_end_matches('\n'));
        } else {
            out.push_str(&" ".repeat(indent * INDENT));
            out.push_str(&text);
        }
        out.push('\n');
    }
    out
}

fn format_chunk(src: &str, indent: usize) -> Option<String> {
    let stream = TokenStream::from_str(src).ok()?;
    let trees = structure(lower(stream));
    let doc = Printer.items(&trees, Context::Items);
    let mut out = " ".repeat(indent * INDENT);
    out.push_str(&render(&nest(indent * INDENT, doc), indent * INDENT));
    out.push('\n');
    Some(out)
}

// ============================================================
// Token trees
// ============================================================

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tok {
    Ident(String),
    Lifetime(String),
    Lit(String),
    /// A punctuation token: a single character or a multi-character operator.
    Punct(String),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Delim {
    Paren,
    Bracket,
    Brace,
    /// Generic arguments or parameters, recognized by [`structure`].
    Angle,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Role {
    Plain,
    /// The `|` opening a closure's parameters.
    ClosureOpen,
    /// The `|` closing a closure's parameters.
    ClosureClose,
}

#[derive(Clone, Debug)]
enum Tree {
    Leaf {
        tok: Tok,
        role: Role,
        line: usize,
    },
    Group {
        delim: Delim,
        body: Vec<Tree>,
        line: usize,
        end_line: usize,
    },
}

impl Tree {
    fn first_line(&self) -> usize {
        match self {
            Tree::Leaf { line, .. } | Tree::Group { line, .. } => *line,
        }
    }

    fn last_line(&self) -> usize {
        match self {
            Tree::Leaf { line, .. } => *line,
            Tree::Group { end_line, .. } => *end_line,
        }
    }

    fn punct(&self) -> Option<&str> {
        match self {
            Tree::Leaf {
                tok: Tok::Punct(p), ..
            } => Some(p),
            _ => None,
        }
    }

    fn ident(&self) -> Option<&str> {
        match self {
            Tree::Leaf {
                tok: Tok::Ident(i), ..
            } => Some(i),
            _ => None,
        }
    }

    fn is_punct(&self, p: &str) -> bool {
        self.punct() == Some(p)
    }

    fn is_ident(&self, i: &str) -> bool {
        self.ident() == Some(i)
    }

    fn delim(&self) -> Option<Delim> {
        match self {
            Tree::Group { delim, .. } => Some(*delim),
            _ => None,
        }
    }
}

/// Multi-character operators, longest first within each prefix, including
/// Verus's.
const OPERATORS: &[&str] = &[
    "<==>", "=~~=", "<<=", ">>=", "...", "..=", "==>", "<==", "===", "!==", "&&&", "|||", "=~=",
    "!~=", "::", "->", "=>", "==", "!=", "<=", ">=", "&&", "||", "+=", "-=", "*=", "/=", "%=",
    "^=", "&=", "|=", "<<", ">>", "..",
];

/// Converts a token stream into trees, joining punctuation into operators and
/// `'` with its identifier into a lifetime.
fn lower(stream: TokenStream) -> Vec<Tree> {
    let tokens: Vec<TokenTree> = stream.into_iter().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < tokens.len() {
        match &tokens[i] {
            TokenTree::Group(g) => {
                let delim = match g.delimiter() {
                    Delimiter::Parenthesis => Delim::Paren,
                    Delimiter::Bracket => Delim::Bracket,
                    Delimiter::Brace => Delim::Brace,
                    Delimiter::None => {
                        out.extend(lower(g.stream()));
                        i += 1;
                        continue;
                    }
                };
                out.push(Tree::Group {
                    delim,
                    body: lower(g.stream()),
                    line: g.span_open().start().line,
                    end_line: g.span_close().end().line,
                });
            }
            TokenTree::Ident(id) => out.push(Tree::Leaf {
                tok: Tok::Ident(id.to_string()),
                role: Role::Plain,
                line: id.span().start().line,
            }),
            TokenTree::Literal(lit) => out.push(Tree::Leaf {
                tok: Tok::Lit(lit.to_string()),
                role: Role::Plain,
                line: lit.span().start().line,
            }),
            TokenTree::Punct(p) => {
                let line = p.span().start().line;
                if p.as_char() == '\'' {
                    if let Some(TokenTree::Ident(id)) = tokens.get(i + 1) {
                        out.push(Tree::Leaf {
                            tok: Tok::Lifetime(format!("'{id}")),
                            role: Role::Plain,
                            line,
                        });
                        i += 2;
                        continue;
                    }
                }
                // Collect the run of joint punctuation, then split it into the
                // longest operators it spells.
                let mut run = String::new();
                let mut j = i;
                while let Some(TokenTree::Punct(q)) = tokens.get(j) {
                    // A `'` begins a lifetime, never an operator.
                    if q.as_char() == '\'' && j > i {
                        break;
                    }
                    run.push(q.as_char());
                    j += 1;
                    if q.spacing() == Spacing::Alone {
                        break;
                    }
                }
                let mut rest = run.as_str();
                while !rest.is_empty() {
                    let op = OPERATORS
                        .iter()
                        .filter(|op| rest.starts_with(**op))
                        .max_by_key(|op| op.len())
                        .copied()
                        .unwrap_or(&rest[..rest.chars().next().unwrap().len_utf8()]);
                    out.push(Tree::Leaf {
                        tok: Tok::Punct(op.to_string()),
                        role: Role::Plain,
                        line,
                    });
                    rest = &rest[op.len()..];
                }
                i = j;
                continue;
            }
        }
        i += 1;
    }
    out
}

const RUST_KEYWORDS: &[&str] = &[
    "as", "async", "await", "break", "const", "continue", "crate", "dyn", "else", "enum", "extern",
    "false", "fn", "for", "if", "impl", "in", "let", "loop", "match", "mod", "move", "mut", "pub",
    "ref", "return", "self", "Self", "static", "struct", "super", "trait", "true", "type",
    "unsafe", "use", "where", "while",
];

/// Keywords, including Verus's, after which an expression starts.
const EXPRESSION_KEYWORDS: &[&str] = &[
    "as",
    "break",
    "else",
    "if",
    "in",
    "let",
    "match",
    "move",
    "mut",
    "ref",
    "return",
    "while",
    "requires",
    "ensures",
    "decreases",
    "recommends",
    "invariant",
    "returns",
    "by",
    "is",
    "matches",
    "ghost",
    "tracked",
    "forall",
    "exists",
    "choose",
];

fn is_keyword(ident: &str) -> bool {
    RUST_KEYWORDS.contains(&ident)
}

/// Whether a tree ends an operand, so that a following `-`, `&`, `*`, or `|`
/// is binary rather than unary.
fn ends_operand(tree: &Tree) -> bool {
    match tree {
        Tree::Group { .. } => true,
        Tree::Leaf { tok, role, .. } => match tok {
            Tok::Ident(i) => {
                !EXPRESSION_KEYWORDS.contains(&i.as_str())
                    && (!is_keyword(i) || matches!(i.as_str(), "self" | "Self" | "true" | "false"))
            }
            Tok::Lit(_) | Tok::Lifetime(_) => true,
            Tok::Punct(p) => matches!(p.as_str(), "?" | "@") && *role == Role::Plain,
        },
    }
}

/// Recognizes generic angle brackets and closure parameter lists, recursively.
fn structure(trees: Vec<Tree>) -> Vec<Tree> {
    let trees: Vec<Tree> = trees
        .into_iter()
        .map(|t| match t {
            Tree::Group {
                delim,
                body,
                line,
                end_line,
            } => Tree::Group {
                delim,
                body: structure(body),
                line,
                end_line,
            },
            leaf => leaf,
        })
        .collect();
    let trees = angles(trees);
    mark_closures(trees)
}

fn generic_open(trees: &[Tree], i: usize) -> bool {
    if !trees[i].is_punct("<") {
        return false;
    }
    let prev = if i > 0 { Some(&trees[i - 1]) } else { None };
    let prev2 = if i > 1 { Some(&trees[i - 2]) } else { None };
    match prev {
        None => true,
        Some(p) if p.is_punct("::") => true,
        Some(p) => match p.ident() {
            Some(id) if id == "impl" || id == "for" => true,
            Some(id) if !is_keyword(id) || id == "Self" => {
                id.starts_with(|c: char| c.is_ascii_uppercase())
                    || prev2.and_then(Tree::ident).is_some_and(|k| {
                        matches!(k, "fn" | "struct" | "enum" | "type" | "trait" | "union")
                    })
            }
            _ => !ends_operand(p),
        },
    }
}

/// Groups each generic `<...>` into an [`Delim::Angle`] group. A `>>` that
/// closes two generics is split; one that does not remains a shift.
fn angles(trees: Vec<Tree>) -> Vec<Tree> {
    // Split `>>` into two `>`, remembering the pairs, so that each can close a
    // generic; pairs left over are re-joined afterwards.
    let mut split = Vec::with_capacity(trees.len());
    for t in trees {
        match t {
            Tree::Leaf {
                tok: Tok::Punct(p),
                role,
                line,
            } if p == ">>" => {
                split.push((
                    Tree::Leaf {
                        tok: Tok::Punct(">".into()),
                        role,
                        line,
                    },
                    true,
                ));
                split.push((
                    Tree::Leaf {
                        tok: Tok::Punct(">".into()),
                        role,
                        line,
                    },
                    false,
                ));
            }
            t => split.push((t, false)),
        }
    }
    let (trees, pair_starts): (Vec<Tree>, Vec<bool>) = split.into_iter().unzip();
    let mut closes = vec![None; trees.len()];
    let mut i = 0;
    while i < trees.len() {
        if generic_open(&trees, i) {
            if let Some(j) = matching_angle(&trees, i) {
                closes[i] = Some(j);
            }
        }
        i += 1;
    }
    build_angles(trees, &pair_starts, &closes, 0, usize::MAX).0
}

/// The index of the `>` closing the generic opened at `open`, if the tokens
/// between can be generic arguments.
fn matching_angle(trees: &[Tree], open: usize) -> Option<usize> {
    let mut depth = 0usize;
    for (k, t) in trees.iter().enumerate().skip(open) {
        if generic_open(trees, k) {
            depth += 1;
        } else if t.is_punct(">") {
            depth -= 1;
            if depth == 0 {
                return Some(k);
            }
        } else if matches!(
            t.punct(),
            Some(";" | "=>" | "&&" | "||" | "==" | "<=" | ">=")
        ) || t.delim() == Some(Delim::Brace)
        {
            return None;
        }
    }
    None
}

fn build_angles(
    trees: Vec<Tree>,
    pair_starts: &[bool],
    closes: &[Option<usize>],
    start: usize,
    end: usize,
) -> (Vec<Tree>, usize) {
    let mut out: Vec<Tree> = Vec::new();
    let mut trees: Vec<Option<Tree>> = trees.into_iter().map(Some).collect();
    let mut i = start;
    let end = end.min(trees.len());
    while i < end {
        if let Some(close) = closes[i] {
            let line = trees[i].as_ref().unwrap().first_line();
            let end_line = trees[close].as_ref().unwrap().last_line();
            let inner: Vec<Tree> = (i + 1..close).filter_map(|k| trees[k].take()).collect();
            // Re-run on the inner slice with the same close table, offset.
            let inner_closes: Vec<Option<usize>> = closes[i + 1..close]
                .iter()
                .map(|c| c.map(|c| c - (i + 1)))
                .collect();
            let body = build_angles(
                inner,
                &pair_starts[i + 1..close],
                &inner_closes,
                0,
                usize::MAX,
            )
            .0;
            out.push(Tree::Group {
                delim: Delim::Angle,
                body,
                line,
                end_line,
            });
            i = close + 1;
            continue;
        }
        let t = trees[i].take().unwrap();
        // Re-join a `>>` whose halves both remain.
        if pair_starts[i]
            && i + 1 < end
            && closes[i + 1].is_none()
            && trees[i + 1].as_ref().is_some_and(|n| n.is_punct(">"))
        {
            if let Tree::Leaf { role, line, .. } = t {
                trees[i + 1].take();
                out.push(Tree::Leaf {
                    tok: Tok::Punct(">>".into()),
                    role,
                    line,
                });
                i += 2;
                continue;
            }
        }
        out.push(t);
        i += 1;
    }
    (out, i)
}

fn mark_closures(mut trees: Vec<Tree>) -> Vec<Tree> {
    let mut i = 0;
    while i < trees.len() {
        let unary = i == 0
            || !ends_operand(&trees[i - 1])
            || trees[i - 1]
                .ident()
                .is_some_and(|k| matches!(k, "move" | "forall" | "exists" | "choose"));
        if trees[i].is_punct("|") && unary {
            if let Some(j) = (i + 1..trees.len()).find(|&j| trees[j].is_punct("|")) {
                set_role(&mut trees[i], Role::ClosureOpen);
                set_role(&mut trees[j], Role::ClosureClose);
                i = j + 1;
                continue;
            }
        }
        if trees[i].is_punct("||") && unary {
            set_role(&mut trees[i], Role::ClosureClose);
        }
        i += 1;
    }
    trees
}

fn set_role(tree: &mut Tree, new: Role) {
    if let Tree::Leaf { role, .. } = tree {
        *role = new;
    }
}

// ============================================================
// Documents
// ============================================================

#[derive(Clone, Debug)]
enum Doc {
    Text(String),
    /// A space, or a line break when its group breaks.
    Line,
    /// Nothing, or a line break when its group breaks.
    SoftLine,
    /// Always a line break.
    HardLine,
    /// An empty line, as a separator between items.
    BlankLine,
    /// The first document when its group breaks, the second when it is flat.
    IfBreak(Box<Doc>, Box<Doc>),
    Nest(usize, Box<Doc>),
    /// Laid out flat if it fits, otherwise broken. Records whether it contains
    /// a hard line break, which forces it to break.
    Group(Box<Doc>, bool),
    Concat(Vec<Doc>),
}

fn text(s: impl Into<String>) -> Doc {
    Doc::Text(s.into())
}

fn nest(n: usize, doc: Doc) -> Doc {
    Doc::Nest(n, Box::new(doc))
}

fn concat(docs: Vec<Doc>) -> Doc {
    Doc::Concat(docs)
}

fn has_hard(doc: &Doc) -> bool {
    match doc {
        Doc::HardLine | Doc::BlankLine => true,
        Doc::Text(_) | Doc::Line | Doc::SoftLine => false,
        Doc::IfBreak(_, flat) => has_hard(flat),
        Doc::Nest(_, d) => has_hard(d),
        Doc::Group(_, hard) => *hard,
        Doc::Concat(ds) => ds.iter().any(has_hard),
    }
}

fn group(doc: Doc) -> Doc {
    let hard = has_hard(&doc);
    Doc::Group(Box::new(doc), hard)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Flat,
    Break,
}

fn render(doc: &Doc, start_col: usize) -> String {
    let mut out = String::new();
    let mut col = start_col;
    let mut stack: Vec<(usize, Mode, &Doc)> = vec![(0, Mode::Break, doc)];
    while let Some((ind, mode, d)) = stack.pop() {
        match d {
            Doc::Text(s) => {
                out.push_str(s);
                col += s.chars().count();
            }
            Doc::Line | Doc::SoftLine if mode == Mode::Flat => {
                if matches!(d, Doc::Line) {
                    out.push(' ');
                    col += 1;
                }
            }
            Doc::Line | Doc::SoftLine | Doc::HardLine => {
                newline(&mut out, ind);
                col = ind;
            }
            Doc::BlankLine => {
                trim_trailing(&mut out);
                out.push('\n');
                newline(&mut out, ind);
                col = ind;
            }
            Doc::IfBreak(broken, flat) => {
                stack.push((ind, mode, if mode == Mode::Break { broken } else { flat }));
            }
            Doc::Nest(n, d) => stack.push((ind + n, mode, d)),
            Doc::Concat(ds) => {
                for d in ds.iter().rev() {
                    stack.push((ind, mode, d));
                }
            }
            Doc::Group(d, hard) => {
                let flat = mode == Mode::Flat
                    || (!*hard && fits(WIDTH.saturating_sub(col) as isize, d, &stack));
                stack.push((ind, if flat { Mode::Flat } else { Mode::Break }, d));
            }
        }
    }
    trim_trailing(&mut out);
    out
}

fn newline(out: &mut String, ind: usize) {
    trim_trailing(out);
    out.push('\n');
    out.extend(std::iter::repeat_n(' ', ind));
}

fn trim_trailing(out: &mut String) {
    while out.ends_with(' ') {
        out.pop();
    }
}

/// Whether `doc`, laid out flat, and what follows it up to the next line
/// break fit in `width` columns.
fn fits(mut width: isize, doc: &Doc, rest: &[(usize, Mode, &Doc)]) -> bool {
    let mut stack: Vec<(Mode, &Doc)> = vec![(Mode::Flat, doc)];
    let mut rest = rest.iter().rev();
    loop {
        let (mode, d) = match stack.pop() {
            Some(item) => item,
            None => match rest.next() {
                Some((_, mode, d)) => (*mode, *d),
                None => return true,
            },
        };
        if width < 0 {
            return false;
        }
        match d {
            Doc::Text(s) => width -= s.chars().count() as isize,
            Doc::Line => {
                if mode == Mode::Break {
                    return true;
                }
                width -= 1;
            }
            Doc::SoftLine => {
                if mode == Mode::Break {
                    return true;
                }
            }
            Doc::HardLine | Doc::BlankLine => return mode == Mode::Break,
            Doc::IfBreak(broken, flat) => {
                stack.push((mode, if mode == Mode::Break { broken } else { flat }))
            }
            Doc::Nest(_, d) => stack.push((mode, d)),
            Doc::Concat(ds) => {
                for d in ds.iter().rev() {
                    stack.push((mode, d));
                }
            }
            Doc::Group(d, hard) => {
                if *hard && mode == Mode::Flat {
                    return false;
                }
                stack.push((mode, d));
            }
        }
        if width < 0 {
            return false;
        }
    }
}

// ============================================================
// Layout
// ============================================================

#[derive(Clone, Copy, PartialEq, Eq)]
enum Context {
    /// Items, as at the top level or in an `impl`.
    Items,
    /// Statements in a block.
    Statements,
}

/// How the contents of a brace group are laid out.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum BraceKind {
    /// A block of items or statements, always broken.
    Block,
    /// Match arms, always broken.
    Arms,
    /// Struct fields, enum variants, or a `broadcast use` list: one per line.
    Fields,
    /// A struct literal or pattern: flat, with inner spaces, if it fits.
    Inline,
    /// A `use` tree: flat if it fits.
    UseTree,
}

/// Verus specification clauses of a function signature.
const CLAUSES: &[&str] = &[
    "requires",
    "recommends",
    "ensures",
    "returns",
    "decreases",
    "opens_invariants",
];

/// Operators before which a long expression breaks.
const CHAIN_OPERATORS: &[&str] = &["||", "&&", "==>", "<==>", "&&&", "|||"];

#[derive(Default)]
struct Printer;

impl Printer {
    /// Lays out items or statements, one per line, keeping blank lines.
    fn items(&self, trees: &[Tree], ctx: Context) -> Doc {
        let units = split_units(trees);
        let mut docs = Vec::new();
        for (k, unit) in units.iter().enumerate() {
            if k > 0 {
                let prev_end = units[k - 1].last().map(Tree::last_line).unwrap_or(0);
                let blank = unit.first().is_some_and(|t| t.first_line() > prev_end + 1)
                    || (ctx == Context::Items && (has_body(units[k - 1]) || has_body(unit)));
                docs.push(if blank { Doc::BlankLine } else { Doc::HardLine });
            }
            docs.push(self.unit(unit, ctx));
        }
        concat(docs)
    }

    /// Lays out one item or statement, with its attributes on their own lines.
    fn unit(&self, trees: &[Tree], ctx: Context) -> Doc {
        let mut docs = Vec::new();
        let mut i = 0;
        while let Some((attr, len)) = attribute(&trees[i..]) {
            docs.push(attr);
            docs.push(Doc::HardLine);
            i += len;
        }
        let rest = &trees[i..];
        // `broadcast use a, b;` lists one name per line when long.
        if rest.len() > 2
            && rest[0].is_ident("broadcast")
            && rest[1].is_ident("use")
            && rest.iter().any(|t| t.is_punct(","))
        {
            let end = if rest.last().is_some_and(|t| t.is_punct(";")) {
                rest.len() - 1
            } else {
                rest.len()
            };
            let mut names = Vec::new();
            for (n, name) in split_commas(&rest[2..end]).into_iter().enumerate() {
                if n > 0 {
                    names.push(text(","));
                }
                names.push(Doc::Line);
                names.push(self.sequence(name, ctx));
            }
            docs.push(group(concat(vec![
                text("broadcast use"),
                nest(INDENT, concat(names)),
                text(";"),
            ])));
            return concat(docs);
        }
        // A long `impl Trait for Type` header breaks before `for`, and its body
        // then opens on a line of its own.
        if let [first, .., Tree::Group {
            delim: Delim::Brace,
            body,
            ..
        }] = rest
        {
            if first.is_ident("impl") {
                if let Some(for_at) = rest.iter().position(|t| t.is_ident("for")) {
                    let brace = rest.len() - 1;
                    docs.push(group(concat(vec![
                        self.sequence(&rest[..for_at], ctx),
                        nest(
                            INDENT,
                            concat(vec![Doc::Line, self.sequence(&rest[for_at..brace], ctx)]),
                        ),
                        Doc::IfBreak(Box::new(Doc::HardLine), Box::new(text(" "))),
                    ])));
                    docs.push(self.brace(body, BraceKind::Block));
                    return concat(docs);
                }
            }
        }
        // `.. by { proof }` keeps its block at the statement's indentation.
        if let [head @ .., by, Tree::Group {
            delim: Delim::Brace,
            body,
            ..
        }] = rest
        {
            if by.is_ident("by") && !head.is_empty() {
                docs.push(self.expression(head, ctx));
                docs.push(text(" by "));
                docs.push(self.brace(body, BraceKind::Block));
                return concat(docs);
            }
        }
        if let Some(clause) = rest
            .iter()
            .position(|t| t.ident().is_some_and(|k| CLAUSES.contains(&k)))
        {
            docs.push(self.function_with_clauses(rest, clause));
        } else {
            docs.push(self.expression(rest, ctx));
        }
        concat(docs)
    }

    /// A function whose signature has Verus clauses: each clause keyword on its
    /// own line, each condition on its own line below it, and the body on the
    /// line after the last.
    fn function_with_clauses(&self, trees: &[Tree], first_clause: usize) -> Doc {
        let (body, end) = match trees.last() {
            Some(
                t @ Tree::Group {
                    delim: Delim::Brace,
                    ..
                },
            ) => (Some(t), trees.len() - 1),
            Some(t) if t.is_punct(";") => (None, trees.len() - 1),
            _ => (None, trees.len()),
        };
        let mut docs = vec![self.expression(&trees[..first_clause], Context::Items)];
        let mut i = first_clause;
        while i < end {
            let next = (i + 1..end)
                .find(|&k| trees[k].ident().is_some_and(|c| CLAUSES.contains(&c)))
                .unwrap_or(end);
            let keyword = trees[i].ident().unwrap().to_string();
            let mut clause = vec![Doc::HardLine, text(keyword)];
            for cond in split_commas(&trees[i + 1..next]) {
                clause.push(nest(
                    INDENT,
                    concat(vec![
                        Doc::HardLine,
                        self.expression(cond, Context::Statements),
                        text(","),
                    ]),
                ));
            }
            docs.push(nest(INDENT, concat(clause)));
            i = next;
        }
        match body {
            Some(Tree::Group { body, .. }) => {
                docs.push(Doc::HardLine);
                docs.push(self.brace(body, BraceKind::Block));
            }
            _ if end < trees.len() => docs.push(text(";")),
            _ => {}
        }
        concat(docs)
    }

    /// Lays out a sequence of trees as one expression, item, or statement,
    /// spacing adjacent tokens and breaking long operator chains.
    fn expression(&self, trees: &[Tree], ctx: Context) -> Doc {
        let breaks_at = |ops: &[&str]| -> Vec<usize> {
            (0..trees.len())
                .filter(|&k| {
                    k > 0
                        && trees[k].punct().is_some_and(|p| ops.contains(&p))
                        && ends_operand(&trees[k - 1])
                        && !matches!(
                            &trees[k],
                            Tree::Leaf {
                                role: Role::ClosureClose,
                                ..
                            }
                        )
                })
                .collect()
        };
        // A quantifier, or a closure whose body cannot break, breaks after its
        // parameters.
        if let Some(close) = trees.iter().position(|t| {
            matches!(
                t,
                Tree::Leaf {
                    role: Role::ClosureClose,
                    ..
                }
            ) && t.is_punct("|")
        }) {
            let open = trees[..close].iter().rposition(|t| {
                matches!(
                    t,
                    Tree::Leaf {
                        role: Role::ClosureOpen,
                        ..
                    }
                )
            });
            let quantifier = open.is_some_and(|o| {
                o > 0
                    && trees[o - 1]
                        .ident()
                        .is_some_and(|k| matches!(k, "forall" | "exists" | "choose"))
            });
            let tail = &trees[close + 1..];
            let unbreakable = !tail
                .iter()
                .any(|t| matches!(t, Tree::Group { body, .. } if body.len() > 1));
            if !tail.is_empty() && (quantifier || unbreakable) && open.is_some() {
                return group(concat(vec![
                    self.sequence(&trees[..=close], ctx),
                    nest(INDENT, concat(vec![Doc::Line, self.expression(tail, ctx)])),
                ]));
            }
        }
        // Break at the loosest operators present: logical ones, else
        // comparisons and sums, but never inside a `let` or assignment target.
        let mut chain = breaks_at(CHAIN_OPERATORS);
        chain.extend((1..trees.len()).filter(|&k| trees[k].is_ident("implies")));
        chain.sort();
        if chain.is_empty() {
            chain = breaks_at(&["==", "!=", "===", "=~=", "+"]);
        }
        let assignment = trees
            .iter()
            .rposition(|t| t.is_punct("="))
            .map_or(0, |k| k + 1);
        chain.retain(|&k| k > assignment);
        if chain.is_empty() {
            return self.sequence(trees, ctx);
        }
        let mut docs = vec![self.sequence(&trees[..chain[0]], ctx)];
        let mut rest = Vec::new();
        for (n, &k) in chain.iter().enumerate() {
            let end = chain.get(n + 1).copied().unwrap_or(trees.len());
            rest.push(Doc::Line);
            rest.push(self.sequence(&trees[k..end], ctx));
        }
        docs.push(nest(INDENT, concat(rest)));
        group(concat(docs))
    }

    fn sequence(&self, trees: &[Tree], ctx: Context) -> Doc {
        // A chain of two or more method calls breaks before each `.` of a call.
        let is_call = |k: usize| {
            trees[k].is_punct(".")
                && trees.get(k + 1).and_then(Tree::ident).is_some()
                && trees
                    .get(k + 2)
                    .is_some_and(|t| t.delim() == Some(Delim::Paren))
        };
        let mut calls: Vec<usize> = Vec::new();
        let mut k = 1;
        while k < trees.len() {
            if is_call(k) {
                // Extend the chain while only postfix tokens separate calls.
                let mut chain = vec![k];
                let mut j = k + 3;
                loop {
                    while j < trees.len()
                        && (trees[j].is_punct("?")
                            || trees[j].is_punct("@")
                            || trees[j].delim() == Some(Delim::Bracket)
                            || (trees[j].is_punct(".")
                                && !is_call(j)
                                && trees.get(j + 1).is_some()))
                    {
                        j += if trees[j].is_punct(".") { 2 } else { 1 };
                    }
                    if j < trees.len() && is_call(j) {
                        chain.push(j);
                        j += 3;
                    } else {
                        break;
                    }
                }
                if chain.len() > calls.len() {
                    calls = chain;
                }
                k = j;
            } else {
                k += 1;
            }
        }
        if calls.len() >= 2 {
            let mut docs = vec![self.tokens(&trees[..calls[0]], ctx, trees)];
            let mut parts = Vec::new();
            for (n, &k) in calls.iter().enumerate() {
                let end = calls.get(n + 1).copied().unwrap_or(trees.len());
                parts.push(Doc::SoftLine);
                parts.push(self.tokens(&trees[k..end], ctx, trees));
            }
            docs.push(nest(INDENT, concat(parts)));
            return group(concat(docs));
        }
        self.tokens(trees, ctx, trees)
    }

    /// Lays out `trees`, a slice of `whole`, token by token.
    fn tokens(&self, trees: &[Tree], ctx: Context, whole: &[Tree]) -> Doc {
        let offset =
            (trees.as_ptr() as usize - whole.as_ptr() as usize) / std::mem::size_of::<Tree>();
        let mut docs = Vec::new();
        let arms_after = whole
            .iter()
            .rposition(|t| t.is_ident("match"))
            .filter(|_| ctx == Context::Statements || ctx == Context::Items);
        let mut prev: Option<&Tree> = if offset > 0 {
            Some(&whole[offset - 1])
        } else {
            None
        };
        let mut prev2: Option<&Tree> = if offset > 1 {
            Some(&whole[offset - 2])
        } else {
            None
        };
        let mut first = true;
        for (k, t) in trees.iter().enumerate() {
            let k = k + offset;
            if let Some(p) = prev {
                if !first && space_between(prev2, p, t) {
                    docs.push(text(" "));
                }
            }
            first = false;
            docs.push(match t {
                Tree::Leaf { tok, .. } => text(tok_text(tok)),
                Tree::Group { delim, body, .. } => match delim {
                    Delim::Brace => {
                        let kind = brace_kind(&whole[..k], arms_after.is_some_and(|m| m < k));
                        self.brace(body, kind)
                    }
                    Delim::Paren => self.list("(", ")", body, false),
                    Delim::Bracket => self.list("[", "]", body, false),
                    Delim::Angle => self.list("<", ">", body, false),
                },
            });
            prev2 = prev;
            prev = Some(t);
        }
        concat(docs)
    }

    /// A delimited, comma-separated list: flat if it fits, otherwise one
    /// element per line with a trailing comma.
    fn list(&self, open: &str, close: &str, body: &[Tree], spaced: bool) -> Doc {
        let elems = split_commas(body);
        if elems.is_empty() {
            return text(format!("{open}{close}"));
        }
        if open == "(" {
            if let Some(doc) = self.nested_tuple(body) {
                return doc;
            }
        }
        // A qualified path `<T as Trait>` stays on one line.
        if open == "<" && body.iter().any(|t| t.is_ident("as")) {
            return concat(vec![
                text("<"),
                self.sequence(body, Context::Statements),
                text(">"),
            ]);
        }
        // `(x,)` is a one-element tuple, whose comma must stay; any other
        // one-element list gains none, as `(x)` and `assert(x)` must not.
        let keep_comma =
            open == "(" && elems.len() == 1 && body.last().is_some_and(|t| t.is_punct(","));
        if elems.len() == 1
            && !keep_comma
            && elems[0].len() == 1
            && matches!(elems[0][0], Tree::Leaf { .. })
        {
            let sep = if spaced { " " } else { "" };
            return concat(vec![
                text(format!("{open}{sep}")),
                self.element(elems[0]),
                text(format!("{sep}{close}")),
            ]);
        }
        let edge = if spaced { Doc::Line } else { Doc::SoftLine };
        let mut inner = vec![edge.clone()];
        for (n, elem) in elems.iter().enumerate() {
            if n > 0 {
                inner.push(text(","));
                inner.push(Doc::Line);
            }
            inner.push(self.element(elem));
        }
        inner.push(if keep_comma {
            text(",")
        } else if elems.len() == 1 && open != "<" {
            text("")
        } else {
            Doc::IfBreak(Box::new(text(",")), Box::new(text("")))
        });
        group(concat(vec![
            text(open),
            nest(INDENT, concat(inner)),
            edge,
            text(close),
        ]))
    }

    /// A right-nested tuple `(a, (b, (c, ..)))`, such as a structural type,
    /// filled onto as few lines as fit rather than one level per line.
    fn nested_tuple(&self, body: &[Tree]) -> Option<Doc> {
        let mut heads = Vec::new();
        let mut body = body;
        loop {
            match split_commas(body).as_slice() {
                [head, [Tree::Group {
                    delim: Delim::Paren,
                    body: inner,
                    ..
                }]] if split_commas(inner).len() == 2 => {
                    heads.push(*head);
                    body = inner;
                }
                _ => break,
            }
        }
        if heads.len() < 2 {
            return None;
        }
        let last = split_commas(body);
        let mut docs = vec![text("("), self.element(heads[0]), text(",")];
        let mut rest = Vec::new();
        for head in &heads[1..] {
            rest.push(group(concat(vec![
                Doc::Line,
                text("("),
                self.element(head),
                text(","),
            ])));
        }
        let mut tail = vec![Doc::Line, text("(")];
        for (n, elem) in last.iter().enumerate() {
            if n > 0 {
                tail.push(text(", "));
            }
            tail.push(self.element(elem));
        }
        tail.push(text(")".repeat(heads.len() + 1)));
        rest.push(group(concat(tail)));
        docs.push(nest(INDENT, concat(rest)));
        Some(group(concat(docs)))
    }

    /// One element of a list, which may carry attributes of its own.
    fn element(&self, trees: &[Tree]) -> Doc {
        let mut docs = Vec::new();
        let mut i = 0;
        while let Some((attr, len)) = attribute(&trees[i..]) {
            docs.push(attr);
            docs.push(Doc::HardLine);
            i += len;
        }
        docs.push(self.expression(&trees[i..], Context::Statements));
        concat(docs)
    }

    fn brace(&self, body: &[Tree], kind: BraceKind) -> Doc {
        if body.is_empty() {
            return text("{}");
        }
        match kind {
            BraceKind::Inline => self.list("{", "}", body, true),
            BraceKind::UseTree => self.list("{", "}", body, false),
            BraceKind::Block => {
                let ctx = if starts_item(body) {
                    Context::Items
                } else {
                    Context::Statements
                };
                concat(vec![
                    text("{"),
                    nest(INDENT, concat(vec![Doc::HardLine, self.items(body, ctx)])),
                    Doc::HardLine,
                    text("}"),
                ])
            }
            BraceKind::Fields => {
                let mut inner = Vec::new();
                for elem in split_commas(body) {
                    inner.push(Doc::HardLine);
                    inner.push(self.element(elem));
                    inner.push(text(","));
                }
                concat(vec![
                    text("{"),
                    nest(INDENT, concat(inner)),
                    Doc::HardLine,
                    text("}"),
                ])
            }
            BraceKind::Arms => {
                let mut inner = Vec::new();
                for arm in split_arms(body) {
                    inner.push(Doc::HardLine);
                    inner.push(self.arm(arm));
                }
                concat(vec![
                    text("{"),
                    nest(INDENT, concat(inner)),
                    Doc::HardLine,
                    text("}"),
                ])
            }
        }
    }

    /// A match arm: `pattern => body,`, breaking after `=>` first when long.
    fn arm(&self, trees: &[Tree]) -> Doc {
        let trees = match trees.last() {
            Some(t) if t.is_punct(",") => &trees[..trees.len() - 1],
            _ => trees,
        };
        let Some(arrow) = trees.iter().position(|t| t.is_punct("=>")) else {
            return concat(vec![self.element(trees), text(",")]);
        };
        let pattern = self.element(&trees[..arrow]);
        let body = &trees[arrow + 1..];
        if let [Tree::Group {
            delim: Delim::Brace,
            body,
            ..
        }] = body
        {
            return concat(vec![
                pattern,
                text(" => "),
                self.brace(body, BraceKind::Block),
            ]);
        }
        group(concat(vec![
            pattern,
            text(" =>"),
            nest(
                INDENT,
                concat(vec![Doc::Line, self.expression(body, Context::Statements)]),
            ),
            text(","),
        ]))
    }
}

fn tok_text(tok: &Tok) -> String {
    match tok {
        Tok::Ident(s) | Tok::Lifetime(s) | Tok::Lit(s) | Tok::Punct(s) => s.clone(),
    }
}

/// Recognizes an attribute at the start of `trees`, returning its layout and
/// the number of trees it spans. `#[doc = "..."]` becomes a `///` comment.
fn attribute(trees: &[Tree]) -> Option<(Doc, usize)> {
    let [hash, rest @ ..] = trees else {
        return None;
    };
    if !hash.is_punct("#") {
        return None;
    }
    let (inner, bang, len) = match rest {
        [Tree::Group {
            delim: Delim::Bracket,
            body,
            ..
        }, ..] => (body, "", 2),
        [bang, Tree::Group {
            delim: Delim::Bracket,
            body,
            ..
        }, ..]
            if bang.is_punct("!") =>
        {
            (body, "!", 3)
        }
        _ => return None,
    };
    if bang.is_empty() {
        if let [doc, eq, Tree::Leaf {
            tok: Tok::Lit(lit), ..
        }] = inner.as_slice()
        {
            if doc.is_ident("doc") && eq.is_punct("=") {
                if let Some(content) = unquote(lit) {
                    let lines: Vec<Doc> = content
                        .split('\n')
                        .map(|l| {
                            let l = l.trim_end();
                            if l.is_empty() {
                                text("///")
                            } else if l.starts_with(' ') {
                                text(format!("///{l}"))
                            } else {
                                text(format!("/// {l}"))
                            }
                        })
                        .collect();
                    let mut docs = Vec::new();
                    for (n, l) in lines.into_iter().enumerate() {
                        if n > 0 {
                            docs.push(Doc::HardLine);
                        }
                        docs.push(l);
                    }
                    return Some((concat(docs), len));
                }
            }
        }
    }
    Some((text(format!("#{bang}[{}]", flat_text(inner))), len))
}

/// The contents of a plain string literal, or `None` for other literals.
fn unquote(lit: &str) -> Option<String> {
    let inner = lit.strip_prefix('"')?.strip_suffix('"')?;
    let mut out = String::new();
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next()? {
            'n' => out.push('\n'),
            't' => out.push('\t'),
            '\\' => out.push('\\'),
            '"' => out.push('"'),
            '\'' => out.push('\''),
            '0' => out.push('\0'),
            _ => return None,
        }
    }
    Some(out)
}

/// A tree sequence on one line, spaced as in [`Printer::sequence`].
fn flat_text(trees: &[Tree]) -> String {
    let doc = Printer.sequence(trees, Context::Statements);
    let mut out = String::new();
    flatten(&doc, &mut out);
    out
}

fn flatten(doc: &Doc, out: &mut String) {
    match doc {
        Doc::Text(s) => out.push_str(s),
        Doc::Line => out.push(' '),
        Doc::SoftLine => {}
        Doc::HardLine | Doc::BlankLine => out.push(' '),
        Doc::IfBreak(_, flat) => flatten(flat, out),
        Doc::Nest(_, d) | Doc::Group(d, _) => flatten(d, out),
        Doc::Concat(ds) => ds.iter().for_each(|d| flatten(d, out)),
    }
}

/// Splits a list at its top-level commas, dropping a trailing one.
fn split_commas(trees: &[Tree]) -> Vec<&[Tree]> {
    let mut out = Vec::new();
    let mut start = 0;
    for (k, t) in trees.iter().enumerate() {
        if t.is_punct(",") {
            out.push(&trees[start..k]);
            start = k + 1;
        }
    }
    if start < trees.len() {
        out.push(&trees[start..]);
    }
    out
}

/// Splits match arms: at top-level commas, and after an arm whose body is a
/// block.
fn split_arms(trees: &[Tree]) -> Vec<&[Tree]> {
    let mut out = Vec::new();
    let mut start = 0;
    let mut k = 0;
    while k < trees.len() {
        let t = &trees[k];
        let block_body = t.delim() == Some(Delim::Brace) && k > 0 && trees[k - 1].is_punct("=>");
        if t.is_punct(",") || (block_body && !trees.get(k + 1).is_some_and(|n| n.is_punct(","))) {
            out.push(&trees[start..=k]);
            start = k + 1;
        }
        k += 1;
    }
    if start < trees.len() {
        out.push(&trees[start..]);
    }
    out
}

/// Splits items or statements: after each top-level `;`, and after a block
/// that ends one.
fn split_units(trees: &[Tree]) -> Vec<&[Tree]> {
    let mut out = Vec::new();
    let mut start = 0;
    let mut k = 0;
    while k < trees.len() {
        let t = &trees[k];
        let ends = if t.is_punct(";") {
            true
        } else if t.delim() == Some(Delim::Brace) {
            match trees.get(k + 1) {
                None => false,
                Some(next) => {
                    let continues = next.punct().is_some_and(|p| p != "#")
                        || next.is_ident("else")
                        || next.is_ident("as")
                        || next.delim().is_some_and(|d| d != Delim::Brace);
                    !continues && !is_struct_literal_head(&trees[start..k])
                }
            }
        } else {
            false
        };
        if ends {
            out.push(&trees[start..=k]);
            start = k + 1;
        }
        k += 1;
    }
    if start < trees.len() {
        out.push(&trees[start..]);
    }
    out
}

/// Whether a brace group after `head` is a struct literal in a statement that
/// continues past it, as in `let x = Foo { .. } + y`; such a brace does not end
/// the statement.
fn is_struct_literal_head(head: &[Tree]) -> bool {
    brace_kind(head, false) == BraceKind::Inline && head.iter().any(|t| t.is_punct("="))
}

/// Whether an item has a braced body, as a function, `impl`, or type does,
/// which a blank line then separates from its neighbours.
fn has_body(unit: &[Tree]) -> bool {
    let mut i = 0;
    while let Some((_, len)) = attribute(&unit[i..]) {
        i += len;
    }
    let is_use = unit[i..].iter().take(3).any(|t| t.is_ident("use"));
    !is_use && unit[i..].iter().any(|t| t.delim() == Some(Delim::Brace))
}

fn starts_item(body: &[Tree]) -> bool {
    let mut i = 0;
    while let Some((_, len)) = attribute(&body[i..]) {
        i += len;
    }
    body.get(i).and_then(Tree::ident).is_some_and(|k| {
        matches!(
            k,
            "pub"
                | "fn"
                | "impl"
                | "struct"
                | "enum"
                | "type"
                | "trait"
                | "mod"
                | "use"
                | "const"
                | "static"
                | "open"
                | "closed"
                | "spec"
                | "proof"
                | "exec"
                | "broadcast"
                | "unsafe"
                | "extern"
        ) && !(k == "proof"
            && body
                .get(i + 1)
                .is_some_and(|n| n.delim() == Some(Delim::Brace)))
    })
}

/// Decides how a brace group following `head` (the trees before it in the same
/// unit) is laid out.
fn brace_kind(head: &[Tree], after_match: bool) -> BraceKind {
    let Some(prev) = head.last() else {
        return BraceKind::Block;
    };
    if prev.is_punct("::") {
        return BraceKind::UseTree;
    }
    if prev.is_ident("use") {
        return BraceKind::Fields;
    }
    if prev.is_punct("=>")
        || prev
            .ident()
            .is_some_and(|k| matches!(k, "else" | "proof" | "unsafe" | "loop" | "by"))
    {
        return BraceKind::Block;
    }
    if matches!(
        prev,
        Tree::Leaf {
            role: Role::ClosureClose,
            ..
        }
    ) {
        return BraceKind::Block;
    }
    // Scan back to the start of the enclosing expression for a keyword that
    // introduces a block.
    for t in head.iter().rev() {
        if t.punct()
            .is_some_and(|p| matches!(p, "," | ";" | "=" | "=>"))
        {
            break;
        }
        if let Some(k) = t.ident() {
            match k {
                "match" => {
                    return if after_match {
                        BraceKind::Arms
                    } else {
                        BraceKind::Block
                    }
                }
                "struct" | "enum" | "union" => return BraceKind::Fields,
                "impl" | "trait" | "mod" | "fn" | "if" | "while" | "for" | "loop" | "unsafe" => {
                    return BraceKind::Block
                }
                _ => {}
            }
        }
    }
    let path_end = prev.ident().is_some_and(|i| !is_keyword(i) || i == "Self")
        || prev.delim() == Some(Delim::Angle);
    if path_end {
        BraceKind::Inline
    } else {
        BraceKind::Block
    }
}

/// Whether a space separates `prev` and `next`, given the tree before `prev`.
fn space_between(prev2: Option<&Tree>, prev: &Tree, next: &Tree) -> bool {
    use Delim::*;
    // Closure bars hug their parameters.
    if matches!(
        prev,
        Tree::Leaf {
            role: Role::ClosureOpen,
            ..
        }
    ) {
        return false;
    }
    if let Tree::Leaf {
        role: Role::ClosureClose,
        tok,
        ..
    } = next
    {
        if tok == &Tok::Punct("|".into()) {
            return false;
        }
    }
    if let Tree::Leaf {
        role: Role::ClosureOpen,
        ..
    } = next
    {
        return !prev
            .ident()
            .is_some_and(|k| matches!(k, "forall" | "exists" | "choose"));
    }
    let unary_prev = is_unary(prev2, prev);
    match (prev, next) {
        // Attributes: `#[..]`, `#![..]`.
        (p, Tree::Group { delim: Bracket, .. }) if p.is_punct("#") => false,
        (p, n) if p.is_punct("#") && n.is_punct("!") => false,
        (p, Tree::Group { delim: Bracket, .. })
            if p.is_punct("!") && prev2.is_some_and(|t| t.is_punct("#")) =>
        {
            false
        }
        // Paths, members, and ranges.
        (_, n) if n.is_punct("::") || n.is_punct(".") || n.is_punct("..") || n.is_punct("..=") => {
            false
        }
        (p, _) if p.is_punct("::") || p.is_punct(".") || p.is_punct("..") || p.is_punct("..=") => {
            false
        }
        // Punctuation that attaches to what precedes it.
        (_, n)
            if n.punct()
                .is_some_and(|p| matches!(p, "," | ";" | "?" | ":")) =>
        {
            false
        }
        (_, n) if n.is_punct("@") => false,
        (p, n) if p.is_punct("@") => !n.punct().is_some_and(|q| matches!(q, "," | ";")),
        // Lifetimes follow `&` and `'` directly.
        (
            p,
            Tree::Leaf {
                tok: Tok::Lifetime(_),
                ..
            },
        ) if p.is_punct("&") => false,
        // Verus's field access `v->field`.
        (p, n) if n.is_punct("->") && p.ident().is_some_and(|i| !is_keyword(i)) => false,
        (p, _)
            if p.is_punct("->")
                && prev2.is_some_and(|t| t.ident().is_some_and(|i| !is_keyword(i))) =>
        {
            false
        }
        // A macro invocation `name!(..)`.
        (p, n) if n.is_punct("!") && p.ident().is_some_and(|i| !is_keyword(i)) => false,
        (
            p,
            Tree::Group {
                delim: Paren | Bracket,
                ..
            },
        ) if p.is_punct("!") && !unary_prev => false,
        // Unary operators attach to their operand.
        (p, _)
            if unary_prev
                && p.punct()
                    .is_some_and(|q| matches!(q, "&" | "&&" | "*" | "-" | "!")) =>
        {
            false
        }
        // Calls, indexing, and generics attach to what they apply to.
        (
            p,
            Tree::Group {
                delim: Paren | Bracket,
                ..
            },
        ) => match p {
            Tree::Group { .. } => false,
            Tree::Leaf {
                tok: Tok::Ident(i), ..
            } => {
                (is_keyword(i) || EXPRESSION_KEYWORDS.contains(&i.as_str()))
                    && !matches!(i.as_str(), "self" | "Self" | "super" | "crate" | "pub")
            }
            Tree::Leaf {
                tok: Tok::Lit(_), ..
            } => false,
            Tree::Leaf {
                tok: Tok::Lifetime(_),
                ..
            } => true,
            Tree::Leaf {
                tok: Tok::Punct(q), ..
            } => !matches!(q.as_str(), "?" | "@" | "&" | "*" | "!"),
        },
        (p, Tree::Group { delim: Angle, .. }) => {
            !(p.ident().is_some() || p.is_punct("::") || p.is_punct("&"))
        }
        (
            Tree::Group {
                delim: Paren | Bracket | Angle,
                ..
            },
            n,
        ) => {
            n.ident().is_some()
                || n.delim() == Some(Brace)
                || matches!(
                    n,
                    Tree::Leaf {
                        tok: Tok::Lit(_) | Tok::Lifetime(_),
                        ..
                    }
                )
                || n.punct().is_some_and(|q| !matches!(q, "!"))
        }
        _ => true,
    }
}

/// Whether `prev`, a punctuation token, is a unary operator.
fn is_unary(prev2: Option<&Tree>, prev: &Tree) -> bool {
    prev.punct()
        .is_some_and(|p| matches!(p, "&" | "&&" | "*" | "-" | "!"))
        && prev2.is_none_or(|t| !ends_operand(t))
}

#[cfg(test)]
mod tests {
    use super::format_items;

    fn fmt(src: &str) -> String {
        format_items(src, 0)
    }

    #[test]
    fn spacing() {
        assert_eq!(
            fmt("pub type X < 'i > = Named < Mapped < Refined < U8 , PredFnSpec < u8 >> > > ;"),
            "pub type X<'i> = Named<Mapped<Refined<U8, PredFnSpec<u8>>>>;\n"
        );
        assert_eq!(
            fmt("fn parse (& self , ibuf : & & 'i [u8]) -> PResult < Self :: PT > { let (n , v) = (Named (\"x\" , XFmt)) . parse (& rest) ? ; Ok ((n , v)) }"),
            "fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {\n    let (n, v) = (Named(\"x\", XFmt)).parse(&rest)?;\n    Ok((n, v))\n}\n"
        );
        assert_eq!(fmt("let x = a >> 4 ;"), "let x = a >> 4;\n");
        assert_eq!(
            fmt("assert (obuf @ == old_obuf + self . spec (v . deep_view ())) ;"),
            "assert(obuf@ == old_obuf + self.spec(v.deep_view()));\n"
        );
        assert_eq!(
            fmt("let f = | x : u16 | x >= 64 ;"),
            "let f = |x: u16| x >= 64;\n"
        );
        assert_eq!(
            fmt("if ! (v >= 64) { return Err (e) ; }"),
            "if !(v >= 64) {\n    return Err(e);\n}\n"
        );
        assert_eq!(
            fmt("reveal (< X as SpecParser > :: spec_parse) ;"),
            "reveal(<X as SpecParser>::spec_parse);\n"
        );
        assert_eq!(
            fmt("# [doc = \"data type\"] # [derive (Clone , Copy)] pub struct XFmt ;"),
            "/// data type\n#[derive(Clone, Copy)]\npub struct XFmt;\n"
        );
        assert_eq!(fmt("let y = v -> field ;"), "let y = v->field;\n");
        assert_eq!(
            fmt("use vest_lib :: core :: { proof :: * , spec :: * } ;"),
            "use vest_lib::core::{proof::*, spec::*};\n"
        );
        assert_eq!(
            fmt("impl<'i> X<'i> { fn f(x: &'i [u8]) {} }"),
            "impl<'i> X<'i> {\n    fn f(x: &'i [u8]) {}\n}\n"
        );
    }

    #[test]
    fn qualified_paths_stay_flat() {
        let long = "reveal(<AnExtremelyLongFormatNameThatWillNotFitOnTheLineFmt as \
                    SpecSerializerDps>::spec_serialize_dps);";
        let out = fmt(long);
        assert!(
            out.contains(
                "<AnExtremelyLongFormatNameThatWillNotFitOnTheLineFmt as SpecSerializerDps>::"
            ),
            "{out}"
        );
    }

    #[test]
    fn formatting_is_idempotent() {
        let src = "impl<'i> Parser<&'i [u8]> for XFmt { type PT = X<'i>; fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> { let (n1, a) = (U8).parse(&rest)?; let total_len = l1.checked_add(l2).ok_or(PreSerializeError::length_too_large())?.checked_add(l3).ok_or(PreSerializeError::length_too_large())?; match (self.t, v) { (A, B(v)) => (Named(\"a_very_long_format_name_to_force_a_break\", AVeryLongFormatNameFmt)).prepare(v), _ => { f(); g() } } } }";
        let once = fmt(src);
        assert_eq!(fmt(&once), once);
    }

    #[test]
    fn layout() {
        assert_eq!(
            fmt("pub struct X < 'i > { pub a : u8 , pub b : & 'i [u8] , }"),
            "pub struct X<'i> {\n    pub a: u8,\n    pub b: &'i [u8],\n}\n"
        );
        assert_eq!(
            fmt("match (x , v) { (A , B (v)) => a (v) , _ => { f () ; g () } }"),
            "match (x, v) {\n    (A, B(v)) => a(v),\n    _ => {\n        f();\n        g()\n    }\n}\n"
        );
        assert_eq!(
            fmt("fn f (& self) -> (r : bool) ensures r , decreases gas , { true }"),
            "fn f(&self) -> (r: bool)\n    ensures\n        r,\n    decreases\n        gas,\n{\n    true\n}\n"
        );
        let long = format!(
            "let x = f ({}) ;",
            (0..30)
                .map(|i| format!("arg{i}"))
                .collect::<Vec<_>>()
                .join(" , ")
        );
        let out = fmt(&long);
        assert!(out.lines().all(|l| l.len() <= 100), "{out}");
        assert!(out.starts_with("let x = f(\n    arg0,\n"), "{out}");
    }

    #[test]
    fn blank_lines_and_comments_survive() {
        assert_eq!(
            fmt("fn a () {}\n\n// note\nfn b () {}\nfn c () {}"),
            "fn a() {}\n\n// note\nfn b() {}\n\nfn c() {}\n"
        );
    }
}
