use proc_macro2::TokenStream;

pub(crate) struct CodeWriter {
    buf: String,
    indent: usize,
    needs_indent: bool,
}

impl CodeWriter {
    pub(crate) fn new() -> Self {
        Self {
            buf: String::new(),
            indent: 0,
            needs_indent: true,
        }
    }

    pub(crate) fn line(&mut self, line: impl AsRef<str>) {
        self.write_line_inner(line.as_ref());
        self.buf.push('\n');
        self.needs_indent = true;
    }

    pub(crate) fn blank_line(&mut self) {
        if !self.buf.ends_with("\n") {
            self.buf.push('\n');
        }
        if !self.buf.ends_with("\n\n") {
            self.buf.push('\n');
        }
        self.needs_indent = true;
    }

    pub(crate) fn push_multiline(&mut self, text: impl AsRef<str>) {
        let text = text.as_ref();
        for line in text.lines() {
            self.write_line_inner(line);
            self.buf.push('\n');
            self.needs_indent = true;
        }
    }

    pub(crate) fn indented(&mut self, f: impl FnOnce(&mut Self)) {
        self.indent += 1;
        f(self);
        self.indent -= 1;
    }

    pub(crate) fn block(&mut self, header: impl AsRef<str>, f: impl FnOnce(&mut Self)) {
        self.line(format!("{} {{", header.as_ref()));
        self.indented(f);
        self.line("}");
    }

    pub(crate) fn finish(mut self) -> String {
        while self.buf.ends_with("\n\n\n") {
            self.buf.pop();
        }
        self.buf
    }

    pub(crate) fn if_block(&mut self, cond: impl AsRef<str>, f: impl FnOnce(&mut Self)) {
        self.block(format!("if {}", cond.as_ref()), f);
    }

    pub(crate) fn record_constructor_stmt(
        &mut self,
        lhs: &str,
        name: &str,
        fields: &[impl AsRef<str>],
    ) {
        if fields.is_empty() {
            self.line(format!("let {} = {} {{}};", lhs, name));
        } else {
            self.line(format!("let {} = {} {{", lhs, name));
            self.write_record_fields(fields);
            self.line("};");
        }
    }

    pub(crate) fn record_destructure_stmt(
        &mut self,
        name: &str,
        fields: &[impl AsRef<str>],
        rhs: &str,
    ) {
        self.write_line_inner("let ");
        if fields.is_empty() {
            self.line(format!("{} {{}} = {};", name, rhs));
        } else {
            self.write_line_inner(&format!("{} {{", name));
            self.buf.push('\n');
            self.needs_indent = true;
            self.write_record_fields(fields);
            self.line(format!("}} = {};", rhs));
        }
    }

    pub(crate) fn match_block_stmt(
        &mut self,
        lhs: Option<&str>,
        header: &str,
        f: impl FnOnce(&mut Self),
    ) {
        if let Some(l) = lhs {
            self.write_line_inner(&format!("let {} = ", l));
        }
        self.line(format!("match {} {{", header));
        self.indented(f);
        if lhs.is_some() {
            self.line("};");
        } else {
            self.line("}");
        }
    }

    fn write_record_fields(&mut self, fields: &[impl AsRef<str>]) {
        self.indented(|w| {
            for field in fields {
                let field_ref = field.as_ref().trim();
                if !field_ref.is_empty() {
                    w.line(format!("{},", field_ref));
                }
            }
        });
    }

    pub(crate) fn call_chain_stmt(
        &mut self,
        lhs: Option<&str>,
        recv: &str,
        method: &str,
        args: &[impl AsRef<str>],
        suffix: Option<&str>,
    ) {
        let mut prefix = String::new();
        if let Some(l) = lhs {
            prefix.push_str("let ");
            prefix.push_str(l);
            prefix.push_str(" = ");
        }

        let mut single_line_args = String::new();
        for (idx, arg) in args.iter().enumerate() {
            if idx > 0 {
                single_line_args.push_str(", ");
            }
            single_line_args.push_str(arg.as_ref().trim());
        }

        let call_part = if recv.is_empty() {
            format!("{}({})", method, single_line_args)
        } else if method.is_empty() {
            recv.to_string()
        } else {
            format!("{}.{}({})", recv, method, single_line_args)
        };

        let total_single_line = format!("{}{}{}", prefix, call_part, suffix.unwrap_or(""));
        if total_single_line.len() <= 80 && !recv.contains('\n') {
            self.line(total_single_line);
        } else {
            if !prefix.is_empty() {
                self.write_line_inner(&prefix);
            }
            if !recv.is_empty() {
                let recv_trimmed = recv.trim();
                self.push_multiline(recv_trimmed);
                if !method.is_empty() {
                    let chained_call =
                        format!(".{}({}){}", method, single_line_args, suffix.unwrap_or(""));
                    if chained_call.len() <= 80 {
                        self.line(chained_call);
                        return;
                    }
                    self.line(format!(".{}(", method));
                }
            } else {
                self.line(format!("{}(", method));
            }
            if !method.is_empty() {
                self.indented(|w| {
                    for arg in args {
                        w.line(format!("{},", arg.as_ref().trim()));
                    }
                });
                self.line(format!("){}", suffix.unwrap_or("")));
            } else if let Some(s) = suffix {
                self.line(s);
            }
        }
    }

    pub(crate) fn reveal_stmt(&mut self, spec: &str) {
        self.line(format!("reveal({});", spec));
    }

    fn write_line_inner(&mut self, line: &str) {
        if line.is_empty() {
            return;
        }
        if self.needs_indent {
            self.buf.push_str(&"    ".repeat(self.indent));
            self.needs_indent = false;
        }
        self.buf.push_str(line);
    }
}

pub(crate) fn cleanup_verus_spacing(input: &str) -> String {
    let mut s = input.to_string();

    for (from, to) in [
        (" . ", "."),
        (":: ", "::"),
        (" ::", "::"),
        ("? ;", "?;"),
        ("& 'i", "&'i"),
        ("& mut", "&mut"),
        ("& [", "&["),
        (" , ", ", "),
        (" ,", ","),
        (" : ", ": "),
        (" ( )", "()"),
        (" ()", "()"),
        ("reveal (", "reveal("),
        ("reveal (<", "reveal(<"),
        (" >::", ">::"),
        ("> ::", ">::"),
        ("< 'i >", "<'i>"),
        (" <'", "<'"),
        ("Vec < u8 >", "Vec<u8>"),
        ("Result <", "Result<"),
        ("PResult <", "PResult<"),
        ("Box <", "Box<"),
        ("dyn std ::", "dyn std::"),
        ("std ::", "std::"),
        ("error ::", "error::"),
        ("Error >", "Error>"),
        ("Self ::", "Self::"),
        ("self .", "self."),
        ("rest .", "rest."),
        ("ibuf .", "ibuf."),
        ("obuf .", "obuf."),
        ("ParseError ::", "ParseError::"),
        ("PreSerializeError ::", "PreSerializeError::"),
        ("* v", "*v"),
        ("* length", "*length"),
        ("* msg_type", "*msg_type"),
        ("* tag", "*tag"),
        ("* len", "*len"),
        ("* total_len", "*total_len"),
        ("* hdr_payload", "*hdr_payload"),
        ("* ext_len", "*ext_len"),
        ("* extension_type", "*extension_type"),
        ("* label_ident", "*label_ident"),
        ("as usize )", "as usize)"),
        ("as u8 )", "as u8)"),
        ("as u16 )", "as u16)"),
        ("as u32 )", "as u32)"),
        ("as u64 )", "as u64)"),
    ] {
        s = s.replace(from, to);
    }

    s
}

pub(crate) fn render_ts(ts: TokenStream) -> String {
    cleanup_verus_spacing(&format_verus_snippet(&ts.to_string()))
}

pub(crate) fn format_verus_snippet(input: &str) -> String {
    let chars = input.chars().collect::<Vec<_>>();
    let mut out = String::new();
    let mut i = 0usize;
    let mut indent = 0usize;
    let mut line_start = true;
    let mut paren_depth = 0usize;
    let mut bracket_depth = 0usize;
    let mut brace_depth = 0usize;
    let mut in_string = false;
    let mut escape = false;

    fn next_non_space(chars: &[char], mut i: usize) -> Option<char> {
        while i < chars.len() {
            if !chars[i].is_whitespace() {
                return Some(chars[i]);
            }
            i += 1;
        }
        None
    }

    fn write_indent(out: &mut String, indent: usize, line_start: &mut bool) {
        if *line_start {
            out.push_str(&"    ".repeat(indent));
            *line_start = false;
        }
    }

    fn trim_trailing_space(out: &mut String) {
        while out.ends_with(' ') || out.ends_with('\t') {
            out.pop();
        }
    }

    fn newline(out: &mut String, line_start: &mut bool) {
        trim_trailing_space(out);
        if !out.ends_with('\n') {
            out.push('\n');
        }
        *line_start = true;
    }

    while i < chars.len() {
        let ch = chars[i];
        let next = next_non_space(&chars, i + 1);

        if in_string {
            write_indent(&mut out, indent, &mut line_start);
            out.push(ch);
            if escape {
                escape = false;
            } else if ch == '\\' {
                escape = true;
            } else if ch == '"' {
                in_string = false;
            }
            i += 1;
            continue;
        }

        match ch {
            '"' => {
                write_indent(&mut out, indent, &mut line_start);
                out.push(ch);
                in_string = true;
            }
            '{' => {
                write_indent(&mut out, indent, &mut line_start);
                out.push('{');
                brace_depth += 1;
                newline(&mut out, &mut line_start);
                indent += 1;
            }
            '}' => {
                indent = indent.saturating_sub(1);
                brace_depth = brace_depth.saturating_sub(1);
                newline(&mut out, &mut line_start);
                write_indent(&mut out, indent, &mut line_start);
                out.push('}');
                if matches!(next, Some(',') | Some(';')) {
                    i += 1;
                    out.push(chars[i]);
                }
                newline(&mut out, &mut line_start);
            }
            '(' => {
                write_indent(&mut out, indent, &mut line_start);
                out.push('(');
                paren_depth += 1;
            }
            ')' => {
                write_indent(&mut out, indent, &mut line_start);
                out.push(')');
                paren_depth = paren_depth.saturating_sub(1);
            }
            '[' => {
                write_indent(&mut out, indent, &mut line_start);
                out.push('[');
                bracket_depth += 1;
            }
            ']' => {
                write_indent(&mut out, indent, &mut line_start);
                out.push(']');
                bracket_depth = bracket_depth.saturating_sub(1);
                if bracket_depth == 0
                    && brace_depth == 0
                    && matches!(next, Some('#' | 'p' | 'i' | 'm'))
                {
                    newline(&mut out, &mut line_start);
                }
            }
            ';' => {
                write_indent(&mut out, indent, &mut line_start);
                out.push(';');
                newline(&mut out, &mut line_start);
            }
            ',' => {
                write_indent(&mut out, indent, &mut line_start);
                out.push(',');
                if brace_depth > 0 && bracket_depth == 0 {
                    newline(&mut out, &mut line_start);
                } else if !matches!(next, Some(')' | ']' | '}' | ',' | ';')) {
                    out.push(' ');
                }
            }
            '\n' | '\r' | '\t' | ' ' => {
                if !line_start && !out.ends_with(' ') && !out.ends_with('\n') {
                    out.push(' ');
                }
            }
            _ => {
                write_indent(&mut out, indent, &mut line_start);
                out.push(ch);
            }
        }

        i += 1;
    }

    let mut formatted = out
        .lines()
        .map(str::trim_end)
        .collect::<Vec<_>>()
        .join("\n");
    while formatted.ends_with("\n\n") {
        formatted.pop();
    }
    formatted
}
