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

/// Renders generated tokens as text. Its layout is irrelevant: the final
/// pass, [`super::pretty::format_items`], lays out the whole file.
pub(crate) fn render_ts(ts: TokenStream) -> String {
    ts.to_string()
}
