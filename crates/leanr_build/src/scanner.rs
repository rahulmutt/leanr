//! Total header scanner (spec §Architecture, component 5): extracts
//! `module` / `prelude` / import statements from the top of a `.lean`
//! file. Grammar surveyed empirically over the pinned Mathlib closure:
//! `[module] [prelude] ([public|private] [meta] import [all] Name)*`.
//! Anything unrecognized simply ends the header — declarations like
//! `public def` must not be misread as imports.

use crate::modules::ModuleName;

#[derive(Debug, Default, PartialEq)]
pub struct Header {
    pub is_module: bool,
    pub prelude: bool,
    pub imports: Vec<ModuleName>,
}

/// Total over arbitrary bytes: invalid UTF-8 is decoded lossily and the
/// replacement characters end the header at the first token they corrupt.
#[allow(unused_assignments)]
pub fn scan_header(bytes: &[u8]) -> Header {
    let text = String::from_utf8_lossy(bytes);
    let mut lx = Lexer { s: &text, pos: 0 };
    let mut h = Header::default();

    lx.skip_trivia();
    if lx.eat_word("module") {
        h.is_module = true;
        lx.skip_trivia();
    }
    if lx.eat_word("prelude") {
        h.prelude = true;
        lx.skip_trivia();
    }
    loop {
        let mark = lx.pos;
        // Modifiers: at most one visibility, at most one `meta`.
        let _vis = lx.eat_word("public") || lx.eat_word("private");
        lx.skip_trivia();
        let _meta = lx.eat_word("meta");
        lx.skip_trivia();
        if !lx.eat_word("import") {
            lx.pos = mark; // `public def …`, EOF, or any declaration
            break;
        }
        lx.skip_trivia();
        // `import all Foo`: `all` is a keyword iff a name follows it;
        // otherwise `all` itself is the imported module.
        let mut name = lx.module_name();
        if name.as_ref().map(|m| m.to_string()).as_deref() == Some("all") {
            lx.skip_trivia();
            if let Some(real) = lx.module_name() {
                // Only use the real name if it starts with uppercase or guillemet (Lean convention).
                // This prevents parsing declaration keywords like 'def' as module names.
                let real_str = real.to_string();
                let first_char = real_str.chars().next();
                if first_char == Some('«') || first_char.map(|c| c.is_uppercase()).unwrap_or(false)
                {
                    name = Some(real);
                }
            }
        }
        match name {
            Some(m) => h.imports.push(m),
            None => {
                lx.pos = mark;
                break;
            }
        }
        lx.skip_trivia();
    }
    h
}

struct Lexer<'a> {
    s: &'a str,
    pos: usize,
}

impl<'a> Lexer<'a> {
    fn rest(&self) -> &'a str {
        &self.s[self.pos..]
    }

    /// Skip whitespace, `--` line comments, and (nested) `/- -/` block
    /// comments. An unterminated block comment consumes to EOF.
    fn skip_trivia(&mut self) {
        loop {
            let r = self.rest();
            if let Some(c) = r.chars().next() {
                if c.is_whitespace() {
                    self.pos += c.len_utf8();
                    continue;
                }
            }
            if r.starts_with("--") {
                match r.find('\n') {
                    Some(i) => self.pos += i + 1,
                    None => self.pos = self.s.len(),
                }
                continue;
            }
            if r.starts_with("/-") {
                let mut depth = 1usize;
                let mut i = 2;
                let b = r.as_bytes();
                while i < b.len() && depth > 0 {
                    if r[i..].starts_with("/-") {
                        depth += 1;
                        i += 2;
                    } else if r[i..].starts_with("-/") {
                        depth -= 1;
                        i += 2;
                    } else {
                        // advance one whole char, not one byte
                        let ch = r[i..].chars().next().unwrap();
                        i += ch.len_utf8();
                    }
                }
                self.pos += i;
                continue;
            }
            break;
        }
    }

    /// Consume `word` iff the next token is exactly that identifier.
    fn eat_word(&mut self, word: &str) -> bool {
        let r = self.rest();
        if let Some(rest) = r.strip_prefix(word) {
            let after = rest.chars().next();
            if (after.is_none() || (!after.unwrap().is_alphanumeric() && after != Some('_')))
                && after != Some('.')
                && after != Some('«')
            {
                self.pos += word.len();
                return true;
            }
        }
        false
    }

    /// Consume a dotted module name: `comp ('.' comp)*` where comp is an
    /// identifier (`[A-Za-z_][A-Za-z0-9_'!?]*`, plus any non-ASCII
    /// letter Lean allows — we accept any non-ASCII alphanumeric) or a
    /// `«...»` atom. Returns None (consuming nothing) if no name starts here.
    fn module_name(&mut self) -> Option<ModuleName> {
        let start = self.pos;
        let mut raw = String::new();
        loop {
            let r = self.rest();
            let mut chars = r.chars();
            match chars.next() {
                Some('«') => {
                    raw.push('«');
                    self.pos += '«'.len_utf8();
                    loop {
                        let c = self.rest().chars().next();
                        match c {
                            Some(c) => {
                                raw.push(c);
                                self.pos += c.len_utf8();
                                if c == '»' {
                                    break;
                                }
                            }
                            None => {
                                self.pos = start;
                                return None; // unclosed
                            }
                        }
                    }
                }
                Some(c) if c.is_alphabetic() || c == '_' => {
                    while let Some(c) = self.rest().chars().next() {
                        if c.is_alphanumeric() || matches!(c, '_' | '\'' | '!' | '?') {
                            raw.push(c);
                            self.pos += c.len_utf8();
                        } else {
                            break;
                        }
                    }
                }
                _ => {
                    self.pos = start;
                    return None;
                }
            }
            if self.rest().starts_with('.') {
                // A dot continues the name only if a component follows.
                let peek = self.s[self.pos + 1..].chars().next();
                let continues =
                    matches!(peek, Some(c) if c.is_alphabetic() || c == '_' || c == '«');
                if continues {
                    raw.push('.');
                    self.pos += 1;
                    continue;
                }
            }
            break;
        }
        match ModuleName::parse(&raw) {
            Ok(m) => Some(m),
            Err(_) => {
                self.pos = start;
                None
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn imports(src: &str) -> Vec<String> {
        scan_header(src.as_bytes())
            .imports
            .iter()
            .map(|m| m.to_string())
            .collect()
    }

    #[test]
    fn plain_imports() {
        let h = scan_header(b"import Foo\nimport Foo.Bar\ndef x := 1\nimport Nope");
        assert_eq!(
            h.imports.iter().map(|m| m.to_string()).collect::<Vec<_>>(),
            ["Foo", "Foo.Bar"]
        );
        assert!(!h.is_module && !h.prelude);
    }

    #[test]
    fn module_system_header_with_visibility_and_meta() {
        let src = "/- copyright -/\nmodule\n\npublic import Aesop\npublic meta import B.C\nmeta import D\nprivate import E\nimport all F\n\n/-! # doc -/\ntheorem t : True := trivial";
        let h = scan_header(src.as_bytes());
        assert!(h.is_module);
        assert_eq!(
            h.imports.iter().map(|m| m.to_string()).collect::<Vec<_>>(),
            ["Aesop", "B.C", "D", "E", "F"]
        );
    }

    #[test]
    fn prelude_and_trailing_line_comment_on_module() {
        let h = scan_header(b"module  -- shake: keep-all\nprelude\nimport Init.Core\n");
        assert!(h.is_module && h.prelude);
        assert_eq!(h.imports[0].to_string(), "Init.Core");
    }

    #[test]
    fn comments_anywhere_in_the_header() {
        let src = "-- line\n/- block /- nested -/ still -/ import A\nimport --mid\n B\n";
        assert_eq!(imports(src), ["A", "B"]);
    }

    #[test]
    fn import_all_takes_the_following_name() {
        assert_eq!(imports("import all Mathlib.X\n"), ["Mathlib.X"]);
        // `all` with no name after it is the imported module itself.
        assert_eq!(imports("import all\ndef x := 1"), ["all"]);
    }

    #[test]
    fn modifier_words_starting_a_declaration_end_the_header() {
        // `public def` / `meta def` are declarations, not imports.
        assert_eq!(imports("import A\npublic def f := 1\n"), ["A"]);
        assert_eq!(imports("import A\nmeta def f := 1\n"), ["A"]);
    }

    #[test]
    fn guillemet_import_and_word_module_only_at_start() {
        assert_eq!(imports("import «weird.name».Sub\n"), ["weird.name.Sub"]);
        // 'module' later in a file is prose/code, not a header keyword.
        let h = scan_header(b"import A\nmodule\n");
        assert!(!h.is_module);
        assert_eq!(h.imports.len(), 1);
    }

    #[test]
    fn degenerate_inputs_are_calm() {
        for src in [
            &b""[..],
            b"--",
            b"/- unterminated",
            b"import",
            b"import .",
            b"import \xFF\xFE",
            b"public",
            b"prelude",
            b"module",
            b"\xFF\xFF\xFF",
        ] {
            let _ = scan_header(src); // must not panic; imports may be empty
        }
        assert!(scan_header(b"import").imports.is_empty());
    }

    proptest! {
        /// Never-panic guarantee over arbitrary bytes (THREAT_MODEL.md
        /// discipline, same as the olean decoder).
        #[test]
        fn scan_header_never_panics(bytes in proptest::collection::vec(any::<u8>(), 0..4096)) {
            let _ = scan_header(&bytes);
        }
    }
}
