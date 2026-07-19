//! Trivia baseline (spec §The first-slice rules, rule 1): a final,
//! line-oriented normalization applied uniformly to formatted AND
//! preserve-fallback output. Only mutates non-significant trivia, so it
//! is parse-safe by construction. Trailing-whitespace stripping also
//! trims trailing whitespace inside line comments (a Lean line comment
//! runs to end of line) — see the comment invariant in verify.rs.

pub fn normalize(s: &str) -> String {
    let mut lines: Vec<&str> = s.lines().map(str::trim_end).collect();
    // Collapse runs of 2+ blank lines to a single blank line.
    let mut collapsed: Vec<&str> = Vec::with_capacity(lines.len());
    let mut prev_blank = false;
    for line in lines.drain(..) {
        let blank = line.is_empty();
        if blank && prev_blank {
            continue;
        }
        collapsed.push(line);
        prev_blank = blank;
    }
    // Drop trailing blank lines.
    while collapsed.last() == Some(&"") {
        collapsed.pop();
    }
    if collapsed.is_empty() {
        return String::new();
    }
    let mut out = collapsed.join("\n");
    out.push('\n');
    out
}

#[cfg(test)]
mod tests {
    use super::normalize;

    #[test]
    fn strips_trailing_whitespace_including_after_line_comments() {
        assert_eq!(
            normalize("def x := 1   \n-- note   \n"),
            "def x := 1\n-- note\n"
        );
    }

    #[test]
    fn collapses_blank_line_runs_to_one() {
        assert_eq!(normalize("a\n\n\n\nb\n"), "a\n\nb\n");
    }

    #[test]
    fn ensures_single_trailing_newline() {
        assert_eq!(normalize("a"), "a\n");
        assert_eq!(normalize("a\n\n\n"), "a\n");
        assert_eq!(normalize(""), "");
    }

    #[test]
    fn is_idempotent() {
        let messy = "a  \n\n\n\nb -- x  \n\n";
        let once = normalize(messy);
        assert_eq!(normalize(&once), once);
    }
}
