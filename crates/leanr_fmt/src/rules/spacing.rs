//! Single-line operator spacing (spec §The first-slice rules, rule 2).
//! Normalizes whitespace-trivia adjacent to target operators to a single
//! space, but ONLY on a single line — the moment the whitespace spans
//! lines (indentation may be significant), it is left verbatim (owned by
//! `trivia::normalize_ws_trivia`, Task 3).

const TARGET_OPERATORS: &[&str] = &[":=", "→"];

fn is_target(tok: Option<&str>) -> bool {
    matches!(tok, Some(t) if TARGET_OPERATORS.contains(&t))
}

/// Given a whitespace-trivia token's text and the atom texts of the
/// nearest significant (non-trivia) tokens on either side, return
/// `Some(normalized)` when the spacing rule applies, else `None` (leave
/// the whitespace to `trivia::normalize_ws_trivia`).
///
/// Applies only when `ws_text` contains no `\n` (single-line) AND one
/// neighbor is a target operator (`:=` or `→`); the normalized form is a
/// single space.
pub fn normalize_ws(
    prev_significant: Option<&str>,
    ws_text: &str,
    next_significant: Option<&str>,
) -> Option<String> {
    if ws_text.contains('\n') {
        return None; // multi-line: leave to normalize_ws_trivia
    }
    if is_target(prev_significant) || is_target(next_significant) {
        Some(" ".to_string())
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::normalize_ws;

    #[test]
    fn collapses_multiple_spaces_around_assign() {
        assert_eq!(
            normalize_ws(Some("x"), "   ", Some(":=")).as_deref(),
            Some(" ")
        );
        assert_eq!(
            normalize_ws(Some(":="), "   ", Some("1")).as_deref(),
            Some(" ")
        );
    }

    #[test]
    fn leaves_multiline_whitespace_untouched() {
        assert_eq!(normalize_ws(Some("x"), "\n  ", Some(":=")), None);
    }

    #[test]
    fn ignores_non_target_neighbors() {
        assert_eq!(normalize_ws(Some("a"), "  ", Some("b")), None);
    }

    #[test]
    fn matches_arrow_target() {
        assert_eq!(
            normalize_ws(Some("x"), "  ", Some("→")).as_deref(),
            Some(" ")
        );
    }

    #[test]
    fn already_single_spaced_stays_single_spaced() {
        assert_eq!(
            normalize_ws(Some("x"), " ", Some(":=")).as_deref(),
            Some(" ")
        );
    }
}
