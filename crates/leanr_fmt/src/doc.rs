//! Hand-rolled Wadler/Leijen pretty-printer IR (spec §Engine). No
//! external dependency. `layout` chooses flat-vs-broken per `Group`
//! against the remaining width; `Line` is a space when flat and a
//! newline (+ current indent) when broken; `Hardline` always breaks.

#[derive(Clone, Debug)]
pub enum Doc {
    Nil,
    Text(String),
    Line,
    Hardline,
    Nest(u16, Box<Doc>),
    Group(Box<Doc>),
    Concat(Vec<Doc>),
}

impl Doc {
    pub fn nil() -> Doc {
        Doc::Nil
    }
    pub fn text(s: impl Into<String>) -> Doc {
        Doc::Text(s.into())
    }
    pub fn line() -> Doc {
        Doc::Line
    }
    pub fn hardline() -> Doc {
        Doc::Hardline
    }
    pub fn nest(indent: u16, d: Doc) -> Doc {
        Doc::Nest(indent, Box::new(d))
    }
    pub fn group(d: Doc) -> Doc {
        Doc::Group(Box::new(d))
    }
    pub fn concat(ds: Vec<Doc>) -> Doc {
        Doc::Concat(ds)
    }
}

// A `Hardline` anywhere in a group forces the group to break.
fn contains_hardline(d: &Doc) -> bool {
    match d {
        Doc::Hardline => true,
        Doc::Nil | Doc::Text(_) | Doc::Line => false,
        Doc::Nest(_, inner) | Doc::Group(inner) => contains_hardline(inner),
        Doc::Concat(ds) => ds.iter().any(contains_hardline),
    }
}

// Would `d` fit flat in `remaining` columns? `Line` counts as one space;
// `Hardline` makes it not fit (forces a break).
fn fits(d: &Doc, mut remaining: isize) -> bool {
    let mut stack = vec![d];
    while let Some(top) = stack.pop() {
        if remaining < 0 {
            return false;
        }
        match top {
            Doc::Nil => {}
            Doc::Text(s) => remaining -= s.chars().count() as isize,
            Doc::Line => remaining -= 1,
            Doc::Hardline => return false,
            Doc::Nest(_, inner) | Doc::Group(inner) => stack.push(inner),
            Doc::Concat(ds) => {
                for sub in ds.iter().rev() {
                    stack.push(sub);
                }
            }
        }
    }
    remaining >= 0
}

pub fn layout(doc: &Doc, width: usize) -> String {
    let mut out = String::new();
    let mut col: usize = 0;
    // (indent, flat?, doc)
    let mut stack: Vec<(u16, bool, &Doc)> = vec![(0, false, doc)];
    while let Some((indent, flat, top)) = stack.pop() {
        match top {
            Doc::Nil => {}
            Doc::Text(s) => {
                out.push_str(s);
                col += s.chars().count();
            }
            Doc::Line => {
                if flat {
                    out.push(' ');
                    col += 1;
                } else {
                    out.push('\n');
                    for _ in 0..indent {
                        out.push(' ');
                    }
                    col = indent as usize;
                }
            }
            Doc::Hardline => {
                out.push('\n');
                for _ in 0..indent {
                    out.push(' ');
                }
                col = indent as usize;
            }
            Doc::Nest(n, inner) => stack.push((indent + n, flat, inner)),
            Doc::Concat(ds) => {
                for sub in ds.iter().rev() {
                    stack.push((indent, flat, sub));
                }
            }
            Doc::Group(inner) => {
                let remaining = width as isize - col as isize;
                let flat_here = !contains_hardline(inner) && fits(inner, remaining);
                stack.push((indent, flat_here, inner));
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flat_group_fits_uses_spaces() {
        let d = Doc::group(Doc::concat(vec![
            Doc::text("a"),
            Doc::line(),
            Doc::text("b"),
        ]));
        assert_eq!(layout(&d, 80), "a b");
    }

    #[test]
    fn broken_group_over_width_uses_newlines_and_nest() {
        let d = Doc::group(Doc::nest(
            2,
            Doc::concat(vec![Doc::text("aaaa"), Doc::line(), Doc::text("bbbb")]),
        ));
        // width 6 cannot fit "aaaa bbbb" (9), so the group breaks.
        assert_eq!(layout(&d, 6), "aaaa\n  bbbb");
    }

    #[test]
    fn hardline_always_breaks_even_when_it_would_fit() {
        let d = Doc::group(Doc::concat(vec![
            Doc::text("a"),
            Doc::hardline(),
            Doc::text("b"),
        ]));
        assert_eq!(layout(&d, 80), "a\nb");
    }
}
