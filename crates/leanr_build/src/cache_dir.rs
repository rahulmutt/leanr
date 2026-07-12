//! leanr's per-user cache root (M2b spec §Layout): `$XDG_CACHE_HOME/leanr`,
//! falling back to `~/.cache/leanr`. Pure resolution — env values are
//! passed in by the caller; the CLI owns env reads (the `discover_roots`
//! convention in leanr_cli).

use std::ffi::OsStr;
use std::path::PathBuf;

/// Resolve the leanr cache root from caller-supplied env values. Empty
/// values are treated as unset (XDG basedir spec). `None` only when
/// neither `XDG_CACHE_HOME` nor `HOME` is usable.
pub fn cache_root(xdg_cache_home: Option<&OsStr>, home: Option<&OsStr>) -> Option<PathBuf> {
    if let Some(x) = xdg_cache_home {
        if !x.is_empty() {
            return Some(PathBuf::from(x).join("leanr"));
        }
    }
    home.filter(|h| !h.is_empty())
        .map(|h| PathBuf::from(h).join(".cache").join("leanr"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::OsStr;
    use std::path::Path;

    #[test]
    fn xdg_cache_home_wins_when_set() {
        let got = cache_root(Some(OsStr::new("/xdg")), Some(OsStr::new("/home/u"))).unwrap();
        assert_eq!(got, Path::new("/xdg/leanr"));
    }

    #[test]
    fn empty_xdg_falls_back_to_home() {
        let got = cache_root(Some(OsStr::new("")), Some(OsStr::new("/home/u"))).unwrap();
        assert_eq!(got, Path::new("/home/u/.cache/leanr"));
    }

    #[test]
    fn unset_xdg_falls_back_to_home() {
        let got = cache_root(None, Some(OsStr::new("/home/u"))).unwrap();
        assert_eq!(got, Path::new("/home/u/.cache/leanr"));
    }

    #[test]
    fn neither_set_is_none() {
        assert!(cache_root(None, None).is_none());
        assert!(cache_root(Some(OsStr::new("")), Some(OsStr::new(""))).is_none());
    }
}
