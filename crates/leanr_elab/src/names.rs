//! Hierarchical-name algebra over a (scratch, base) store pair, and the
//! environment's name tables (`protectedExt`, `namespacesExt`,
//! `aliasExtension`). The anonymous name is `None`.
//!
//! Every function takes `st` and `base` as `Store`'s own methods do: an
//! id is read from `base` when it is persistent-region and from `st` when
//! it is scratch-region, and a name built here is interned with `base` so
//! it is the same `NameId` the persistent store already has for it (and
//! hence the one `EnvView::get` looks up).

use std::collections::{HashMap, HashSet};
use std::sync::LazyLock;

use leanr_kernel::bank::names::NameRow;
use leanr_kernel::bank::{NameId, Store};
use leanr_kernel::KernelError;

/// The three name tables the resolver reads. oracle: `protectedExt`
/// (`Lean/Modifiers.lean:17-21`), `namespacesExt`
/// (`Lean/Namespace.lean:55-62`) and `aliasExtension`
/// (`ResolveName.lean:63-92`).
#[derive(Clone, Debug, Default)]
pub struct NameTables {
    protected: HashSet<NameId>,
    namespaces: HashSet<Option<NameId>>,
    /// alias → targets, most recently added first (`addAliasEntry`).
    aliases: HashMap<NameId, Vec<NameId>>,
}

static EMPTY: LazyLock<NameTables> = LazyLock::new(NameTables::default);

impl NameTables {
    /// The tables from their decoded entries. `aliases` is folded in order
    /// with `addAliasEntry` (`ResolveName.lean:63-66`).
    pub fn new(
        protected: &[NameId],
        namespaces: &[Option<NameId>],
        aliases: &[(NameId, NameId)],
    ) -> NameTables {
        let mut t = NameTables {
            protected: protected.iter().copied().collect(),
            namespaces: namespaces.iter().copied().collect(),
            aliases: HashMap::new(),
        };
        for &(a, e) in aliases {
            t.add_alias_entry(a, e);
        }
        t
    }

    /// No protected names, no namespaces, no aliases: what a term-only
    /// caller resolves against (`ResolveCtx::root`).
    pub fn empty() -> &'static NameTables {
        &EMPTY
    }

    /// oracle: `addAliasEntry` (`ResolveName.lean:63-66`): a new target is
    /// consed onto the front; a target already present is ignored.
    fn add_alias_entry(&mut self, a: NameId, e: NameId) {
        let es = self.aliases.entry(a).or_default();
        if !es.contains(&e) {
            es.insert(0, e);
        }
    }

    /// oracle: `isProtected` (`Lean/Modifiers.lean:20-21`).
    pub fn is_protected(&self, n: NameId) -> bool {
        self.protected.contains(&n)
    }

    /// oracle: `isNamespace` (`Lean/Namespace.lean:61-62`).
    pub fn is_namespace(&self, n: Option<NameId>) -> bool {
        self.namespaces.contains(&n)
    }

    /// oracle: `getAliases` (`ResolveName.lean:85-92`): with
    /// `skip_protected`, protected targets are dropped.
    pub fn get_aliases(&self, a: NameId, skip_protected: bool) -> Vec<NameId> {
        match self.aliases.get(&a) {
            None => Vec::new(),
            Some(es) if skip_protected => es
                .iter()
                .copied()
                .filter(|&e| !self.is_protected(e))
                .collect(),
            Some(es) => es.clone(),
        }
    }

    /// oracle: `registerNamespace` (`Lean/Namespace.lean:55-58`).
    pub fn register_namespace(&mut self, n: Option<NameId>) {
        self.namespaces.insert(n);
    }

    /// oracle: `addProtected` (`Lean/Modifiers.lean:17-18`).
    pub fn add_protected(&mut self, n: NameId) {
        self.protected.insert(n);
    }

    /// oracle: `registerNamePrefixes` (`AddDecl.lean:54-66`). `n` must be
    /// readable from `st` alone (a persistent name in the persistent
    /// store). A last component starting with `_` registers nothing;
    /// otherwise `go` registers each proper prefix while it is a
    /// `isNamespaceName` (`:49-52`, a chain of string components).
    /// `privateToUserName` is the identity: `private` is seamed.
    pub fn register_name_prefixes(&mut self, st: &Store, n: NameId) {
        match last_str(st, None, n) {
            Some(s) if !s.starts_with('_') => {}
            _ => return,
        }
        let mut cur = n;
        // `go`: `.str p _ => if isNamespaceName p then go (register p) p`.
        while let NameRow::Str { parent: p, .. } = *st.name_row(None, cur) {
            match p {
                Some(p) if is_namespace_name(st, p) => {
                    self.register_namespace(Some(p));
                    cur = p;
                }
                _ => break,
            }
        }
    }
}

/// oracle: `isNamespaceName` (`AddDecl.lean:49-52`): a non-anonymous
/// chain of string components.
fn is_namespace_name(st: &Store, n: NameId) -> bool {
    let mut cur = Some(n);
    while let Some(c) = cur {
        match *st.name_row(None, c) {
            NameRow::Str { parent, .. } => cur = parent,
            NameRow::Num { .. } => return false,
        }
    }
    true
}

/// oracle: `Name.appendCore` (`Init/Prelude.lean:4828-4831`): `b`'s
/// components rebuilt onto `a`. leanr names carry no macro scopes, so
/// `Name.append` is `appendCore`.
pub(crate) fn append(
    st: &mut Store,
    base: Option<&Store>,
    a: Option<NameId>,
    b: Option<NameId>,
) -> Result<Option<NameId>, KernelError> {
    let mut rows = Vec::new();
    let mut cur = b;
    while let Some(c) = cur {
        let row = *st.name_row(base, c);
        cur = match row {
            NameRow::Str { parent, .. } | NameRow::Num { parent, .. } => parent,
        };
        rows.push(row);
    }
    let mut out = a;
    for row in rows.into_iter().rev() {
        out = Some(push_row(st, base, out, row)?);
    }
    Ok(out)
}

/// `row`'s component on top of `parent`.
fn push_row(
    st: &mut Store,
    base: Option<&Store>,
    parent: Option<NameId>,
    row: NameRow,
) -> Result<NameId, KernelError> {
    match row {
        NameRow::Str { part, .. } => st.name_str(base, parent, part),
        NameRow::Num { part, .. } => st.name_num(base, parent, part),
    }
}

/// oracle: `Name.getPrefix`.
pub(crate) fn parent(st: &Store, base: Option<&Store>, n: NameId) -> Option<NameId> {
    match *st.name_row(base, n) {
        NameRow::Str { parent, .. } | NameRow::Num { parent, .. } => parent,
    }
}

/// The last component's text, or `None` for a numeric component.
pub(crate) fn last_str<'a>(st: &'a Store, base: Option<&'a Store>, n: NameId) -> Option<&'a str> {
    match *st.name_row(base, n) {
        NameRow::Str { part, .. } => Some(st.str_at(base, part)),
        NameRow::Num { .. } => None,
    }
}

/// oracle: `Name.isAtomic` (`Lean/Data/Name.lean:173-177`): the
/// anonymous name and every one-component name.
pub(crate) fn is_atomic(st: &Store, base: Option<&Store>, n: Option<NameId>) -> bool {
    n.is_none_or(|n| parent(st, base, n).is_none())
}

/// oracle: `Name.isPrefixOf` (`Lean/Data/Name.lean:55-58`):
/// `p == n || isPrefixOf p n.getPrefix`, the anonymous name a prefix of
/// every name.
pub(crate) fn is_prefix_of(
    st: &Store,
    base: Option<&Store>,
    p: Option<NameId>,
    n: Option<NameId>,
) -> bool {
    let mut cur = n;
    loop {
        if cur == p {
            return true;
        }
        match cur {
            None => return false,
            Some(c) => cur = parent(st, base, c),
        }
    }
}

/// oracle: `Name.isSuffixOf` (`Lean/Data/Name.lean:61-65`), component by
/// component from the end. Components are compared by value (string
/// text, numeral), so a scratch-region and a persistent-region id for
/// equal components agree.
pub(crate) fn is_suffix_of(
    st: &Store,
    base: Option<&Store>,
    s: Option<NameId>,
    n: Option<NameId>,
) -> bool {
    let (mut s, mut n) = (s, n);
    loop {
        let Some(sc) = s else { return true };
        let Some(nc) = n else { return false };
        match (*st.name_row(base, sc), *st.name_row(base, nc)) {
            (
                NameRow::Str {
                    parent: sp,
                    part: a,
                },
                NameRow::Str {
                    parent: np,
                    part: b,
                },
            ) => {
                if st.str_at(base, a) != st.str_at(base, b) {
                    return false;
                }
                (s, n) = (sp, np);
            }
            (
                NameRow::Num {
                    parent: sp,
                    part: a,
                },
                NameRow::Num {
                    parent: np,
                    part: b,
                },
            ) => {
                if st.nat_at(base, a) != st.nat_at(base, b) {
                    return false;
                }
                (s, n) = (sp, np);
            }
            _ => return false,
        }
    }
}

/// oracle: `Name.replacePrefix` (`Init/Meta/Defs.lean:292-296`): the
/// longest ancestor of `n` (itself included) equal to `prefix` becomes
/// `new`, and the components below it are rebuilt on top. With no such
/// ancestor `n` is rebuilt unchanged, except that an anonymous `prefix`
/// matches the root, so the result is `new ++ n`.
pub(crate) fn replace_prefix(
    st: &mut Store,
    base: Option<&Store>,
    n: Option<NameId>,
    prefix: Option<NameId>,
    new: Option<NameId>,
) -> Result<Option<NameId>, KernelError> {
    let mut rows = Vec::new();
    let mut cur = n;
    // `| anonymous, anonymous, newP => newP` / `| anonymous, _, _ => anonymous`.
    let mut out = loop {
        match cur {
            c if c == prefix => break new,
            None => break None,
            Some(c) => {
                let row = *st.name_row(base, c);
                rows.push(row);
                cur = parent(st, base, c);
            }
        }
    };
    for row in rows.into_iter().rev() {
        out = Some(push_row(st, base, out, row)?);
    }
    Ok(out)
}

/// The single-component name `s`.
pub(crate) fn mk_atomic(
    st: &mut Store,
    base: Option<&Store>,
    s: &str,
) -> Result<NameId, KernelError> {
    let sid = st.intern_str(base, s)?;
    st.name_str(base, None, sid)
}

/// The name as Lean prints it; `[anonymous]` for `None`.
pub(crate) fn render(st: &Store, base: Option<&Store>, n: Option<NameId>) -> String {
    match n {
        None => "[anonymous]".to_string(),
        Some(_) => st.to_name(base, n).to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use leanr_kernel::bank::{NameId, Store};

    fn mk(st: &mut Store, s: &str) -> NameId {
        let mut id = None;
        for part in s.split('.') {
            let sid = st.intern_str(None, part).unwrap();
            id = Some(st.name_str(None, id, sid).unwrap());
        }
        id.unwrap()
    }

    /// `AddDecl.lean:54-66`: `registerNamePrefixes` registers every proper
    /// prefix (`go`, guarded by `isNamespaceName`), never the name itself
    /// nor the anonymous name, and nothing when the last component starts
    /// with `_`.
    #[test]
    fn register_name_prefixes_skips_underscore_last_components() {
        let mut st = Store::persistent();
        let a = mk(&mut st, "A");
        let ab = mk(&mut st, "A.B");
        let abf = mk(&mut st, "A.B.f");
        let proof = mk(&mut st, "A._proof_1");
        let mut t = NameTables::default();
        t.register_name_prefixes(&st, abf);
        assert!(t.is_namespace(Some(ab)));
        assert!(t.is_namespace(Some(a)));
        assert!(!t.is_namespace(Some(abf)));
        assert!(!t.is_namespace(None));

        let mut t = NameTables::default();
        t.register_name_prefixes(&st, proof);
        assert!(!t.is_namespace(Some(a)));
        assert!(!t.is_namespace(Some(proof)));
    }

    /// `addAliasEntry` (`ResolveName.lean:63-66`) prepends a new target and
    /// ignores a duplicate; `getAliases` (`:85-92`) with `skipProtected`
    /// drops protected targets.
    #[test]
    fn aliases_fold_like_add_alias_entry() {
        let mut st = Store::persistent();
        let a = mk(&mut st, "a");
        let x = mk(&mut st, "X.x");
        let y = mk(&mut st, "Y.y");
        let t = NameTables::new(&[], &[], &[(a, x), (a, y), (a, x)]);
        assert_eq!(t.get_aliases(a, false), vec![y, x]);
        assert_eq!(t.get_aliases(a, true), vec![y, x]);
        assert_eq!(t.get_aliases(x, false), Vec::<NameId>::new());
        let t = NameTables::new(&[y], &[], &[(a, x), (a, y), (a, x)]);
        assert_eq!(t.get_aliases(a, false), vec![y, x]);
        assert_eq!(t.get_aliases(a, true), vec![x]);
    }

    /// `Name.isSuffixOf`/`Name.isPrefixOf` (`Lean/Data/Name.lean:55-65`),
    /// `Name.replacePrefix` (`Init/Meta/Defs.lean:292-296`).
    #[test]
    fn suffix_and_prefix_algebra() {
        let mut st = Store::persistent();
        let f = mk(&mut st, "f");
        let a = mk(&mut st, "A");
        let ab = mk(&mut st, "A.B");
        let bf = mk(&mut st, "B.f");
        let af = mk(&mut st, "A.f");
        let abf = mk(&mut st, "A.B.f");
        assert!(is_suffix_of(&st, None, Some(f), Some(abf)));
        assert!(is_suffix_of(&st, None, Some(bf), Some(abf)));
        assert!(!is_suffix_of(&st, None, Some(af), Some(abf)));
        assert!(is_suffix_of(&st, None, None, Some(abf)));
        assert!(!is_suffix_of(&st, None, Some(abf), Some(bf)));

        assert!(is_prefix_of(&st, None, None, Some(ab)));
        assert!(is_prefix_of(&st, None, Some(a), Some(ab)));
        assert!(is_prefix_of(&st, None, Some(ab), Some(ab)));
        assert!(!is_prefix_of(&st, None, Some(ab), Some(a)));
        assert!(!is_prefix_of(&st, None, Some(ab), None));

        let root_ax = mk(&mut st, "_root_.A.x");
        let root = mk(&mut st, "_root_");
        let ax = mk(&mut st, "A.x");
        assert_eq!(
            replace_prefix(&mut st, None, Some(root_ax), Some(root), None).unwrap(),
            Some(ax)
        );
        // Not a prefix: rebuilt unchanged.
        assert_eq!(
            replace_prefix(&mut st, None, Some(ax), Some(root), None).unwrap(),
            Some(ax)
        );
        // `append` is `Name.appendCore` (`Init/Prelude.lean:4828-4831`).
        assert_eq!(append(&mut st, None, Some(a), Some(bf)).unwrap(), Some(abf));
        assert_eq!(append(&mut st, None, None, Some(bf)).unwrap(), Some(bf));
        assert_eq!(append(&mut st, None, Some(a), None).unwrap(), Some(a));

        assert!(is_atomic(&st, None, Some(a)));
        assert!(!is_atomic(&st, None, Some(ab)));
        // `Name.isAtomic` (`Lean/Data/Name.lean:173-177`): `anonymous => true`.
        assert!(is_atomic(&st, None, None));
        assert_eq!(parent(&st, None, ab), Some(a));
        assert_eq!(last_str(&st, None, abf), Some("f"));
        assert_eq!(render(&st, None, Some(abf)), "A.B.f");
        assert_eq!(render(&st, None, None), "[anonymous]");
    }
}
