//! Id-native `Environment` — representation-only port of `crate::env`
//! (oracle: environment.cpp; per-function line cites below). The
//! persistent bank this module owns IS the `Environment`'s storage
//! (spec §2's "persistent bank, owned by `Environment`"): every
//! `NameId`/`ExprId` reachable from `constants` lives in `self.store`
//! (region 0) — never scratch. Declarations are checked in a fresh,
//! per-declaration scratch `Store` (`add_decl`'s `let mut scratch =
//! Store::scratch();`, Global Constraints' region discipline) and only
//! the surviving `ConstantInfo`(s) cross into the persistent store, via
//! `add_core`'s `promote_constant_info` — the single admission choke
//! point, mirroring Arc `add_core`'s "single choke point" role but
//! promoting ids instead of structurally interning `Arc`s (dedup
//! already happened at interning time; the Arc `interner.intern_input`/
//! `intern` calls have no id equivalent, see `add_core`'s doc comment).
//!
//! `Clone` is NOT implemented (module doc constraint): the Arc version's
//! `Clone` existed only for the nested-inductive admission path's scratch
//! env, which Task 5's `EnvView.extra` + `extend_view` replaced — nothing
//! else clones an `Environment` (`grep -rn "\.clone()"
//! crates/leanr_kernel/src/inductive.rs crates/leanr_kernel/src/env.rs |
//! grep -i env` finds no hits in the bank port's call sites either).

use std::collections::HashMap;
use std::sync::Arc;

use super::decl::{
    intern_constant_info, AxiomVal, ConstantInfo, ConstantVal, ConstructorVal, Declaration,
    DefinitionVal, InductiveVal, OpaqueVal, QuotVal, RecursorRule, RecursorVal, TheoremVal,
};
use super::scratch::{promote, promote_name};
use super::tc::{EnvView, TypeChecker};
use super::{ExprId, NameId, Store};
use crate::{DefinitionSafety, KernelError, Name, Nat};

/// oracle: `env.rs`'s own `EnvironmentError` (Arc env.rs:9-12). `Bank`
/// has no Arc counterpart: the id bank's finite (2^31-per-region) id
/// space can be exhausted while interning a module's constants, which
/// the Arc `Environment` (backed by unbounded `Arc` allocation) never
/// needs to report here — the global "no panics reachable from attacker
/// data" constraint means a bank-exhaustion hit during `from_modules`
/// must surface as an `Err`, not a panic, so this variant carries it
/// rather than silently dropping it.
#[derive(Debug, PartialEq, Eq)]
pub enum EnvironmentError {
    DuplicateName(Arc<Name>),
    Bank(KernelError),
}

impl From<KernelError> for EnvironmentError {
    fn from(e: KernelError) -> Self {
        EnvironmentError::Bank(e)
    }
}

// ---------------------------------------------------------------------
// `check_name`/`check_duplicated_univ_params`/`check_no_metavar_no_fvar`
// — hoisted here from `bank/inductive.rs` (that file's module doc point
// 7 flagged this as a Task 6 follow-up: "they belong to `bank/env.rs`
// conceptually — Arc's `env.rs:18-56` — but that module doesn't exist
// until Task 6"). Bodies are unchanged from the inductive.rs copies;
// `inductive.rs` now imports them from here instead of defining its own.
// `pub(crate)` so both this module's `add_decl` and `bank::inductive`
// can call them; region-correct (`n`/`p` may be a scratch-region id
// during admission, so error construction always routes through
// `scratch.to_name(Some(view.store), ...)`, never `EnvView::get_with`'s
// bare miss-path).
// ---------------------------------------------------------------------

/// oracle: environment.cpp:102-105 (`check_name`) — `AlreadyDeclared` if
/// `n` is already bound.
pub(crate) fn check_name(scratch: &Store, view: &EnvView, n: NameId) -> Result<(), KernelError> {
    if view.get(n).is_some() {
        return Err(KernelError::AlreadyDeclared(
            scratch.to_name(Some(view.store), Some(n)),
        ));
    }
    Ok(())
}

/// oracle: environment.cpp:111-121 (`check_duplicated_univ_params`).
pub(crate) fn check_duplicated_univ_params(
    scratch: &Store,
    view: &EnvView,
    ls: &[NameId],
) -> Result<(), KernelError> {
    for (i, &p) in ls.iter().enumerate() {
        if ls[i + 1..].contains(&p) {
            return Err(KernelError::DuplicateUnivParam(
                scratch.to_name(Some(view.store), Some(p)),
            ));
        }
    }
    Ok(())
}

/// oracle: environment.cpp:87-100 (`check_no_metavar_no_fvar`).
pub(crate) fn check_no_metavar_no_fvar(
    scratch: &Store,
    view: &EnvView,
    n: NameId,
    e: ExprId,
) -> Result<(), KernelError> {
    let d = scratch.expr_data(Some(view.store), e);
    if d.has_expr_mvar() || d.has_level_mvar() {
        return Err(KernelError::HasMetavars(
            scratch.to_name(Some(view.store), Some(n)),
        ));
    }
    if d.has_fvar() {
        return Err(KernelError::HasFVars(
            scratch.to_name(Some(view.store), Some(n)),
        ));
    }
    Ok(())
}

/// oracle: environment.cpp:127-133 (`check_constant_val`), split into
/// two halves at the point where a `TypeChecker` starts to exist:
///
/// - `check_constant_val_pre`: name + univ-param + mvar/fvar checks on
///   the declared type. Runs BEFORE any `TypeChecker` is constructed, so
///   it can take `scratch: &Store` directly (no `TypeChecker` yet holds
///   `scratch`'s mutable borrow).
/// - `check_constant_val_sort`: `checker` infers the type's own type and
///   `ensure_sort`s it. Runs immediately after, once `checker` exists.
///
/// Every `add_decl` arm calls both back-to-back, so the observable
/// sequence is byte-identical to Arc's single `check_constant_val` call
/// — the split is purely to satisfy Rust's aliasing rules (a
/// `TypeChecker<'e>` borrows `scratch` mutably for its whole lifetime,
/// so a free function taking `scratch: &Store` cannot run while a
/// `checker` value is alive; Arc has no such conflict since Arc's
/// `TypeChecker` only ever borrows `&Environment`, never anything
/// mutably). Declaration kinds needing a further mvar/fvar check on the
/// VALUE (`Defn`/`Thm`) use `TypeChecker::check_no_metavar_no_fvar`
/// instead of the free function, for the same reason.
fn check_constant_val_pre(
    scratch: &Store,
    view: &EnvView,
    v: &ConstantVal,
) -> Result<(), KernelError> {
    check_name(scratch, view, v.name)?;
    check_duplicated_univ_params(scratch, view, &v.level_params)?;
    check_no_metavar_no_fvar(scratch, view, v.name, v.ty)?;
    Ok(())
}

fn check_constant_val_sort(checker: &mut TypeChecker, v: &ConstantVal) -> Result<(), KernelError> {
    let sort = checker.check(v.ty, &v.level_params)?;
    checker.ensure_sort(sort)?;
    Ok(())
}

/// The id-native `Environment`: persistent bank + the constant map the
/// checker consults, plus the quotient-initialized flag. Every id
/// reachable from `constants` lives in `store` (region 0) — the
/// region-discipline invariant `add_core`/`promote_constant_info`
/// maintain.
pub struct Environment {
    store: Store,
    constants: HashMap<NameId, ConstantInfo>,
    /// oracle: `environment::m_quot_initialized`. Set exactly once, by
    /// `add_decl`'s `Declaration::Quot` arm after `quot::add_quot`
    /// succeeds.
    quot_initialized: bool,
}

impl Default for Environment {
    fn default() -> Self {
        Environment {
            store: Store::persistent(),
            constants: HashMap::new(),
            quot_initialized: false,
        }
    }
}

impl Environment {
    /// oracle: `Environment::from_modules` (Arc env.rs:125). Interns
    /// each module's constants directly into `self.store`
    /// (`intern_constant_info(&mut self.store, None, ..)`), dropping
    /// each module's Arc graph before pulling the next module from the
    /// iterator (already lazy — this loop never collects `modules`).
    pub fn from_modules<I>(modules: I) -> Result<Environment, EnvironmentError>
    where
        I: IntoIterator<Item = Vec<crate::ConstantInfo>>,
    {
        let mut env = Environment::default();
        for module in modules {
            for info in module {
                let id_ci = intern_constant_info(&mut env.store, None, &info)?;
                let name = id_ci.name();
                if env.constants.contains_key(&name) {
                    let dup = env.store.to_name(None, Some(name));
                    return Err(EnvironmentError::DuplicateName(dup));
                }
                env.constants.insert(name, id_ci);
            }
        }
        Ok(env)
    }

    /// The replay-input bridge: intern a decoded module's Arc
    /// `ConstantInfo`s directly into `self.store`, returning the id-form
    /// constants keyed by name. Consumes (drops) the Arc module as it
    /// goes — `module: Vec<..>` is owned, and each `ConstantInfo` is
    /// dropped at the end of its loop iteration once bridged. Callers
    /// (`bank::replay`'s test harness, or a real decoder driver) fold
    /// the returned maps from successive modules together before calling
    /// `bank::replay::replay`.
    pub fn intern_module(
        &mut self,
        module: Vec<crate::ConstantInfo>,
    ) -> Result<HashMap<NameId, ConstantInfo>, KernelError> {
        let mut out = HashMap::with_capacity(module.len());
        for info in module {
            let id_ci = intern_constant_info(&mut self.store, None, &info)?;
            out.insert(id_ci.name(), id_ci);
        }
        Ok(out)
    }

    pub fn get(&self, n: NameId) -> Option<&ConstantInfo> {
        self.constants.get(&n)
    }

    /// oracle: `environment::get` — like `get`, but a miss is
    /// `KernelError::UnknownConstant` rather than a silent `None`.
    /// **Callers must pass a PERSISTENT-region `NameId`** — same
    /// contract as `EnvView::get_with` (this environment's own `store`
    /// resolves the miss-path `to_name` with `base = None`).
    pub fn get_with(&self, n: NameId) -> Result<&ConstantInfo, KernelError> {
        self.get(n).ok_or_else(|| {
            debug_assert!(
                !n.is_scratch(),
                "Environment::get_with: passed scratch-region NameId"
            );
            KernelError::UnknownConstant(self.store.to_name(None, Some(n)))
        })
    }

    /// oracle: inductive.cpp:27 (`is_non_rec_structure`) — mirrors
    /// `EnvView::is_structure_like` (Task 4).
    pub fn is_structure_like(&self, name: NameId) -> bool {
        matches!(self.get(name), Some(ConstantInfo::Induct(v))
            if v.ctors.len() == 1 && v.num_indices == Nat::from(0u64) && !v.is_rec)
    }

    /// oracle: `environment::is_quot_initialized`.
    pub fn quot_initialized(&self) -> bool {
        self.quot_initialized
    }

    pub fn len(&self) -> usize {
        self.constants.len()
    }

    pub fn is_empty(&self) -> bool {
        self.constants.is_empty()
    }

    /// The `EnvView` this environment's own store/constants project —
    /// what every checker/admission-pipeline call in `add_decl` consults.
    /// `extra` is always `None` here: nested-inductive admission's own
    /// `extra` accumulator (Task 5's `extend_view`) is internal to
    /// `bank::inductive` and never surfaces at this boundary.
    pub fn view(&self) -> EnvView<'_> {
        EnvView {
            consts: &self.constants,
            extra: None,
            quot_initialized: self.quot_initialized,
            store: &self.store,
        }
    }

    /// Intern an `Arc<Name>` directly into this environment's persistent
    /// store, returning its `NameId` (idempotent: an already-interned
    /// name returns the existing id, never a duplicate row).
    /// `pub(crate)` for `bank::replay`, which needs `Eq`'s persistent
    /// `NameId` to probe its own working map before admitting the
    /// quotient — the id-native environment has no direct `Arc<Name>`
    /// keyed lookup the way Arc `Environment::get` does, so the name
    /// must be resolved to an id first.
    pub(crate) fn intern_name(&mut self, n: &Arc<Name>) -> Result<Option<NameId>, KernelError> {
        self.store.intern_name(None, n)
    }

    /// oracle: environment.cpp:261-273 (`environment::add`) plus the
    /// per-kind `add_axiom`/`add_definition`/`add_theorem`/`add_opaque`
    /// (environment.cpp:152-223). Creates a fresh per-declaration scratch
    /// `Store` (Global Constraints' region discipline), checks the
    /// declaration against the PRE-extension environment, then admits
    /// the survivor(s) via `add_core`. On any check failure the
    /// environment is left completely unchanged.
    ///
    /// **Region contract**: every `NameId`/`ExprId` embedded in `d` must
    /// already be persistent-region (i.e. interned into `self.store`,
    /// e.g. via `intern_module`/`from_modules`, or extracted from a
    /// `ConstantInfo` that was) — this method's freshly-created `scratch`
    /// cannot resolve a scratch id minted by some OTHER scratch store the
    /// caller may have used to build `d`.
    pub fn add_decl(&mut self, d: Declaration) -> Result<(), KernelError> {
        let mut scratch = Store::scratch();
        let info = {
            match d {
                Declaration::Axiom(v) => {
                    let view = self.view();
                    check_constant_val_pre(&scratch, &view, &v.val)?;
                    let mut checker = TypeChecker::new(self.view(), &mut scratch);
                    check_constant_val_sort(&mut checker, &v.val)?;
                    ConstantInfo::Axiom(v)
                }
                Declaration::Defn(v) => {
                    // oracle: environment.cpp:163 (`v.is_unsafe()`); the
                    // unsafe/partial branch is unreachable for us (see
                    // the brief's `Declaration` doc comment — replay
                    // never sends an unsafe/partial `Defn`). Total &
                    // documented: reject rather than silently mis-check.
                    if v.safety != DefinitionSafety::Safe {
                        let name = self.store.to_name(None, Some(v.val.name));
                        return Err(KernelError::UnsafeConstInSafeDecl(name));
                    }
                    let view = self.view();
                    check_constant_val_pre(&scratch, &view, &v.val)?;
                    let mut checker = TypeChecker::new(self.view(), &mut scratch);
                    check_constant_val_sort(&mut checker, &v.val)?;
                    checker.check_no_metavar_no_fvar(v.val.name, v.value)?;
                    let val_type = checker.check(v.value, &v.val.level_params)?;
                    if !checker.is_def_eq(val_type, v.val.ty)? {
                        let name = self.store.to_name(None, Some(v.val.name));
                        return Err(KernelError::DefTypeMismatch(name));
                    }
                    ConstantInfo::Defn(v)
                }
                Declaration::Thm(v) => {
                    let view = self.view();
                    check_constant_val_pre(&scratch, &view, &v.val)?;
                    let mut checker = TypeChecker::new(self.view(), &mut scratch);
                    check_constant_val_sort(&mut checker, &v.val)?;
                    if !checker.is_prop(v.val.ty)? {
                        let name = self.store.to_name(None, Some(v.val.name));
                        return Err(KernelError::TheoremTypeNotProp(name));
                    }
                    checker.check_no_metavar_no_fvar(v.val.name, v.value)?;
                    let val_type = checker.check(v.value, &v.val.level_params)?;
                    if !checker.is_def_eq(val_type, v.val.ty)? {
                        let name = self.store.to_name(None, Some(v.val.name));
                        return Err(KernelError::DefTypeMismatch(name));
                    }
                    ConstantInfo::Thm(v)
                }
                Declaration::Opaque(v) => {
                    // oracle (environment.cpp:211-222): no
                    // `check_no_metavar_no_fvar` on the value here —
                    // unlike Defn/Thm, `add_opaque` relies solely on the
                    // `checker.check` walk below. Ported as-is.
                    let view = self.view();
                    check_constant_val_pre(&scratch, &view, &v.val)?;
                    let mut checker = TypeChecker::new(self.view(), &mut scratch);
                    check_constant_val_sort(&mut checker, &v.val)?;
                    let val_type = checker.check(v.value, &v.val.level_params)?;
                    if !checker.is_def_eq(val_type, v.val.ty)? {
                        let name = self.store.to_name(None, Some(v.val.name));
                        return Err(KernelError::DefTypeMismatch(name));
                    }
                    ConstantInfo::Opaque(v)
                }
                // oracle: environment.cpp:266-267 -> `add_quot`
                // (quot.cpp:47-79). `quot::add_quot` does its own
                // checking and returns every survivor to admit rather
                // than mutating a shared environment (Task 5's
                // `scratch`/`view`-only signature) — this arm admits
                // them via `add_core` itself and sets the flag, then
                // returns directly rather than falling through to the
                // shared `self.add_core(info)` at the end.
                Declaration::Quot => {
                    let admitted = {
                        let view = self.view();
                        super::quot::add_quot(&mut scratch, &view)?
                    };
                    for ci in admitted {
                        self.add_core(&scratch, ci)?;
                    }
                    self.quot_initialized = true;
                    return Ok(());
                }
                // oracle: environment.cpp:266-267 -> `add_inductive`
                // (inductive.cpp:1116). `inductive::add_inductive`
                // eliminates nested occurrences, runs the ordinary
                // machinery, and (when nesting occurred) restores the
                // real nested inductives — returning every survivor to
                // admit. See this function's own doc comment for the
                // arrival-order analysis: `add_core`'s per-entry
                // promote-then-insert is independent of the `Vec`'s
                // order, so the nondeterministic `HashMap::into_values()`
                // order `add_inductive` returns is safe to consume as-is.
                Declaration::Inductive {
                    lparams,
                    nparams,
                    types,
                    is_unsafe,
                } => {
                    let admitted = {
                        let view = self.view();
                        super::inductive::add_inductive(
                            &mut scratch,
                            &view,
                            lparams,
                            nparams,
                            types,
                            is_unsafe,
                        )?
                    };
                    for ci in admitted {
                        self.add_core(&scratch, ci)?;
                    }
                    return Ok(());
                }
            }
        };
        self.add_core(&scratch, info)?;
        Ok(())
    }

    /// oracle: environment.cpp:144 (`environment::add`, the unchecked
    /// insert used AFTER a declaration has already been checked) — the
    /// single admission choke point every `ConstantInfo` (decoded or
    /// kernel-generated, e.g. recursor types/rules built fresh during
    /// inductive admission) passes through. Translates `info`'s
    /// scratch-region ids into `self.store`-persistent ones via
    /// `promote_constant_info`, then inserts. The Arc kernel's
    /// `interner.intern_input`/`intern` calls in `add_core` have no id
    /// equivalent — deduplication already happened at interning time
    /// (`Store::intern_expr`/`intern_name`/etc. are hash-consing), so
    /// there is nothing left to intern here, only to promote.
    ///
    /// **Ordering**: called once per `ConstantInfo` to admit, in
    /// whatever order the caller's `Vec` (or the single-`info` case)
    /// presents them. Safe regardless of order: `promote_constant_info`
    /// only ever reads `scratch`/writes fresh rows into `self.store`
    /// (never touches `self.constants`), and every name distinctness
    /// check (`check_name`, run inside `add_quot`/`add_inductive`
    /// against their OWN growing view before a `Vec` is ever returned)
    /// has already happened by the time `add_core` sees an entry — see
    /// this method's caller (`add_decl`)'s doc comment.
    fn add_core(&mut self, scratch: &Store, info: ConstantInfo) -> Result<(), KernelError> {
        let promoted = promote_constant_info(&mut self.store, scratch, &info)?;
        self.constants.insert(promoted.name(), promoted);
        Ok(())
    }
}

// ---------------------------------------------------------------------
// `promote_constant_info` — field-by-field scratch -> persistent
// translation, one function per `ConstantInfo`/payload-struct pair,
// mirroring `bank/decl.rs`'s `intern_*`/`constant_info_eq` field
// enumeration (every field of every variant accounted for).
// ---------------------------------------------------------------------

fn promote_name_vec(
    base: &mut Store,
    scratch: &Store,
    ns: &[NameId],
) -> Result<Vec<NameId>, KernelError> {
    ns.iter().map(|&n| promote_name(base, scratch, n)).collect()
}

fn promote_constant_val(
    base: &mut Store,
    scratch: &Store,
    v: &ConstantVal,
) -> Result<ConstantVal, KernelError> {
    Ok(ConstantVal {
        name: promote_name(base, scratch, v.name)?,
        level_params: promote_name_vec(base, scratch, &v.level_params)?,
        ty: promote(base, scratch, v.ty)?,
    })
}

/// Translate a scratch-region `ConstantInfo` into an equivalent one
/// whose every id is persistent (`base`-region), per `add_core`'s
/// choke-point contract. Every field of every variant is enumerated
/// below (same coverage discipline as `decl.rs`'s `constant_info_eq`
/// doc comment); a skipped field would leak a scratch id into the
/// persistent environment.
///
/// Field coverage (every variant, every field of its payload struct):
/// - `ConstantVal` (`.val` on every kind): `name`, `level_params`, `ty`.
/// - `AxiomVal`: `val` (+ `is_unsafe` copied, no ids).
/// - `DefinitionVal`: `val`, `value`, `all` (+ `hints`/`safety` copied).
/// - `TheoremVal`: `val`, `value`, `all`.
/// - `OpaqueVal`: `val`, `value`, `all` (+ `is_unsafe` copied).
/// - `QuotVal`: `val` (+ `kind` copied).
/// - `InductiveVal`: `val`, `all`, `ctors` (+ `num_params`/`num_indices`/
///   `num_nested`/`is_rec`/`is_unsafe`/`is_reflexive` copied, no ids).
/// - `ConstructorVal`: `val`, `induct` (+ `cidx`/`num_params`/
///   `num_fields`/`is_unsafe` copied, no ids).
/// - `RecursorVal`: `val`, `all`, `rules` (per `RecursorRule`: `ctor`,
///   `rhs`, + `nfields` copied) (+ `num_params`/`num_indices`/
///   `num_motives`/`num_minors`/`k`/`is_unsafe` copied, no ids).
pub(crate) fn promote_constant_info(
    base: &mut Store,
    scratch: &Store,
    ci: &ConstantInfo,
) -> Result<ConstantInfo, KernelError> {
    Ok(match ci {
        ConstantInfo::Axiom(v) => ConstantInfo::Axiom(AxiomVal {
            val: promote_constant_val(base, scratch, &v.val)?,
            is_unsafe: v.is_unsafe,
        }),
        ConstantInfo::Defn(v) => ConstantInfo::Defn(DefinitionVal {
            val: promote_constant_val(base, scratch, &v.val)?,
            value: promote(base, scratch, v.value)?,
            hints: v.hints,
            safety: v.safety,
            all: promote_name_vec(base, scratch, &v.all)?,
        }),
        ConstantInfo::Thm(v) => ConstantInfo::Thm(TheoremVal {
            val: promote_constant_val(base, scratch, &v.val)?,
            value: promote(base, scratch, v.value)?,
            all: promote_name_vec(base, scratch, &v.all)?,
        }),
        ConstantInfo::Opaque(v) => ConstantInfo::Opaque(OpaqueVal {
            val: promote_constant_val(base, scratch, &v.val)?,
            value: promote(base, scratch, v.value)?,
            is_unsafe: v.is_unsafe,
            all: promote_name_vec(base, scratch, &v.all)?,
        }),
        ConstantInfo::Quot(v) => ConstantInfo::Quot(QuotVal {
            val: promote_constant_val(base, scratch, &v.val)?,
            kind: v.kind,
        }),
        ConstantInfo::Induct(v) => ConstantInfo::Induct(InductiveVal {
            val: promote_constant_val(base, scratch, &v.val)?,
            num_params: v.num_params.clone(),
            num_indices: v.num_indices.clone(),
            all: promote_name_vec(base, scratch, &v.all)?,
            ctors: promote_name_vec(base, scratch, &v.ctors)?,
            num_nested: v.num_nested.clone(),
            is_rec: v.is_rec,
            is_unsafe: v.is_unsafe,
            is_reflexive: v.is_reflexive,
        }),
        ConstantInfo::Ctor(v) => ConstantInfo::Ctor(ConstructorVal {
            val: promote_constant_val(base, scratch, &v.val)?,
            induct: promote_name(base, scratch, v.induct)?,
            cidx: v.cidx.clone(),
            num_params: v.num_params.clone(),
            num_fields: v.num_fields.clone(),
            is_unsafe: v.is_unsafe,
        }),
        ConstantInfo::Rec(v) => ConstantInfo::Rec(RecursorVal {
            val: promote_constant_val(base, scratch, &v.val)?,
            all: promote_name_vec(base, scratch, &v.all)?,
            num_params: v.num_params.clone(),
            num_indices: v.num_indices.clone(),
            num_motives: v.num_motives.clone(),
            num_minors: v.num_minors.clone(),
            rules: v
                .rules
                .iter()
                .map(|r| {
                    Ok(RecursorRule {
                        ctor: promote_name(base, scratch, r.ctor)?,
                        nfields: r.nfields.clone(),
                        rhs: promote(base, scratch, r.rhs)?,
                    })
                })
                .collect::<Result<Vec<_>, KernelError>>()?,
            k: v.k,
            is_unsafe: v.is_unsafe,
        }),
    })
}

#[cfg(test)]
mod tests;
