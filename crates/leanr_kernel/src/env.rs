use std::collections::HashMap;
use std::sync::Arc;

use crate::{
    ConstantInfo, ConstantVal, Declaration, DefinitionSafety, Expr, KernelError, Name, TypeChecker,
};

fn mk_name2(a: &str, b: &str) -> Arc<Name> {
    Arc::new(Name::Str {
        parent: Arc::new(Name::Str {
            parent: Arc::new(Name::Anonymous),
            part: a.to_string(),
        }),
        part: b.to_string(),
    })
}

#[derive(Debug, PartialEq, Eq)]
pub enum EnvironmentError {
    DuplicateName(Arc<Name>),
}

/// oracle: environment.cpp:102-105 (`check_name`) — `AlreadyDeclared` if
/// `n` is already bound. `pub(crate)` so the inductive-admission
/// pipeline (inductive.rs, Task 9) can reuse the exact same check the
/// oracle's `m_env.check_name` performs at every `add_core` site.
pub(crate) fn check_name(env: &Environment, n: &Arc<Name>) -> Result<(), KernelError> {
    if env.get(n).is_some() {
        return Err(KernelError::AlreadyDeclared(Arc::clone(n)));
    }
    Ok(())
}

/// oracle: environment.cpp:111-121 (`check_duplicated_univ_params`) — the
/// first level param that recurs later in the list, else `Ok`. `Name`
/// lists here are the declaration's own `level_params` (small, no
/// attacker-controlled blowup), so the O(n^2) scan is fine. `pub(crate)`
/// for the inductive pipeline (Task 9), which runs it at the head of
/// `operator()` (inductive.cpp:779).
pub(crate) fn check_duplicated_univ_params(ls: &[Arc<Name>]) -> Result<(), KernelError> {
    for (i, p) in ls.iter().enumerate() {
        if ls[i + 1..].iter().any(|q| q == p) {
            return Err(KernelError::DuplicateUnivParam(Arc::clone(p)));
        }
    }
    Ok(())
}

/// oracle: environment.cpp:87-100 (`check_no_metavar_no_fvar`). O(1) via
/// the cached `ExprData` flags (`has_expr_mvar`/`has_level_mvar` →
/// `HasMetavars`, `has_fvar` → `HasFVars`) rather than a tree walk —
/// metavar check first, matching the oracle's order. `pub(crate)` so the
/// inductive pipeline (Task 9) can reuse it on the per-type/per-ctor
/// declared types exactly where the oracle calls it (inductive.cpp:218,
/// 425).
pub(crate) fn check_no_metavar_no_fvar(n: &Arc<Name>, e: &Arc<Expr>) -> Result<(), KernelError> {
    let d = e.data();
    if d.has_expr_mvar() || d.has_level_mvar() {
        return Err(KernelError::HasMetavars(Arc::clone(n)));
    }
    if d.has_fvar() {
        return Err(KernelError::HasFVars(Arc::clone(n)));
    }
    Ok(())
}

/// oracle: environment.cpp:127-133 (`check_constant_val`): name +
/// univ-param + mvar/fvar checks on the declared type, then `checker`
/// infers the type's own type and `ensure_sort`s it (`TypeExpected` on
/// failure).
fn check_constant_val(
    env: &Environment,
    v: &ConstantVal,
    checker: &mut TypeChecker,
) -> Result<(), KernelError> {
    check_name(env, &v.name)?;
    check_duplicated_univ_params(&v.level_params)?;
    check_no_metavar_no_fvar(&v.name, &v.ty)?;
    let sort = checker.check(&v.ty, &v.level_params)?;
    checker.ensure_sort(&sort)?;
    Ok(())
}

/// The constant map the checker (M1b) will consult. M1a ships only
/// construction and lookup.
#[derive(Debug, Default)]
pub struct Environment {
    constants: HashMap<Arc<Name>, ConstantInfo>,
}

impl Environment {
    /// Merge decoded modules' constants; duplicate names are an error
    /// (spec: "errors on duplicates").
    pub fn from_modules<I>(modules: I) -> Result<Environment, EnvironmentError>
    where
        I: IntoIterator<Item = Vec<ConstantInfo>>,
    {
        let mut constants: HashMap<Arc<Name>, ConstantInfo> = HashMap::new();
        for module in modules {
            for info in module {
                let name = Arc::clone(info.name());
                if constants.contains_key(&name) {
                    return Err(EnvironmentError::DuplicateName(name));
                }
                constants.insert(name, info);
            }
        }
        Ok(Environment { constants })
    }

    pub fn get(&self, name: &Arc<Name>) -> Option<&ConstantInfo> {
        self.constants.get(name)
    }

    /// oracle: environment.cpp `environment::get` — like `get`, but a
    /// miss is the kernel's `unknown_constant_exception`
    /// (`KernelError::UnknownConstant`) rather than a silent `None`. This
    /// is the form the M1b type checker consults (type_checker.cpp:93
    /// `env().get(const_name(e))`).
    pub fn get_with(&self, name: &Arc<Name>) -> Result<&ConstantInfo, KernelError> {
        self.constants
            .get(name)
            .ok_or_else(|| KernelError::UnknownConstant(Arc::clone(name)))
    }

    /// oracle: environment.cpp:144 (`environment::add`, the unchecked
    /// insert used AFTER a declaration has already been checked). Used by
    /// the admission pipeline (`add_decl`, Tasks 8-11); `pub(crate)`
    /// because callers outside the kernel must go through the checking
    /// `add_decl`, never this raw insert.
    pub(crate) fn add_core(&mut self, info: ConstantInfo) {
        let name = Arc::clone(info.name());
        self.constants.insert(name, info);
    }

    /// Remove a previously `add_core`d constant. Used only by the
    /// inductive-admission pipeline's failure rollback (inductive.rs):
    /// the oracle mutates a *copy* of the environment (`m_env`) and
    /// discards it on any error, leaving the caller's environment
    /// untouched (inductive.cpp:1120-1123). We instead mutate the real
    /// environment in place for performance (no full-map clone per
    /// inductive during whole-stdlib replay) and undo every `add_core`
    /// we performed if a later phase fails — restoring the exact
    /// pre-admission state, since every added name was fresh (guaranteed
    /// by the `check_name` that precedes each `add_core`).
    pub(crate) fn remove_core(&mut self, name: &Arc<Name>) {
        self.constants.remove(name);
    }

    /// oracle: environment.cpp:261-273 (`environment::add`, the
    /// dispatch-then-check-then-extend entry) plus the per-kind
    /// `add_axiom`/`add_definition`/`add_theorem`/`add_opaque`
    /// (environment.cpp:152-223). Checks the declaration against the
    /// PRE-extension environment (this method's `&self` borrow, taken
    /// only for the checking phase and dropped before `add_core`
    /// extends), then admits it. On any check failure the environment is
    /// left completely unchanged (`get`/`len` identical to before the
    /// call).
    pub fn add_decl(&mut self, d: Declaration) -> Result<(), KernelError> {
        let info = {
            let env: &Environment = &*self;
            match d {
                Declaration::Axiom(v) => {
                    let mut checker = TypeChecker::new(env);
                    check_constant_val(env, &v.val, &mut checker)?;
                    ConstantInfo::Axiom(v)
                }
                Declaration::Defn(v) => {
                    // oracle: environment.cpp:163 (`v.is_unsafe()`) picks the
                    // unsafe/recursive-checking branch (179-189 is the safe
                    // branch we port; 163-178 is unreachable for us — see
                    // the brief's `Declaration` doc comment: replay never
                    // sends an unsafe/partial `Defn`). Total & documented:
                    // reject rather than silently mis-check.
                    if v.safety != DefinitionSafety::Safe {
                        return Err(KernelError::UnsafeConstInSafeDecl(Arc::clone(&v.val.name)));
                    }
                    let mut checker = TypeChecker::new(env);
                    check_constant_val(env, &v.val, &mut checker)?;
                    check_no_metavar_no_fvar(&v.val.name, &v.value)?;
                    let val_type = checker.check(&v.value, &v.val.level_params)?;
                    if !checker.is_def_eq(&val_type, &v.val.ty)? {
                        return Err(KernelError::DefTypeMismatch(Arc::clone(&v.val.name)));
                    }
                    ConstantInfo::Defn(v)
                }
                Declaration::Thm(v) => {
                    let mut checker = TypeChecker::new(env);
                    check_constant_val(env, &v.val, &mut checker)?;
                    if !checker.is_prop(&v.val.ty)? {
                        return Err(KernelError::TheoremTypeNotProp(Arc::clone(&v.val.name)));
                    }
                    check_no_metavar_no_fvar(&v.val.name, &v.value)?;
                    let val_type = checker.check(&v.value, &v.val.level_params)?;
                    if !checker.is_def_eq(&val_type, &v.val.ty)? {
                        return Err(KernelError::DefTypeMismatch(Arc::clone(&v.val.name)));
                    }
                    ConstantInfo::Thm(v)
                }
                Declaration::Opaque(v) => {
                    // oracle (environment.cpp:211-222): no
                    // `check_no_metavar_no_fvar` on the value here — unlike
                    // Defn/Thm, add_opaque relies solely on the `checker.check`
                    // walk below to reject a malformed value. Ported as-is.
                    let mut checker = TypeChecker::new(env);
                    check_constant_val(env, &v.val, &mut checker)?;
                    let val_type = checker.check(&v.value, &v.val.level_params)?;
                    if !checker.is_def_eq(&val_type, &v.val.ty)? {
                        return Err(KernelError::DefTypeMismatch(Arc::clone(&v.val.name)));
                    }
                    ConstantInfo::Opaque(v)
                }
                // oracle: environment.cpp:266-267 dispatches Quot/Inductive
                // to `add_quot`/`add_inductive`, ported in Tasks 11/9
                // respectively. Placeholder rejections until then (never
                // reached by anything that constructs a `Declaration`
                // today). The brief's sketch cites `InvalidInductive` for
                // both stubs but that variant requires a `name`, which a
                // bare `Quot` declaration has none of; `InvalidQuot` (the
                // oracle's own quot-admission error, quot.cpp:19-45) fits
                // without inventing a placeholder name, so it is used here
                // instead — documented deviation from the brief's literal
                // syntax, not from any tested behavior (no corpus test
                // exercises either stub).
                Declaration::Quot => {
                    return Err(KernelError::InvalidQuot {
                        what: "not implemented",
                    });
                }
                // oracle: environment.cpp:266-267 → `add_inductive`
                // (inductive.cpp:1116). Task 9 ports the non-nested
                // machinery; `nnested` is 0 here (Task 10 threads a
                // nonzero value once nested-inductive elimination lands).
                // `add_inductive` does its own checking and env mutation
                // (with failure rollback), so this arm returns directly.
                Declaration::Inductive {
                    lparams,
                    nparams,
                    types,
                    is_unsafe,
                } => {
                    return crate::inductive::add_inductive(
                        self,
                        lparams,
                        nparams,
                        types,
                        is_unsafe,
                        crate::Nat::from(0),
                    );
                }
            }
        };
        self.add_core(info);
        Ok(())
    }

    /// oracle: inductive.cpp:27 (`is_non_rec_structure`) — the query the
    /// checker uses for structure-eta / unit-like / eta-when-structure.
    /// True iff `name` is an inductive with exactly one constructor, no
    /// indices, and is not recursive. (The Task-7 brief paraphrases this
    /// as "inductive, one ctor, no indices"; the oracle additionally
    /// excludes recursive inductives, and the oracle is normative.)
    pub fn is_structure_like(&self, name: &Arc<Name>) -> bool {
        match self.constants.get(name) {
            Some(ConstantInfo::Induct(v)) => {
                v.ctors.len() == 1 && v.num_indices == crate::Nat::from(0) && !v.is_rec
            }
            _ => false,
        }
    }

    /// oracle: `environment::is_quot_initialized` — whether the built-in
    /// quotient constants have been admitted, which gates
    /// `quot_reduce_rec` in `reduce_recursor` (type_checker.cpp:334).
    ///
    /// M1a stored no such flag; as a temporary gate we treat the quotient
    /// as initialized once its four constants are present. Task 11
    /// (quotient admission) replaces this with an explicit flag set when
    /// `Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind` are added, matching the
    /// oracle exactly. The proxy is sound in the interim: `quot_reduce_rec`
    /// itself only fires on genuine `Quot.lift`/`Quot.ind` heads reducing
    /// a fully-applied `Quot.mk`.
    pub fn quot_initialized(&self) -> bool {
        self.constants.contains_key(&mk_name2("Quot", "mk"))
            && self.constants.contains_key(&mk_name2("Quot", "lift"))
            && self.constants.contains_key(&mk_name2("Quot", "ind"))
    }

    pub fn len(&self) -> usize {
        self.constants.len()
    }

    pub fn is_empty(&self) -> bool {
        self.constants.is_empty()
    }
}

#[cfg(test)]
mod tests;
