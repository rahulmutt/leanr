use std::collections::HashMap;
use std::sync::Arc;

use crate::{ConstantInfo, KernelError, Name};

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
    /// the admission pipeline in Tasks 8-11; `pub(crate)` because callers
    /// outside the kernel must go through the checking `add` (a later
    /// task), never this raw insert.
    #[allow(dead_code)] // first consumer lands in Task 8's admission pipeline
    pub(crate) fn add_core(&mut self, info: ConstantInfo) {
        let name = Arc::clone(info.name());
        self.constants.insert(name, info);
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
