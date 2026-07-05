use std::collections::HashMap;
use std::sync::Arc;

use crate::{ConstantInfo, KernelError, Name};

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

    pub fn len(&self) -> usize {
        self.constants.len()
    }

    pub fn is_empty(&self) -> bool {
        self.constants.is_empty()
    }
}
