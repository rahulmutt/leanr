use std::collections::HashMap;
use std::sync::Arc;

use crate::{ConstantInfo, Name};

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

    pub fn len(&self) -> usize {
        self.constants.len()
    }

    pub fn is_empty(&self) -> bool {
        self.constants.is_empty()
    }
}
