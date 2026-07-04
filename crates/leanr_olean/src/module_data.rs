//! The decoded contents of one `.olean` module (oracle:
//! src/Lean/Environment.lean:109-129).

use std::sync::Arc;

use leanr_kernel::{ConstantInfo, Name};

use crate::{interp::Interp, raw, OleanError};

/// oracle: src/Lean/Setup.lean:25-32
#[derive(Debug, Clone)]
pub struct Import {
    pub module: Arc<Name>,
    pub import_all: bool,
    pub is_exported: bool,
    pub is_meta: bool,
}

#[derive(Debug)]
pub struct ModuleData {
    pub is_module: bool,
    pub imports: Vec<Import>,
    pub const_names: Vec<Arc<Name>>,
    pub constants: Vec<ConstantInfo>,
    pub extra_const_names: Vec<Arc<Name>>,
    /// Environment-extension entries are validated by phase A but kept
    /// opaque (spec: interpreted by the elaborator in M4).
    pub num_entries: usize,
}

impl ModuleData {
    /// Decode a whole `.olean` file. `bytes` is untrusted input; every
    /// failure mode is an `OleanError`, never a panic (see
    /// docs/THREAT_MODEL.md and the raw-module docs).
    pub fn parse(bytes: &[u8]) -> Result<ModuleData, OleanError> {
        let root = raw::parse_bytes(bytes)?;
        Interp::new().module_data(&root)
    }
}
